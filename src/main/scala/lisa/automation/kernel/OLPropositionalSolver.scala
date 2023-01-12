package lisa.automation.kernel

import lisa.kernel.proof.SequentCalculus as LK
import lisa.kernel.proof.SequentCalculus.*
import lisa.kernel.proof.SCProof
import lisa.kernel.fol.FOL.*
import lisa.utils.Helpers.{*, given}
import lisa.utils.Helpers.{_, given}
import lisa.utils.Library
import lisa.utils.tactics.ProofTacticLib.ParameterlessAndThen
import lisa.utils.tactics.ProofTacticLib.ParameterlessHave
import lisa.utils.tactics.ProofTacticLib.ProofTactic

object OLPropositionalSolver {


  /**
   * A tactic object dedicated to solve any propositionaly provable sequent (possibly in exponential time). Can be used with arbitrary many premises.
   * Leverages the OL algorithm for propositional logic.
   */
  object Tautology extends ProofTactic with ParameterlessHave with ParameterlessAndThen {

    /**
     * Given a targeted conclusion sequent, try to prove it using laws of propositional logic and reflexivity and symmetry of equality.
     *
     * @param proof The ongoing proof object in which the step happens.
     * @param bot The desired conclusion.
     */
    def apply(using proof: Library#Proof)(bot: Sequent): proof.ProofTacticJudgement = {
      solveSequent(bot) match {
        case Some(value) => proof.ValidProofTactic(value.steps, Seq())
        case None => proof.InvalidProofTactic("Impossible to prove desired conclusion with only propositional logic.")
      }
    }

    /**
     * Given a targeted conclusion sequent, try to prove it using laws of propositional logic and reflexivity and symmetry of equality.
     * Uses the given already proven facts as assumptions to reach the desired goal.
     *
     * @param proof The ongoing proof object in which the step happens.
     * @param premise A previously proven step necessary to reach the conclusion.
     * @param bot   The desired conclusion.
     */
    def apply(using proof: Library#Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      apply2(using proof)(Seq(premise) *)(bot)

    def apply2(using proof: Library#Proof)(premises: proof.Fact*)(bot: Sequent): proof.ProofTacticJudgement = {
      val premsFormulas = premises.map(p => (p, sequentToFormula(proof.getSequent(p)))).zipWithIndex
      val initProof = premsFormulas.map(s => Rewrite(() |- s._1._2, -(1 + s._2))).toList
      val sqToProve = bot ++< (premsFormulas.map(s => s._1._2).toSet |- ())
      solveSequent(sqToProve) match {
        case Some(value) =>
          val subpr = SCSubproof(value)
          val stepsList = premsFormulas.foldLeft[List[SCProofStep]](List(subpr))((prev: List[SCProofStep], cur) => {
            val ((prem, form), position) = cur
            Cut(prev.head.bot -< form, position, initProof.length + prev.length - 1, form) :: prev
          })
          val steps = (initProof ++ stepsList.reverse).toIndexedSeq
          proof.ValidProofTactic(steps, premises)
        case None =>
          proof.InvalidProofTactic("Impossible to prove desired conclusion with only propositional logic.")
      }
    }
  } //End of tactic object Tautology

  /**
   * This function returns a proof of the given sequent if such a proof exists using only the rules of propositional logic and reflexivity and symmetry of equality.
   * Be aware that the runtime and size of the proof may be exponential in the number of atoms (i.e. number of non-propositional subformulas of the input).
   * The strategy consists in leveraging OL formula reduction by alternating between branching on an atom and reducing the formula.
   * @param s A sequent that should be a propositional logic tautology. It can contain binders and schematic connector symbols, but they will be treated as atoms.
   * @return A proof of the given sequent, if it exists
   */
  def solveSequent(s: Sequent): Option[SCProof] = {
    val augSeq = augmentSequent(s)
    val MaRvIn = VariableFormulaLabel(freshId(augSeq.formula.schematicFormulaLabels.map(_.id), "MaRvIn")) //arbitrary name that is unlikely to already exist in the formula

    try {
      val steps = solveAugSequent(augSeq, 0)(using MaRvIn)
      Some(SCProof((Rewrite(s, steps.length-1)::steps).reverse.toIndexedSeq))
    }
    catch case e: NoProofFoundException => None

  }

  //From there, private code.


  //Augmented Sequent
  private case class AugSequent(decisions: (List[Formula], List[Formula]), formula:Formula)

  //Transform a sequent into a format more adequate for solving
  private def augmentSequent(s:Sequent): AugSequent = {
    val f = reducedForm(sequentToFormula(s))
    val atoms: scala.collection.mutable.Map[Formula, Int] = scala.collection.mutable.Map.empty
    AugSequent((Nil, Nil), f)
  }

  //Find all "atoms" of the formula.
  //We mean atom in the propositional logic sense, so any formula starting with a predicate symbol, a binder or a schematic connector is an atom here.
  private def findBestAtom(f: Formula): Option[Formula] = {
    val atoms: scala.collection.mutable.Map[Formula, Int] = scala.collection.mutable.Map.empty
    def findAtoms2(f: Formula, add: Formula => Unit): Unit = f match {
      case f: PredicateFormula => add (f)
      case ConnectorFormula (label, args) => label match {
        case label: ConstantConnectorLabel => args.foreach (c => findAtoms2 (c, add) )
        case SchematicConnectorLabel (id, arity) => add (f)
      }
      case BinderFormula (label, bound, inner) => add (f)
    }
    findAtoms2(f, a => atoms.update(a, {val g = atoms.get(a); if (g.isEmpty) 1 else g.get+1}))
    if (atoms.isEmpty) None else Some(atoms.toList.maxBy(_._2)._1)
  }

  private class NoProofFoundException extends Exception

  //Given a sequent, return a proof of that sequent if on exists that only uses propositional logic rules and reflexivity of equality.
  //Alternates between reducing the formulas using the OL algorithm for propositional logic and branching on an atom using excluded middle.
  //An atom is a subformula of the input that is either a predicate, a binder or a schematic connector, i.e. a subformula that has not meaning in propositional logic.
  private def solveAugSequent(s:AugSequent, offset:Int)(using MaRvIn : VariableFormulaLabel): List[SCProofStep] = {
    val bestAtom = findBestAtom(s.formula)
    if (isSame(s.formula, top())) {
      List(RewriteTrue(s.decisions._1++s.decisions._2.map((f:Formula) => Neg(f)) |- s.formula))
    }
    else if (bestAtom.isEmpty) {
      throw new NoProofFoundException
    }
    else {
      val atom = bestAtom.get
      val redF = reducedForm(s.formula)
      val optLambda = SimpleSimplifier.findSubformula(redF, Seq((MaRvIn, atom)))
      if (optLambda.isEmpty) return solveAugSequent(AugSequent(s.decisions, redF), offset)
      val lambdaF = optLambda.get

      val seq1 = AugSequent((atom::s.decisions._1, s.decisions._2), lambdaF(Seq(top())))
      val proof1 = solveAugSequent(seq1, offset)
      val subst1 = RightSubstIff(atom::s.decisions._1++s.decisions._2.map((f:Formula) => Neg(f)) |- redF, offset+proof1.length-1, List((atom, top())), lambdaF)
      val seq2 = AugSequent((s.decisions._1, atom::s.decisions._2), lambdaF(Seq(bot())))
      val proof2 = solveAugSequent(seq2, offset+proof1.length+1)
      val subst2 = RightSubstIff(Neg(atom)::s.decisions._1++s.decisions._2.map((f:Formula) => Neg(f)) |- redF, offset+proof1.length+proof2.length-1+1, List((atom, bot())), lambdaF)
      val red2 = Rewrite(s.decisions._1++s.decisions._2.map((f:Formula) => Neg(f)) |- (redF, atom), offset+proof1.length+proof2.length+2-1)
      val cutStep = Cut(s.decisions._1 |- redF::s.decisions._2, offset+proof1.length+proof2.length+3-1, offset+proof1.length+1-1, atom)
      val redStep = Rewrite(s.decisions._1 |- s.formula::s.decisions._2, offset+proof1.length+proof2.length+4-1)
      redStep::cutStep::red2::subst2::proof2++(subst1::proof1)

      }
    }

}
