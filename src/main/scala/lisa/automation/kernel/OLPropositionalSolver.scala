package lisa.automation.kernel

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.*
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib.*
import lisa.prooflib.Substitution
import lisa.utils.KernelHelpers.{_, given}

object OLPropositionalSolver {

  /**
   * A tactic object dedicated to solve any propositionaly provable sequent (possibly in exponential time). Can be used with arbitrary many premises.
   * Leverages the OL algorithm for scalafmpropositional logic.
   */
  object Tautology extends ProofTactic with ProofSequentTactic with ProofFactSequentTactic {

    /**
     * Given a targeted conclusion sequent, try to prove it using laws of propositional logic and reflexivity and symmetry of equality.
     *
     * @param proof The ongoing proof object in which the step happens.
     * @param bot The desired conclusion.
     */
    def apply(using lib: Library, proof: lib.Proof)(bot: Sequent): proof.ProofTacticJudgement = {
      solveSequent(bot) match {
        case Left(value) => proof.ValidProofTactic(value.steps, Seq())
        case Right((msg, seq)) => proof.InvalidProofTactic(msg)
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
    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      from(using lib, proof)(Seq(premise)*)(bot)

    def from(using lib: Library, proof: lib.Proof)(premises: proof.Fact*)(bot: Sequent): proof.ProofTacticJudgement = {
      val premsFormulas = premises.map(p => (p, sequentToFormula(proof.getSequent(p)))).zipWithIndex
      val initProof = premsFormulas.map(s => Restate(() |- s._1._2, -(1 + s._2))).toList
      val sqToProve = bot ++<< (premsFormulas.map(s => s._1._2).toSet |- ())
      solveSequent(sqToProve) match {
        case Left(value) =>
          val subpr = SCSubproof(value)
          val stepsList = premsFormulas.foldLeft[List[SCProofStep]](List(subpr))((prev: List[SCProofStep], cur) => {
            val ((prem, form), position) = cur
            Cut(prev.head.bot -<< form, position, initProof.length + prev.length - 1, form) :: prev
          })
          val steps = (initProof ++ stepsList.reverse).toIndexedSeq
          proof.ValidProofTactic(steps, premises)
        case Right((msg, seq)) =>
          proof.InvalidProofTactic(msg)
      }
    }
  } // End of tactic object Tautology

  /**
   * This function returns a proof of the given sequent if such a proof exists using only the rules of propositional logic and reflexivity and symmetry of equality.
   * Be aware that the runtime and size of the proof may be exponential in the number of atoms (i.e. number of non-propositional subformulas of the input).
   * The strategy consists in leveraging OL formula reduction by alternating between branching on an atom and reducing the formula.
   * @param s A sequent that should be a propositional logic tautology. It can contain binders and schematic connector symbols, but they will be treated as atoms.
   * @return A proof of the given sequent, if it exists
   */
  def solveSequent(s: Sequent): Either[SCProof, (String, Sequent)] = {
    val augSeq = augmentSequent(s)
    val MaRvIn = VariableFormulaLabel(freshId(augSeq.formula.schematicFormulaLabels.map(_.id), "MaRvIn")) // arbitrary name that is unlikely to already exist in the formula

    try {
      val steps = solveAugSequent(augSeq, 0)(using MaRvIn)
      Left(SCProof((Restate(s, steps.length - 1) :: steps).reverse.toIndexedSeq))
    } catch
      case e: NoProofFoundException =>
        Right(
          (
            "The statement may be incorrect or not provable within propositional logic.\n" +
              "The proof search failed because it needed the truth of the following sequent:\n" +
              s"${lisa.utils.FOLPrinter.prettySequent(e.unsolvable)}",
            e.unsolvable
          )
        )

  }

  // From there, private code.

  // Augmented Sequent
  private case class AugSequent(decisions: (List[Formula], List[Formula]), formula: Formula)

  // Transform a sequent into a format more adequate for solving
  private def augmentSequent(s: Sequent): AugSequent = {
    val f = reducedForm(sequentToFormula(s))
    val atoms: scala.collection.mutable.Map[Formula, Int] = scala.collection.mutable.Map.empty
    AugSequent((Nil, Nil), f)
  }

  def reduceSequent(s: Sequent): Formula = {
    val p = simplify(sequentToFormula(s))
    val nf = computeNormalForm(p)
    val fln = fromLocallyNameless(nf, Map.empty, 0)
    val res = toFormulaAIG(fln)
    res
  }

  // Find all "atoms" of the formula.
  // We mean atom in the propositional logic sense, so any formula starting with a predicate symbol, a binder or a schematic connector is an atom here.
  def findBestAtom(f: Formula): Option[Formula] = {
    val atoms: scala.collection.mutable.Map[Formula, Int] = scala.collection.mutable.Map.empty
    def findAtoms2(f: Formula, add: Formula => Unit): Unit = f match {
      case PredicateFormula(label, _) if label != top && label != bot => add(f)
      case PredicateFormula(_, _) => ()
      case ConnectorFormula(label, args) =>
        label match {
          case label: ConstantConnectorLabel => args.foreach(c => findAtoms2(c, add))
          case SchematicConnectorLabel(id, arity) => add(f)
        }
      case BinderFormula(label, bound, inner) => add(f)
    }
    findAtoms2(f, a => atoms.update(a, { val g = atoms.get(a); if (g.isEmpty) 1 else g.get + 1 }))
    if (atoms.isEmpty) None else Some(atoms.toList.maxBy(_._2)._1)
  }

  private class NoProofFoundException(val unsolvable: Sequent) extends Exception

  // Given a sequent, return a proof of that sequent if on exists that only uses propositional logic rules and reflexivity of equality.
  // Alternates between reducing the formulas using the OL algorithm for propositional logic and branching on an atom using excluded middle.
  // An atom is a subformula of the input that is either a predicate, a binder or a schematic connector, i.e. a subformula that has not meaning in propositional logic.
  private def solveAugSequent(s: AugSequent, offset: Int)(using MaRvIn: VariableFormulaLabel): List[SCProofStep] = {
    val bestAtom = findBestAtom(s.formula)
    val redF = reducedForm(s.formula)
    if (redF == top()) {
      List(RestateTrue(s.decisions._1 ++ s.decisions._2.map((f: Formula) => Neg(f)) |- s.formula))
    } else if (bestAtom.isEmpty) {
      assert(redF == bot()) // sanity check; If the formula has no atom left in it and is reduced, it should be either ⊤ or ⊥.
      val res = s.decisions._1 |- redF :: s.decisions._2 // the branch that can't be closed
      throw new NoProofFoundException(res)
    } else {
      val atom = bestAtom.get
      val optLambda = Substitution.applySubst.findSubformula(redF, Seq((MaRvIn, atom)))
      if (optLambda.isEmpty) return solveAugSequent(AugSequent(s.decisions, redF), offset)
      val lambdaF = optLambda.get

      val seq1 = AugSequent((atom :: s.decisions._1, s.decisions._2), lambdaF(Seq(top())))
      val proof1 = solveAugSequent(seq1, offset)
      val subst1 = RightSubstIff(atom :: s.decisions._1 ++ s.decisions._2.map((f: Formula) => Neg(f)) |- redF, offset + proof1.length - 1, List((atom, top())), lambdaF)
      val seq2 = AugSequent((s.decisions._1, atom :: s.decisions._2), lambdaF(Seq(bot())))
      val proof2 = solveAugSequent(seq2, offset + proof1.length + 1)
      val subst2 = RightSubstIff(Neg(atom) :: s.decisions._1 ++ s.decisions._2.map((f: Formula) => Neg(f)) |- redF, offset + proof1.length + proof2.length - 1 + 1, List((atom, bot())), lambdaF)
      val red2 = Restate(s.decisions._1 ++ s.decisions._2.map((f: Formula) => Neg(f)) |- (redF, atom), offset + proof1.length + proof2.length + 2 - 1)
      val cutStep = Cut(s.decisions._1 ++ s.decisions._2.map((f: Formula) => Neg(f)) |- redF, offset + proof1.length + proof2.length + 3 - 1, offset + proof1.length + 1 - 1, atom)
      val redStep = Restate(s.decisions._1 ++ s.decisions._2.map((f: Formula) => Neg(f)) |- s.formula, offset + proof1.length + proof2.length + 4 - 1)
      redStep :: cutStep :: red2 :: subst2 :: proof2 ++ (subst1 :: proof1)

    }
  }

}
