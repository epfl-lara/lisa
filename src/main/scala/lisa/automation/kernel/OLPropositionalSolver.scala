package lisa.automation.kernel

import lisa.kernel.proof.SequentCalculus as LK
import lisa.kernel.proof.SequentCalculus.*
import lisa.kernel.proof.SCProof
import lisa.kernel.fol.FOL.*
import lisa.utils.Helpers.{*, given}
import lisa.utils.tactics.SimpleDeducedSteps.Restate

object OLPropositionalSolver {
  
  //Augmented Sequent
  private case class AugSequent(decisions: (List[Formula], List[Formula]), formula:Formula, atoms:List[Formula])

  //Transform a sequent into a format more adequate for solving
  private def augmentSequent(s:Sequent): AugSequent = {
    val f = reducedForm(sequentToFormula(s))
    var atoms: List[Formula] = Nil
    findAtoms(f, a => atoms = a::atoms)
    AugSequent((Nil, Nil), f, atoms)
  }





  //Find all "atoms" of the formula.
  //We mean atom in the propositional logic sense, so any formula starting with a predicate symbol, a binder or a schematic connector is an atom here.
  private def findAtoms(f:Formula, add : Formula => Unit): Unit = f match {
    case f: PredicateFormula => add(f)
    case ConnectorFormula(label, args) => label match {
      case label: ConstantConnectorLabel => args.foreach(c => findAtoms(c, add))
      case SchematicConnectorLabel(id, arity) => add(f)
    }
    case BinderFormula(label, bound, inner) => add(f)
  }

  private class NoProofFoundException extends Exception
  def solveSequent(s:Sequent): Option[SCProof] = {
    val augSeq = augmentSequent(s)
    val MaRvIn = VariableFormulaLabel(freshId(augSeq.formula.schematicFormulaLabels.map(_.id), "MaRvIn")) //arbitrary name that is unlikely to already exist in the formula

    try {
      Some(SCProof(solveAugSequent(augSeq, 0)(using MaRvIn ).reverse.toIndexedSeq))
    }
    catch case e:NoProofFoundException => None

  }
  //Given a sequent, return a proof of that sequent if on exists that only uses propositional logic rules and reflexivity of equality.
  private def solveAugSequent(s:AugSequent, offset:Int)(using MaRvIn : VariableFormulaLabel): List[SCProofStep] = {
    if (isSame(s.formula, top())) {
      List(RewriteTrue(s.decisions._1++s.decisions._2.map((f:Formula) => Neg(f)) |- s.formula))
    }
    else if (s.atoms.isEmpty) {
      throw new NoProofFoundException
    }
    else {
      val atom = s.atoms.head
      val remaining = s.atoms.tail
      val redF = reducedForm(s.formula)
      val optLambda = SimpleSimplifier.findSubformula(redF, Seq((MaRvIn, atom)))
      if (optLambda.isEmpty) return solveAugSequent(AugSequent(s.decisions, redF, remaining), offset)
      val lambdaF = optLambda.get



      val seq1 = AugSequent((atom::s.decisions._1, s.decisions._2), lambdaF(Seq(top())), remaining)
      val proof1 = solveAugSequent(seq1, offset)
      val subst1 = RightSubstIff(atom::s.decisions._1++s.decisions._2.map((f:Formula) => Neg(f)) |- redF, offset+proof1.length-1, List((atom, top())), lambdaF)
      val seq2 = AugSequent((s.decisions._1, atom::s.decisions._2), lambdaF(Seq(bot())), remaining)
      val proof2 = solveAugSequent(seq2, offset+proof1.length+1)
      val subst2 = RightSubstIff(Neg(atom)::s.decisions._1++s.decisions._2.map((f:Formula) => Neg(f)) |- redF, offset+proof1.length+proof2.length-1+1, List((atom, bot())), lambdaF)
      val red2 = Rewrite(s.decisions._1++s.decisions._2.map((f:Formula) => Neg(f)) |- (redF, atom), offset+proof1.length+proof2.length+2-1)
      val cutStep = Cut(s.decisions._1 |- redF::s.decisions._2, offset+proof1.length+proof2.length+3-1, offset+proof1.length+1-1, atom)
      val redStep = Rewrite(s.decisions._1 |- s.formula::s.decisions._2, offset+proof1.length+proof2.length+4-1)
      redStep::cutStep::red2::subst2::proof2++(subst1::proof1)

      }
    }
  
  //def reduce
}
