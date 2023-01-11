package lisa.automation.kernel

import lisa.kernel.proof.SequentCalculus as LK
import lisa.kernel.proof.SequentCalculus.*
import lisa.kernel.proof.SCProof
import lisa.kernel.fol.FOL.*
import lisa.utils.Helpers.{given, *}

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
  def solveSequent(s:Sequent): Option[List[SCProofStep]] = {
    val augSeq = augmentSequent(s)
    val MaRvIn = VariableFormulaLabel(freshId(augSeq.formula.schematicFormulaLabels.map(_.id), "MaRvIn")) //arbitrary name that is unlikely to already exist in the formula

    try {
      Some(solveAugSequent(augSeq, 0)(using MaRvIn ).reverse)
    }
    catch case e:NoProofFoundException => None

  }
  //Given a sequent, return a proof of that sequent if on exists that only uses propositional logic rules and reflexivity of equality.
  private def solveAugSequent(s:AugSequent, offset:Int)(using MaRvIn : VariableFormulaLabel): List[SCProofStep] = {
    if (isSame(s.formula, top())) {
      List(RewriteTrue(s.decisions._1 |- s.formula::s.decisions._2))
    }
    else if (s.atoms.isEmpty) {
      throw new NoProofFoundException
    }
    else {
      val atom = s.atoms.head
      val remaining = s.atoms.tail
      val optLambda = SimpleSimplifier.findSubformula(s.formula, Seq((MaRvIn, atom)))
      if (optLambda.isEmpty) return solveAugSequent(AugSequent(s.decisions, s.formula, remaining), offset)
      val lambdaF = optLambda.get

      val seq1 = AugSequent((atom::s.decisions._1, s.decisions._2), reducedForm(lambdaF(Seq(top()))), remaining)
      val proof1 = solveAugSequent(seq1, offset)
      val seq2 = AugSequent((s.decisions._1, atom::s.decisions._2), reducedForm(lambdaF(Seq(bot()))), remaining)
      val proof2 = solveAugSequent(seq2, offset+proof1.length)
      val newStep = Cut(s.decisions._1 |- s.formula::s.decisions._2, offset+proof1.length-1, offset+proof1.length+proof2.length-1, atom)
      newStep::(proof2++proof1)

      }
    }
  
  //def reduce
}
