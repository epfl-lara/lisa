package utilities

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheoryJudgement.InvalidJustification
import lisa.kernel.proof.SequentCalculus.*
import lisa.kernel.proof.*
import utilities.Printer

trait TheoriesHelpers extends KernelHelpers {

  // for when the kernel will have a dedicated parser
  extension (theory: RunningTheory)
    def theorem(name: String, statement: String, proof: SCProof, justifications: Seq[theory.Justification]): RunningTheoryJudgement[theory.Theorem] = {
      val expected = proof.conclusion // parse(statement)
      if (expected == proof.conclusion) theory.makeTheorem(name, expected, proof, justifications)
      else if (isSameSequent(expected, proof.conclusion)) theory.makeTheorem(name, expected, proof.appended(Rewrite(expected, proof.length - 1)), justifications)
      else InvalidJustification("The proof does not prove the claimed statement", None)
    }

    def getJustification(name: String): Option[theory.Justification] = theory.getAxiom(name).orElse(theory.getTheorem(name)).orElse(theory.getDefinition(name))

  extension (just: RunningTheory#Justification)
    def show(output: String => Unit = println): just.type = {
      just match
        case thm: RunningTheory#Theorem => output(s"Theorem ${thm.name} := ${Printer.prettySequent(thm.proposition)}")
        case axiom: RunningTheory#Axiom => output(s"Axiom ${axiom.name} := ${Printer.prettyFormula(axiom.ax)}")
        case d: RunningTheory#Definition =>
          d match
            case pd: RunningTheory#PredicateDefinition =>
              output(s"Definition of predicate symbol ${pd.label.id} := ${Printer.prettyFormula(pd.label(pd.args.map(VariableTerm(_))*) <=> pd.phi)}") // (label, args, phi)
            case fd: RunningTheory#FunctionDefinition =>
              output(s"Definition of function symbol ${fd.label.id} := ${Printer.prettyFormula((fd.label(fd.args.map(VariableTerm(_))*) === fd.out) <=> fd.phi)})")
        // output(Printer.prettySequent(thm.proposition))
        // thm
      just
    }

  extension [J <: RunningTheory#Justification](theoryJudgement: RunningTheoryJudgement[J]) {

    def showAndGet(output: String => Unit = println): J = {
      theoryJudgement match
        case RunningTheoryJudgement.ValidJustification(just) =>
          just.show(output)
        case InvalidJustification(message, error) =>
          output(s"$message\n${error match
              case Some(judgement) => Printer.prettySCProof(judgement)
              case None => ""
            }")
          theoryJudgement.get
    }
  }

  def checkProof(proof: SCProof, output: String => Unit = println): Unit = {
    val judgement = SCProofChecker.checkSCProof(proof)
    output(Printer.prettySCProof(judgement))
  }
}
