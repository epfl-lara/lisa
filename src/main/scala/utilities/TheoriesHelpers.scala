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

    def functionDefinition(symbol:String, expression:LambdaTermFormula, out:VariableLabel, proof:SCProof, justifications:Seq[theory.Justification] ): RunningTheoryJudgement[theory.FunctionDefinition] = {
      val label = ConstantFunctionLabel(symbol, expression.vars.size)
      theory.makeFunctionDefinition(proof, justifications, label, out, expression)
    }
    def predicateDefinition(symbol:String, expression:LambdaTermFormula): RunningTheoryJudgement[theory.PredicateDefinition] = {
      val label = ConstantPredicateLabel(symbol, expression.vars.size)
      theory.makePredicateDefinition(label, expression)
    }

    def getJustification(name: String): Option[theory.Justification] = theory.getAxiom(name).orElse(theory.getTheorem(name)).orElse(theory.getDefinition(name))

  extension (just: RunningTheory#Justification)
    def show(implicit output: String => Unit ): just.type = {
      just match
        case thm: RunningTheory#Theorem => output(s" Theorem ${thm.name} := ${Printer.prettySequent(thm.proposition)}\n")
        case axiom: RunningTheory#Axiom => output(s" Axiom ${axiom.name} := ${Printer.prettyFormula(axiom.ax)}\n")
        case d: RunningTheory#Definition =>
          d match
            case pd: RunningTheory#PredicateDefinition =>
              output(s" Definition of predicate symbol ${pd.label.id} := ${Printer.prettyFormula(pd.label(pd.expression.vars.map(_())*) <=> pd.expression.body)}\n") // (label, args, phi)
            case fd: RunningTheory#FunctionDefinition =>
              output(s" Definition of function symbol ${fd.label.id} := ${Printer.prettyFormula(( fd.out === fd.label(fd.expression.vars.map(_())*)) <=> fd.expression.body)})\n")
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
