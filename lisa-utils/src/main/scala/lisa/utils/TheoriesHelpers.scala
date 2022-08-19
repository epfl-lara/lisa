package lisa.utils

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheoryJudgement.InvalidJustification
import lisa.kernel.proof.RunningTheoryJudgement.InvalidJustificationException
import lisa.kernel.proof.SequentCalculus.*
import lisa.kernel.proof.*
import lisa.utils.Printer

/**
 * A helper file that provides various syntactic sugars for LISA's FOL and proofs. Best imported through utilities.Helpers
 * Usage:
 * <pre>
 * import utilities.Helpers.*
 * </pre>
 * or
 * <pre>
 * extends utilities.KernelHelpers.*
 * </pre>
 */
trait TheoriesHelpers extends KernelHelpers {

  extension (theory: RunningTheory) {

    /**
     * Add a theorem to the theory, but also asks explicitely for the desired conclusion
     * of the theorem to have more explicit writing and for sanity check.
     */
    def theorem(name: String, statement: String, proof: SCProof, justifications: Seq[theory.Justification]): RunningTheoryJudgement[theory.Theorem] = {
      val expected = proof.conclusion // parse(statement)
      if (expected == proof.conclusion) theory.makeTheorem(name, expected, proof, justifications)
      else if (isSameSequent(expected, proof.conclusion)) theory.makeTheorem(name, expected, proof.appended(Rewrite(expected, proof.length - 1)), justifications)
      else InvalidJustification("The proof does not prove the claimed statement", None)
    }

    /**
     * Make a function definition in the theory, but only ask for the identifier of the new symbol; Arity is inferred
     * of the theorem to have more explicit writing and for sanity check. See [[lisa.kernel.proof.RunningTheory.makeFunctionDefinition]]
     */
    def functionDefinition(
        symbol: String,
        expression: LambdaTermFormula,
        out: VariableLabel,
        proof: SCProof,
        justifications: Seq[theory.Justification]
    ): RunningTheoryJudgement[theory.FunctionDefinition] = {
      val label = ConstantFunctionLabel(symbol, expression.vars.size)
      theory.makeFunctionDefinition(proof, justifications, label, out, expression)
    }

    /**
     * Make a predicate definition in the theory, but only ask for the identifier of the new symbol; Arity is inferred
     * of the theorem to have more explicit writing and for sanity check. See [[lisa.kernel.proof.RunningTheory.makePredicateDefinition]]
     */
    def predicateDefinition(symbol: String, expression: LambdaTermFormula): RunningTheoryJudgement[theory.PredicateDefinition] = {
      val label = ConstantPredicateLabel(symbol, expression.vars.size)
      theory.makePredicateDefinition(label, expression)
    }

    /**
     * Try to fetch, in this order, a justification that is an Axiom with the given name,
     * a Theorem with a given name or a Definition with a the given name as symbol
     */
    def getJustification(name: String): Option[theory.Justification] = theory.getAxiom(name).orElse(theory.getTheorem(name)).orElse(theory.getDefinition(name))
  }

  extension (just: RunningTheory#Justification) {

    /**
     * Outputs, with an implicit output function, a readable representation of the Axiom, Theorem or Definition.
     */
    def show(using output: String => Unit): just.type = {
      just match {
        case thm: RunningTheory#Theorem => output(s" Theorem ${thm.name} := ${Printer.prettySequent(thm.proposition)}\n")
        case axiom: RunningTheory#Axiom => output(s" Axiom ${axiom.name} := ${Printer.prettyFormula(axiom.ax)}\n")
        case d: RunningTheory#Definition =>
          d match {
            case pd: RunningTheory#PredicateDefinition =>
              output(s" Definition of predicate symbol ${pd.label.id} := ${Printer.prettyFormula(pd.label(pd.expression.vars.map(VariableTerm.apply)*) <=> pd.expression.body)}\n") // (label, args, phi)
            case fd: RunningTheory#FunctionDefinition =>
              output(s" Definition of function symbol ${Printer.prettyTerm(fd.label(fd.expression.vars.map(VariableTerm.apply)*))} := the ${fd.out.id} such that ${Printer
                  .prettyFormula((fd.out === fd.label(fd.expression.vars.map(VariableTerm.apply)*)) <=> fd.expression.body)})\n")
          }
      }
      just
    }
  }

  extension [J <: RunningTheory#Justification](theoryJudgement: RunningTheoryJudgement[J]) {

    /**
     * If the Judgement is valid, show the inner justification and returns it.
     * Otherwise, output the error leading to the invalid justification and throw an error.
     */
    def showAndGet(using output: String => Unit)(using finishOutput: Throwable => Nothing): J = {
      theoryJudgement match {
        case RunningTheoryJudgement.ValidJustification(just) =>
          just.show
        case InvalidJustification(message, error) =>
          output(s"$message\n${error match {
              case Some(judgement) => Printer.prettySCProof(judgement)
              case None => ""
            }}")
          finishOutput(InvalidJustificationException(message, error))
      }
    }
  }

  /**
   * Output a readable representation of a proof.
   */
  def checkProof(proof: SCProof, output: String => Unit = println): Unit = {
    val judgement = SCProofChecker.checkSCProof(proof)
    output(Printer.prettySCProof(judgement))
  }

}
