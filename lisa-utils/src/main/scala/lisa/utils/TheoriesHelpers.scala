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
    def theorem(name: String, statement: Sequent, proof: SCProof, justifications: Seq[theory.Justification]): RunningTheoryJudgement[theory.Theorem] = {
      if (statement == proof.conclusion) theory.makeTheorem(name, statement, proof, justifications)
      else if (isSameSequent(statement, proof.conclusion)) theory.makeTheorem(name, statement, proof.appended(Rewrite(statement, proof.length - 1)), justifications)
      else InvalidJustification(s"The proof proves ${FOLPrinter.prettySequent(proof.conclusion)} instead of claimed ${FOLPrinter.prettySequent(statement)}", None)
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
     * of the theorem to have more explicit writing and for sanity check. See also [[lisa.kernel.proof.RunningTheory.makePredicateDefinition]]
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
    def repr: String = just match {
      case thm: RunningTheory#Theorem => s" Theorem ${thm.name} := ${FOLPrinter.prettySequent(thm.proposition)}\n"
      case axiom: RunningTheory#Axiom => s" Axiom ${axiom.name} := ${FOLPrinter.prettyFormula(axiom.ax)}\n"
      case d: RunningTheory#Definition =>
        d match {
          case pd: RunningTheory#PredicateDefinition =>
            s" Definition of predicate symbol ${pd.label.id} := ${FOLPrinter.prettyFormula(pd.label(pd.expression.vars.map(VariableTerm.apply)*) <=> pd.expression.body)}\n"
          case fd: RunningTheory#FunctionDefinition =>
            s" Definition of function symbol ${FOLPrinter.prettyTerm(fd.label(fd.expression.vars.map(VariableTerm.apply)*))} := the ${fd.out.id} such that ${FOLPrinter
                .prettyFormula((fd.out === fd.label(fd.expression.vars.map(VariableTerm.apply)*)) <=> fd.expression.body)})\n"
        }
    }

    /**
     * Outputs, with an implicit om.output function, a readable representation of the Axiom, Theorem or Definition.
     */
    def show(using om: OutputManager): just.type = {
      om.output(repr, Console.GREEN)
      just

    }
  }

  extension [J <: RunningTheory#Justification](theoryJudgement: RunningTheoryJudgement[J]) {

    /**
     * If the Judgement is valid, show the inner justification and returns it.
     * Otherwise, om.output the error leading to the invalid justification and throw an error.
     */
    def repr: String = {
      theoryJudgement match {
        case RunningTheoryJudgement.ValidJustification(just) =>
          just.repr
        case InvalidJustification(message, error) =>
          s"$message\n${error match {
              case Some(judgement) => FOLPrinter.prettySCProof(judgement)
              case None => ""
            }}"
      }
    }

    /**
     * If the Judgement is valid, show the inner justification and returns it.
     * Otherwise, om.output the error leading to the invalid justification and throw an error.
     */
    def show(using om: OutputManager): Unit = {
      om.output(repr)
    }

    /**
     * If the Judgement is valid, show the inner justification and returns it.
     * Otherwise, om.output the error leading to the invalid justification and throw an error.
     */
    def showAndGet(using om: OutputManager): J = {
      theoryJudgement match {
        case RunningTheoryJudgement.ValidJustification(just) =>
          just.show
        case InvalidJustification(message, error) =>
          om.output(s"$message\n${error match {
              case Some(judgement) => FOLPrinter.prettySCProof(judgement)
              case None => ""
            }}")
          om.finishOutput(InvalidJustificationException(message, error))
      }
    }
  }

  extension (proofJudgement: SCProofCheckerJudgement) {

    /**
     * If the SCProof is valid, show the inner proof and returns it.
     * Otherwise, om.output the error leading to the invalid justification and throw an error.
     */
    def showAndGet(using om: OutputManager): SCProof = {
      proofJudgement match {
        case SCProofCheckerJudgement.SCValidProof(proof) =>
          om.output(FOLPrinter.prettySCProof(proofJudgement))
          proof
        case ip @ SCProofCheckerJudgement.SCInvalidProof(proof, path, message) =>
          om.output(s"$message\n${FOLPrinter.prettySCProof(proofJudgement)}")
          om.finishOutput(InvalidJustificationException("", Some(ip)))
      }
    }
  }

  case class InvalidProofException(proofJudgement: SCProofCheckerJudgement.SCInvalidProof) extends Exception(proofJudgement.message)

  /**
   * om.output a readable representation of a proof.
   */
  def checkProof(proof: SCProof, output: String => Unit = println): Unit = {
    val judgement = SCProofChecker.checkSCProof(proof)
    output(FOLPrinter.prettySCProof(judgement))
  }

}
