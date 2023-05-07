package lisa.prooflib

import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.SCProofChecker
import lisa.kernel.proof.SCProofCheckerJudgement
import lisa.kernel.proof.SequentCalculus
import lisa.prooflib.ProofTacticLib.ProofTactic
import lisa.utils.{_, given}


import scala.collection.mutable.Stack as stack

/**
 * A class abstracting a [[lisa.kernel.proof.RunningTheory]] providing utility functions and a convenient syntax
 * to write and use Theorems and Definitions.
 * @param theory The inner RunningTheory
 */
abstract class Library extends lisa.prooflib.WithTheorems with lisa.prooflib.ProofsHelpers {
  val theory: RunningTheory
  given library: this.type = this
  given RunningTheory = theory

  export lisa.kernel.fol.FOL.{Formula, *}
  val SC: SequentCalculus.type = lisa.kernel.proof.SequentCalculus
  export lisa.kernel.proof.SequentCalculus.{Sequent, SCProofStep}
  export lisa.kernel.proof.SCProof
  export lisa.prooflib.TheoriesHelpers.{_, given}

  /**
   * a type representing different types that have a natural representation as K.Sequent
   */

  var last: Option[theory.Justification] = None

  // kernel theory management

  /**
   * An alias to create a Theorem
   */
  def makeTheorem(name: String, statement: K.Sequent, proof: K.SCProof, justifications: Seq[theory.Justification]): K.Judgement[theory.Theorem] =
    theory.theorem(name, statement, proof, justifications)

  // DEFINITION Syntax

  /**
   * Allows to create a definition by shortcut of a function symbol:
   */
  def simpleDefinition(symbol: String, expression: LambdaTermTerm): K.Judgement[theory.FunctionDefinition] = {
    val LambdaTermTerm(vars, body) = expression

    val out: VariableLabel = VariableLabel(freshId((vars.map(_.id) ++ body.schematicTermLabels.map(_.id)).toSet, "y"))
    val proof: K.SCProof = simpleFunctionDefinition(expression, out)
    theory.functionDefinition(symbol, LambdaTermFormula(vars, out === body), out, proof, out === body, Nil)
  }

  /**
   * Allows to create a definition by shortcut of a predicate symbol:
   */
  def simpleDefinition(symbol: String, expression: LambdaTermFormula): K.Judgement[theory.PredicateDefinition] =
    theory.predicateDefinition(symbol, expression)

  private def simpleFunctionDefinition(expression: LambdaTermTerm, out: VariableLabel): K.SCProof = {
    val x = out
    val LambdaTermTerm(vars, body) = expression
    val xeb = x === body
    val y = VariableLabel(freshId(body.freeVariables.map(_.id) ++ vars.map(_.id) + out.id, "y"))
    val s0 = SC.RightRefl(() |- body === body, body === body)
    val s1 = SC.Restate(() |- (xeb) <=> (xeb), 0)
    val s2 = SC.RightForall(() |- forall(x, (xeb) <=> (xeb)), 1, (xeb) <=> (xeb), x)
    val s3 = SC.RightExists(() |- exists(y, forall(x, (x === y) <=> (xeb))), 2, forall(x, (x === y) <=> (xeb)), y, body)
    val s4 = SC.Restate(() |- existsOne(x, xeb), 3)
    val v = Vector(s0, s1, s2, s3, s4)
    K.SCProof(v)
  }

  //////////////////////////////////////////
  //      Tools for proof development     //
  //////////////////////////////////////////


  /**
   * Prints a short representation of the last theorem or definition introduced
   */
  def show(using om: OutputManager): theory.Justification = last match {
    case Some(value) => value.show
    case None => throw new NoSuchElementException("There is nothing to show: No theorem or definition has been proved yet.")
  }




}
