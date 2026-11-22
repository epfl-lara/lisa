package lisa.utils.prooflib

import lisa.utils.K
import lisa.utils.LisaException
import lisa.utils.fol.FOL._

import scala.collection.View
import scala.collection.mutable

final class ProofBuilder private (val lib: Library, val goal: Option[Sequent], val isTactic: Boolean, inheritedAssumptions: Iterable[Expr[Prop]] = Nil):
  given Library = lib
  given K.Theory = lib.theory

  private val currentErrors = mutable.ArrayBuffer.empty[ProofDiagnostic]
  private val currentAssumptions: mutable.Set[Expr[Prop]] = mutable.Set.from(inheritedAssumptions)

  private var lastKnown: Option[Thm] = None

  def last: Option[Thm] = lastKnown

  def errors: View[ProofDiagnostic] = currentErrors.view

  def assumptions: View[Expr[Prop]] = currentAssumptions.view

  def assume(formula: Expr[Prop]): Unit =
    currentAssumptions += formula

  def assume(formulas: Iterable[Expr[Prop]]): Unit =
    currentAssumptions ++= formulas

  def withAssumptions(statement: lisa.utils.fol.FOL.Sequent): lisa.utils.fol.FOL.Sequent =
    if currentAssumptions.isEmpty then statement
    else lisa.utils.fol.FOL.Sequent(statement.left ++ currentAssumptions, statement.right)

  def report(error: ProofDiagnostic): Unit =
    currentErrors += error

  def report(errors: Iterable[ProofDiagnostic]): Unit =
    currentErrors ++= errors

  /**
   * Runs a goal-bearing user boundary, admitting its conclusion on a Lisa exception or returned failure.
   */
  private[prooflib] def recover(conclusion: Sequent)(body: => ProofJudgement)(using file: sourcecode.File, line: sourcecode.Line): ProofJudgement =
    def admit(error: LisaException): ProofJudgement =
      val admitted = BasicStep.Sorry(conclusion)
      report(ProofDiagnostic(error, file, line, conclusion))
      admitted

    val result =
      if isTactic then body
      else
        try body
        catch case error: LisaException => admit(error)

    result match
      case ProofCarrier.Failure(message) if !isTactic => admit(new TacticFailureException(message))
      case _ => result

  def absorb[T](carrier: ProofCarrier[T]): ProofCarrier[T] =
    carrier match
      case ProofCarrier.Success(theorem, _) => lastKnown = Some(theorem)
      case _: ProofCarrier.Failure => ()
    carrier

  def absorbDestruct[T](carrier: ProofCarrier[T])(using sourcecode.File, sourcecode.Line): (Thm, T) =
    absorb(carrier).destruct

  private def child(goal: Option[Sequent] = None, inheritAssumptions: Boolean = true): ProofBuilder =
    new ProofBuilder(lib, goal, isTactic, if inheritAssumptions then currentAssumptions else Nil)

  def withSubcontext[T](goal: Option[Sequent] = None, inheritAssumptions: Boolean = true)(inner: ProofBuilder ?=> ProofCarrier[T]): ProofCarrier[T] =
    val subproof = child(goal, inheritAssumptions)
    try inner(using subproof)
    finally report(subproof.errors)

  def pure[T](result: T): ProofCarrier[T] =
    last match
      case Some(theorem) => ProofCarrier.Success(theorem, result)
      case None => ProofCarrier.Failure("The proof produced no theorem.")

object ProofBuilder:
  def withGoal(using lib: Library)(goal: Sequent, isTactic: Boolean = false): ProofBuilder = new ProofBuilder(lib, Some(goal), isTactic)
  def withKernelGoal(using lib: Library)(goal: K.Sequent): ProofBuilder = withGoal(Thm.liftSequent(goal))

  def withContext[T](using lib: Library)(inner: ProofBuilder ?=> ProofCarrier[T]): ProofCarrier[T] =
    freshContext(isTactic = false)(inner)

  private[prooflib] def freshContext[T](using lib: Library)(isTactic: Boolean)(inner: ProofBuilder ?=> ProofCarrier[T]): ProofCarrier[T] =
    val proof = new ProofBuilder(lib, None, isTactic)
    inner(using proof)
