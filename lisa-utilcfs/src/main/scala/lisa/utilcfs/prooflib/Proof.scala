package lisa.utilcfs.prooflib

import lisa.utilcfs.K

import lisa.kernelcf.proof.Sequent
import lisa.kernelcf.proof.Thm

import scala.collection.mutable
import scala.collection.View

final class Proof private (val lib: Library, val goal: Option[Sequent], inheritedAssumptions: Iterable[K.Expression] = Nil):
  given Library = lib
  given K.Theory = lib.theory

  private val currentErrors: mutable.Set[ProofError] = mutable.Set.empty
  private val currentAssumptions: mutable.Set[K.Expression] = mutable.Set.from(inheritedAssumptions)

  var lastKnown: Option[Thm] = None

  def last: Option[Thm] = lastKnown

  def errors: View[ProofError] = currentErrors.view

  def assumptions: View[K.Expression] = currentAssumptions.view

  def assume(formula: K.Expression): Unit =
    currentAssumptions += formula

  def assume(formulas: Iterable[K.Expression]): Unit =
    currentAssumptions ++= formulas

  def withAssumptions(statement: Sequent): Sequent =
    if currentAssumptions.isEmpty then statement
    else Sequent(statement.left ++ currentAssumptions, statement.right)

  def report(error: ProofError): Unit =
    currentErrors += error

  def report(errors: Iterable[ProofError]): Unit =
    currentErrors ++= errors

  def absorb[T](carrier: ProofCarrier[T]): ProofCarrier[T] =
    report(carrier.errors)
    carrier.justification.foreach(thm => lastKnown = Some(thm))
    carrier

  def absorbDestruct[T](carrier: ProofCarrier[T]): (Thm, T) =
    absorb(carrier).destruct

  private def child(goal: Option[Sequent] = None): Proof =
    new Proof(lib, goal, currentAssumptions)

  def withSubcontext[T](goal: Option[Sequent] = None)(inner: Proof ?=> ProofCarrier[T]): ProofCarrier[T] =
    val subproof = child(goal)
    val carrier = inner(using subproof)
    val merged = carrier.withErrors(subproof.errors)
    report(merged.errors)
    merged


  def pure[T](result: T): ProofCarrier[T] =
    val lastJudgement = 
      last match
        case Some(j) => j
        case None => 
          K.Sorry(goal.getOrElse(Sequent(Set.empty, Set(K.top)))) match
            case Right(j) => j
    ProofCarrier(
      currentErrors.toSet,
      lastJudgement.statement,
      Some(lastJudgement),
      result
    )

object Proof:
  private def empty(using lib: Library): Proof = new Proof(lib, None)
  def withGoal(using lib: Library)(goal: Sequent): Proof = new Proof(lib, Some(goal))

  def withContext[T](using lib: Library)(inner: Proof ?=> ProofCarrier[T]): ProofCarrier[T] =
    val proof = Proof.empty
    val carrier = inner(using proof)
    carrier.withErrors(proof.errors)
