package lisa.utilcfs.prooflib

import lisa.kernelcf.proof.{Sequent, Thm}
import lisa.utilcfs.K

final case class ProofCarrier[+T](
    errors: Set[ProofError],
    statement: Sequent,
    justification: Option[Thm],
    payload: T
)(using lib: Library):
  given K.Theory = lib.theory

  /**
    * A carrier is valid iff it has no accumulated errors and has a valid
    * justification.
    */
  def isValid: Boolean = errors.isEmpty && justification.nonEmpty
  /**
   * Whether this carrier has a valid justification. A carrier may have errors
   * but still have a valid justification.
   */
  def hasJustification: Boolean = justification.nonEmpty

  /**
    * This carrier with the payload transformed by the given function.
    */
  def map[U](f: T => U): ProofCarrier[U] =
    copy(payload = f(payload))

  /**
    * This carrier with the payload and justification transformed by the given
    * function.
    */
  def flatMap[U](f: (T, Thm) => ProofCarrier[U]): ProofCarrier[U] =
    val next = f(payload, destruct._1)
    next.copy(errors = errors ++ next.errors)

  /**
    * This carrier with an additional error.
    */
  def withError(error: ProofError): ProofCarrier[T] =
    copy(errors = errors + error)

  /**
    * This carrier with additional appended errors.
    */
  def withErrors(extraErrors: Iterable[ProofError]): ProofCarrier[T] =
    copy(errors = errors ++ extraErrors)

  /**
    * This carrier with an overriden justification. Used to add a step while
    * preserving values and errors.
    *
    * Use [[flatMap]] to additionally transform the existing justification
    * and/or payload.
    */
  def withJustification(just: Thm): ProofCarrier[T] =
    copy(justification = Some(just))

  /**
    * This carrier with the payload discarded.
    */
  def judgement: ProofJudgement =
    copy(payload = ())

  /**
    * The carrier's theorem and payload, using a sorry theorem when no
    * justification was produced.
    */
  def destruct: (Thm, T) =
    justification.getOrElse(K.sorry(using lib.theory)(statement)) -> payload

type ProofJudgement = ProofCarrier[Unit]

object ProofJudgement:
  def apply(using lib: Library)(just: Thm): ProofJudgement =
    ProofCarrier(Set.empty, just.statement, Some(just), ())

extension (kernelResult: Either[ProofError, Thm])(using lib: Library)
  def lift(intendedConclusion: Sequent): ProofJudgement =
    kernelResult match
      case Left(err) => 
        ProofCarrier(Set(err), intendedConclusion, None, ())
      case Right(j) => 
        assert(j.statement == intendedConclusion, s"Justification statement ${j.statement} does not match intended conclusion $intendedConclusion")
        ProofCarrier(Set.empty, intendedConclusion, Some(j), ())
