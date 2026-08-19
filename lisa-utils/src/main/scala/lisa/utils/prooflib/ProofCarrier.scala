package lisa.utils.prooflib

import lisa.utils.K
import lisa.utils.fol.FOL.Sequent

trait ProofCarrierException extends Exception
case class FatalCarrierDestructionException(carrier: FatalCarrier, file: sourcecode.File, line: sourcecode.Line)
    extends Exception(s"Attempted recovery of a fatal error state.")
    with ProofCarrierException

trait ProofCarrier[+T]:
  val errors: Set[ProofError]

  def justification: Option[Thm]

  /**
   * A carrier is valid iff it has no accumulated errors and has a valid
   * justification.
   */
  def isValid: Boolean

  /**
   * Whether this carrier has a valid justification. A carrier may have errors
   * but still have a valid justification.
   */
  def hasJustification: Boolean

  /**
   * This carrier with the payload transformed by the given function.
   */
  def map[U](f: T => U): ProofCarrier[U]

  /**
   * This carrier with the payload and justification transformed by the given
   * function.
   */
  def flatMap[U](f: (T, Thm) => ProofCarrier[U]): ProofCarrier[U]

  /**
   * This carrier with an additional error.
   */
  def withError(error: ProofError): ProofCarrier[T]

  /**
   * This carrier with additional appended errors.
   */
  def withErrors(extraErrors: Iterable[ProofError]): ProofCarrier[T]

  /**
   * This carrier with the payload discarded.
   */
  def judgement: ProofJudgement

  /**
   * The carrier's theorem and payload, using a sorry theorem when no
   * justification was produced. 
   * 
   * @throws FatalCarrierDestructionException if this carrier holds a fatal error; see [[FatalCarrier]].
   */
  def destruct(using file: sourcecode.File, line: sourcecode.Line): (Thm, T)

  /**
   * This carrier with an overriden justification. Used to add a step while
   * preserving values and errors.
   *
   * Use [[flatMap]] to additionally transform the existing justification
   * and/or payload.
   * 
   * @throws FatalCarrierDestructionException if this carrier holds a fatal error; see [[FatalCarrier]].
   */
  def withJustification(using file: sourcecode.File, line: sourcecode.Line)(just: Thm): ProofCarrier[T]

object ProofCarrier:
  def apply[U](errors: Set[ProofError], statement: Sequent, justification: Option[Thm], payload: U)(using lib: Library): ProofCarrier[U] =
    SoftCarrier(errors, statement, justification, payload)

type ProofJudgement = ProofCarrier[Unit]

final case class FatalCarrier(fatalError: FatalError, errors: Set[ProofError]) extends ProofCarrier[Nothing]:

  /**
   * Recover from a fatal error if exiting a context where an intended
   * conclusion is known. Should only be used at the boundaries of subproofs and
   * theorems.
   *
   * In effect, the only meaningful thing you can do with a fatal carrier.
   */
  def recoverWith(statement: Sequent)(using lib: Library): ProofCarrier[Unit] =
    ProofCarrier(errors + fatalError, statement, None, ())

  def justification: Option[Thm] = None
  def flatMap[U](f: (Nothing, Thm) => ProofCarrier[U]): this.type = this
  def hasJustification: Boolean = false
  def isValid: Boolean = false
  def judgement: ProofJudgement = this
  def map[U](f: Nothing => U): this.type = this
  def withError(error: ProofError): ProofCarrier[Nothing] =
    copy(errors = errors + error)
  def withErrors(extraErrors: Iterable[ProofError]): ProofCarrier[Nothing] =
    copy(errors = errors ++ extraErrors)

  def destruct(using file: sourcecode.File, line: sourcecode.Line): Nothing =
    throw new FatalCarrierDestructionException(this, file, line)

  def withJustification(using file: sourcecode.File, line: sourcecode.Line)(just: Thm): Nothing =
    throw new FatalCarrierDestructionException(this, file, line)

final case class SoftCarrier[+T](
    errors: Set[ProofError],
    statement: Sequent,
    justification: Option[Thm],
    payload: T
)(using lib: Library)
    extends ProofCarrier[T]:
  given K.Theory = lib.theory

  def isValid: Boolean = errors.isEmpty && justification.nonEmpty

  def hasJustification: Boolean = justification.nonEmpty

  def map[U](f: T => U): SoftCarrier[U] =
    copy(payload = f(payload))

  def flatMap[U](f: (T, Thm) => ProofCarrier[U]): ProofCarrier[U] =
    val next = f(payload, destruct._1)
    next.withErrors(errors)

  def withError(error: ProofError): SoftCarrier[T] =
    copy(errors = errors + error)

  def withErrors(extraErrors: Iterable[ProofError]): SoftCarrier[T] =
    copy(errors = errors ++ extraErrors)

  def withJustification(using file: sourcecode.File, line: sourcecode.Line)(just: Thm): SoftCarrier[T] =
    copy(justification = Some(just))

  def judgement: SoftCarrier[Unit] =
    copy(payload = ())

  private inline def asSorryK: K.Thm =
    K.sorry(using lib.theory)(statement.underlying)

  private inline def asSorry: Thm =
    Thm(statement, asSorryK)

  def destruct(using file: sourcecode.File, line: sourcecode.Line): (Thm, T) =
    (
      justification.getOrElse(asSorry),
      payload
    )
object ProofJudgement:
  def apply(using lib: Library)(just: Thm): ProofJudgement =
    ProofCarrier(Set.empty, just.statement, Some(just), ())

  def apply(using lib: Library)(just: K.Thm): ProofJudgement =
    ProofJudgement(Thm(just))

extension (kernelResult: Either[ProofError, K.Thm])(using lib: Library)
  /**
    * Lift a kernel result (with its error handled, see [[ProofError]]) into a
    * proof judgement/carrier with a known front statement.
    *
    * Checks that `intendedConclusion.underlying` is `==` to the kernel result.
    *
    * @throws IllegalArgumentException if the kernel result's statement does not
    * match the intended conclusion.
    */
  def lift(intendedConclusion: Sequent): ProofJudgement =
    kernelResult match
      case Left(err) =>
        ProofCarrier(Set(err), intendedConclusion, None, ())
      case Right(j) =>
        require(j.statement == intendedConclusion.underlying, s"Justification statement ${j.statement} does not match intended conclusion $intendedConclusion")
        ProofCarrier(Set.empty, intendedConclusion, Some(Thm(intendedConclusion, j)), ())
