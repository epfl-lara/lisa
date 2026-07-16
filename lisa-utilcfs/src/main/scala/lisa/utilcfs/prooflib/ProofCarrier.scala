package lisa.utilcfs.prooflib

import lisa.utilcfs.K

import lisa.utilcfs.fol.FOL.Sequent

trait ProofCarrierException extends Exception
case class FatalCarrierDestructionException(carrier: FatalCarrier, file: sourcecode.File, line: sourcecode.Line) extends Exception(s"Attempted recovery of a fatal error state.") with ProofCarrierException

trait ProofCarrier[+T]:
  val errors: Set[ProofError]

  def justification: Option[Thm]

  def isValid: Boolean

  def hasJustification: Boolean

  def map[U](f: T => U): ProofCarrier[U]

  def flatMap[U](f: (T, Thm) => ProofCarrier[U]): ProofCarrier[U]

  def withError(error: ProofError): ProofCarrier[T]

  def withErrors(extraErrors: Iterable[ProofError]): ProofCarrier[T]

  def withJustification(using file: sourcecode.File, line: sourcecode.Line)(just: Thm): ProofCarrier[T]

  def judgement: ProofJudgement

  def destruct(using file: sourcecode.File, line: sourcecode.Line): (Thm, T)

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

  def destruct(using file: sourcecode.File, line: sourcecode.Line): Nothing =
    throw new FatalCarrierDestructionException(this, file, line)
  def flatMap[U](f: (Nothing, Thm) => ProofCarrier[U]): this.type = this
  def hasJustification: Boolean = false
  def isValid: Boolean = false
  def judgement: ProofJudgement = this
  def map[U](f: Nothing => U): this.type = this
  def withError(error: ProofError): ProofCarrier[Nothing] =
    copy(errors = errors + error)
  def withErrors(extraErrors: Iterable[ProofError]): ProofCarrier[Nothing] =
    copy(errors = errors ++ extraErrors)

  def withJustification(using file: sourcecode.File, line: sourcecode.Line)(just: Thm): Nothing =
    throw new FatalCarrierDestructionException(this, file, line)


final case class SoftCarrier[+T](
    errors: Set[ProofError],
    statement: Sequent,
    justification: Option[Thm],
    payload: T
)(using lib: Library) extends ProofCarrier[T]:
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
  def map[U](f: T => U): SoftCarrier[U] =
    copy(payload = f(payload))

  /**
    * This carrier with the payload and justification transformed by the given
    * function.
    */
  def flatMap[U](f: (T, Thm) => ProofCarrier[U]): ProofCarrier[U] =
    val next = f(payload, destruct._1)
    next.withErrors(errors)

  /**
    * This carrier with an additional error.
    */
  def withError(error: ProofError): SoftCarrier[T] =
    copy(errors = errors + error)

  /**
    * This carrier with additional appended errors.
    */
  def withErrors(extraErrors: Iterable[ProofError]): SoftCarrier[T] =
    copy(errors = errors ++ extraErrors)

  /**
    * This carrier with an overriden justification. Used to add a step while
    * preserving values and errors.
    *
    * Use [[flatMap]] to additionally transform the existing justification
    * and/or payload.
    */
  def withJustification(using file: sourcecode.File, line: sourcecode.Line)(just: Thm): SoftCarrier[T] =
    copy(justification = Some(just))

  /**
    * This carrier with the payload discarded.
    */
  def judgement: SoftCarrier[Unit] =
    copy(payload = ())

  private def asSorry: K.Thm =
    K.sorry(using lib.theory)(statement.underlying)

  /**
    * The carrier's theorem and payload, using a sorry theorem when no
    * justification was produced.
    */
  def destruct(using file: sourcecode.File, line: sourcecode.Line): (Thm, T) =
    (
      justification.getOrElse(Thm(statement, asSorry)),
      payload
    )
object ProofJudgement:
  def apply(using lib: Library)(just: Thm): ProofJudgement =
    ProofCarrier(Set.empty, just.statement, Some(just), ())

  def apply(using lib: Library)(just: K.Thm): ProofJudgement =
    ProofJudgement(Thm(just))

extension (kernelResult: Either[ProofError, K.Thm])(using lib: Library)
  def lift(intendedConclusion: Sequent): ProofJudgement =
    kernelResult match
      case Left(err) => 
        ProofCarrier(Set(err), intendedConclusion, None, ())
      case Right(j) => 
        assert(j.statement == intendedConclusion.underlying, s"Justification statement ${j.statement} does not match intended conclusion $intendedConclusion")
        ProofCarrier(Set.empty, intendedConclusion, Some(Thm(intendedConclusion, j)), ())
