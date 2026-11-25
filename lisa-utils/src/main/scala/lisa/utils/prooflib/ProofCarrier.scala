package lisa.utils.prooflib

import lisa.utils.K
import lisa.utils.fol.FOL.Sequent

/**
 * A successful theorem and payload, or an expected tactic failure.
 */
sealed trait ProofCarrier[+T]:
  import ProofCarrier.*

  /**
   * Whether this result contains a theorem and payload.
   */
  final def isValid: Boolean = this match
    case _: Success[?] => true
    case _: Failure => false

  /**
   * Transforms the payload on success, leaving failures untouched.
   */
  final def map[U](f: T => U): ProofCarrier[U] = this match
    case Success(theorem, payload) => Success(theorem, f(payload))
    case failure: Failure => failure

  /**
   * Continues on success, leaving failures and thrown exceptions untouched.
   */
  final def flatMap[U](f: (T, Thm) => ProofCarrier[U]): ProofCarrier[U] = this match
    case Success(theorem, payload) => f(payload, theorem)
    case failure: Failure => failure

  /**
   * Discards the payload while preserving the theorem or failure.
   */
  final def judgement: ProofJudgement = map(_ => ())

  /**
   * Extracts the theorem, throwing if the tactic failed.
   */
  final def thm(using file: sourcecode.File, line: sourcecode.Line): Thm = destruct._1

  /**
   * Extracts the kernel theorem, throwing if the tactic failed.
   */
  final def kernel(using file: sourcecode.File, line: sourcecode.Line): K.Thm = thm.kernel

  /**
   * Extracts the theorem and payload, throwing rather than admitting a failed result.
   */
  final def destruct(using file: sourcecode.File, line: sourcecode.Line): (Thm, T) = this match
    case Success(theorem, payload) => (theorem, payload)
    case Failure(message) => throw new TacticFailureException(message)

/**
 * Constructors for successful results and expected failures.
 */
object ProofCarrier:
  /**
   * A theorem accompanied by a computed value.
   */
  final case class Success[+T](theorem: Thm, payload: T) extends ProofCarrier[T]

  /**
   * An expected failure without a theorem, payload, captured stack or diagnostic.
   */
  final case class Failure(message: String) extends ProofCarrier[Nothing]

/**
 * A tactic result with no additional payload.
 */
type ProofJudgement = ProofCarrier[Unit]

/**
 * Constructs successful judgements from front or kernel theorems.
 */
object ProofJudgement:
  /**
   * Wraps a front theorem without changing its statement.
   */
  def apply(just: Thm): ProofJudgement = ProofCarrier.Success(just, ())

  /**
   * Lifts a kernel theorem into a successful judgement.
   */
  def apply(just: K.Thm): ProofJudgement = ProofJudgement(Thm(just))

extension (kernelResult: Either[ProofCarrier.Failure, K.Thm])
  /**
   * Lifts a kernel result, checking that a successful theorem has the intended statement.
   */
  def lift(intendedConclusion: Sequent): ProofJudgement = kernelResult match
    case Left(failure) => failure
    case Right(theorem) =>
      require(
        theorem.statement == intendedConclusion.underlying,
        s"Justification statement ${theorem.statement} does not match intended conclusion $intendedConclusion"
      )
      ProofJudgement(Thm(intendedConclusion, theorem))
