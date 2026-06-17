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

  def isValid: Boolean = errors.isEmpty && justification.nonEmpty
  def hasJustification: Boolean = justification.nonEmpty

  def map[U](f: T => U): ProofCarrier[U] =
    copy(payload = f(payload))

  def flatMap[U](f: (T, Thm) => ProofCarrier[U]): ProofCarrier[U] =
    val just = justification.getOrElse:
      K.Sorry(statement) match
        case Right(j) => j
    val next = f(payload, just)
    next.copy(errors = errors ++ next.errors)

  def withError(error: ProofError): ProofCarrier[T] =
    copy(errors = errors + error)

  def withErrors(extraErrors: Iterable[ProofError]): ProofCarrier[T] =
    copy(errors = errors ++ extraErrors)

  def judgement: ProofJudgement =
    copy(payload = ())

type ProofJudgement = ProofCarrier[Unit]

extension (kernelResult: Either[ProofError, Thm])(using lib: Library)
  def lift(intendedConclusion: Sequent): ProofJudgement =
    kernelResult match
      case Left(err) => 
        ProofCarrier(Set(err), intendedConclusion, None, ())
      case Right(j) => 
        assert(j.statement == intendedConclusion, s"Justification statement ${j.statement} does not match intended conclusion $intendedConclusion")
        ProofCarrier(Set.empty, intendedConclusion, Some(j), ())
