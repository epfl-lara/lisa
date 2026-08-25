package lisa.utils.kernel

import lisa.kernel.proof as K
import lisa.kernel.proof.{Sequent, Thm}
import lisa.utils.collection.Extensions.mapLeft

sealed trait CheckError extends Exception
case object EmptyProofError extends CheckError
case class ForwardReferenceError(idx: Int) extends CheckError
case class InvalidImportError(idx: Int) extends CheckError
case class InvalidStepError(idx: Int, error: K.ProofError) extends CheckError

case class LinearProof(
  steps: Array[ProofStep],
  imports: Array[Sequent]
):
  def importThms(using theory: K.Theory): Array[K.Thm] = imports.map { statement =>
    K.Assume(statement) match
      case Right(thm) => thm
  }

  def check(using theory: K.Theory = K.Theory.empty): Either[CheckError, Thm] =
    if steps.isEmpty then
      Left(EmptyProofError)
    else
      var idx = 0
      val checked = new Array[Thm](steps.length)

      while idx < steps.length do
        checkOne(steps(idx), idx, checked, importThms) match
          case Left(error) => return Left(error)
          case Right(thm) => checked(idx) = thm

        idx += 1

      Right(checked.last)

  extension (idx: Int) private def asImport: Int = -idx - 1

  private def checkOne(
    step: ProofStep,
    idx: Int,
    checked: Array[Thm],
    imports: Array[K.Thm]
  )(using theory: K.Theory): Either[CheckError, Thm] =
    val fwdRef = step.premises.find(p => p >= idx)
    val invalidImport = step.premises.find(p => p < 0 && p.asImport >= imports.length)

    if fwdRef.isDefined then
      Left(ForwardReferenceError(fwdRef.get))
    else if invalidImport.isDefined then
      Left(InvalidImportError(invalidImport.get))
    else
      def resolve(premise: Int): Thm =
        if premise >= 0 then checked(premise)
        else imports(premise.asImport)

      def checkedResult[E <: K.ProofError](result: Either[E, Thm]): Either[CheckError, Thm] =
        result.mapLeft(InvalidStepError(idx, _))

      def checkedResultWithStatement[E <: K.ProofError](statement: Sequent, result: Either[E, Thm]): Either[CheckError, Thm] =
        checkedResult(result.flatMap(thm => K.Restate(statement, thm).map(_ => thm)))

      step match
        case Sorry(statement) =>
          checkedResult(K.Sorry(statement))
        case Axiom(statement) =>
          checkedResult(K.Axiom(statement))
        case Assume(statement) =>
          checkedResult(K.Assume(statement))
        case Discharge(statement, premise, justification) =>
          checkedResultWithStatement(statement, K.Discharge(resolve(premise), resolve(justification)))
        case Definition(statement, cst, vars, exp) =>
          checkedResultWithStatement(statement, K.Definition(cst, vars, exp))
        case Restate(statement, premise) =>
          checkedResult(K.Restate(statement, resolve(premise)))
        case RestateTrue(statement) =>
          checkedResult(K.RestateTrue(statement))
        case Hypothesis(statement, phi) =>
          checkedResult(K.Hypothesis(statement, phi))
        case Cut(statement, premise1, premise2, phi) =>
          checkedResult(K.Cut(statement, resolve(premise1), resolve(premise2), phi))
        case LeftAnd(statement, premise, phi, psi) =>
          checkedResult(K.LeftAnd(statement, resolve(premise), phi, psi))
        case LeftOr(statement, premises, disjuncts) =>
          checkedResult(K.LeftOr(statement, premises.iterator.map(resolve).toSeq, disjuncts))
        case LeftImplies(statement, premise1, premise2, phi, psi) =>
          checkedResult(K.LeftImplies(statement, resolve(premise1), resolve(premise2), phi, psi))
        case LeftIff(statement, premise, phi, psi) =>
          checkedResult(K.LeftIff(statement, resolve(premise), phi, psi))
        case LeftNot(statement, premise, phi) =>
          checkedResult(K.LeftNot(statement, resolve(premise), phi))
        case LeftForall(statement, premise, phi, x, t) =>
          checkedResult(K.LeftForall(statement, resolve(premise), phi, x, t))
        case LeftExists(statement, premise, phi, x) =>
          checkedResult(K.LeftExists(statement, resolve(premise), phi, x))
        case RightAnd(statement, premises, conjuncts) =>
          checkedResult(K.RightAnd(statement, premises.iterator.map(resolve).toSeq, conjuncts))
        case RightOr(statement, premise, phi, psi) =>
          checkedResult(K.RightOr(statement, resolve(premise), phi, psi))
        case RightImplies(statement, premise, phi, psi) =>
          checkedResult(K.RightImplies(statement, resolve(premise), phi, psi))
        case RightIff(statement, premise1, premise2, phi, psi) =>
          checkedResult(K.RightIff(statement, resolve(premise1), resolve(premise2), phi, psi))
        case RightNot(statement, premise, phi) =>
          checkedResult(K.RightNot(statement, resolve(premise), phi))
        case RightForall(statement, premise, phi, x) =>
          checkedResult(K.RightForall(statement, resolve(premise), phi, x))
        case RightExists(statement, premise, phi, x, t) =>
          checkedResult(K.RightExists(statement, resolve(premise), phi, x, t))
        case RightEpsilon(statement, premise, phi, x, t) =>
          checkedResult(K.RightEpsilon(statement, resolve(premise), phi, x, t))
        case Weakening(statement, premise) =>
          checkedResult(K.Weakening(statement, resolve(premise)))
        case LeftRefl(statement, premise, phi) =>
          checkedResult(K.LeftRefl(statement, resolve(premise), phi))
        case RightRefl(statement, phi) =>
          checkedResult(K.RightRefl(statement, phi))
        case LeftSubstEq(statement, premise, equals, lambdaPhi) =>
          checkedResult(K.LeftSubstEq(statement, resolve(premise), equals, lambdaPhi))
        case RightSubstEq(statement, premise, equals, lambdaPhi) =>
          checkedResult(K.RightSubstEq(statement, resolve(premise), equals, lambdaPhi))
        case InstSchema(statement, premise, subst) =>
          checkedResult(K.InstSchema(statement, resolve(premise), subst))
