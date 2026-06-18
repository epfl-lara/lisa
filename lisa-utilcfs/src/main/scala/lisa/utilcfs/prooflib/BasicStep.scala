package lisa.utilcfs.prooflib

import lisa.kernelcf.{proof => K}
import lisa.utilcfs.fol.FOL.*
import lisa.utilcfs.collection.Extensions.{*, given}
import lisa.utilcfs.prooflib.Helpers.*

object BasicStep:

  case class FrontKernelMismatch(reason: String) extends Exception:
    def msg = s"[FATAL] Front-end and kernel mismatch: $reason"

  case object UnreachableErrorException extends Exception:
    def msg = "[FATAL] This error path should be unreachable."

  private def withParams(base: String, params: (String, Any)*): String =
    if params.isEmpty then base
    else 
      val paramStr = params.map((k, v) => s"\t$k: $v").mkString("\n")
      s"$base\n$paramStr"

  private def theoryMismatch(file: sourcecode.File, line: sourcecode.Line)(step: String, expected: K.Theory, actual: K.Theory): ProofError =
    SoftError(withParams(s"In step $step, premises and conclusion had mismatched underlying theories.", "Expected" -> expected, "Actual" -> actual), file, line)

  object Sorry:
    private def liftError(err: K.Sorry.ErrorType): ProofError = 
      summon[K.Sorry.ErrorType =:= Nothing]
      err

    def apply(using library: Library, proof: Proof)(conclusion: Sequent): ProofJudgement =
      val underlying = conclusion.underlying
      K.Sorry(using library.theory)(underlying)
        .mapLeft(liftError)
        .lift(underlying)

  object Axiom:
    private def liftError(err: K.Axiom.ErrorType): ProofError = 
      summon[K.Axiom.ErrorType =:= Nothing]
      err

    def apply(using library: Library, proof: Proof)(conclusion: Sequent): ProofJudgement =
      val underlying = conclusion.underlying
      K.Axiom(using library.theory)(underlying)
        .mapLeft(liftError)
        .lift(underlying)

  object Hypothesis:
    private def liftError(file: sourcecode.File, line: sourcecode.Line)(conclusion: Sequent, pivot: Expr[Prop])(err: K.Hypothesis.ErrorType): ProofError = 
      err match
        // step-specific errors
        case _: K.Hypothesis.MissingFromLeft =>
          assert(!conclusion.left.containsEq(pivot), s"Pivot $pivot is in the left side of the conclusion $conclusion, despite the kernel reporting it as missing.")
          val base = s"Hypothesis pivot is missing from the left side of the conclusion"
          SoftError(withParams(base, "Pivot" -> pivot, "Conclusion" -> conclusion), file, line)
        case _: K.Hypothesis.MissingFromRight =>
          assert(!conclusion.right.containsEq(pivot), s"Pivot $pivot is in the right side of the conclusion $conclusion, despite the kernel reporting it as missing.")
          val base = s"Hypothesis pivot is missing from the right side of the conclusion"
          SoftError(withParams(base, "Pivot" -> pivot, "Conclusion" -> conclusion), file, line)
        // general errors
        case _: K.SortMismatch =>
          // should only happen if the pivot is not a prop, which is ensured by
          // the front type system
          throw FrontKernelMismatch("Expr[Prop] pivot is not a kernel Prop")
        case _: K.TheoryMismatch =>
          // Hyp has no premises
          throw UnreachableErrorException

    def withParameters(using file: sourcecode.File, line: sourcecode.Line)(using library: Library, proof: Proof)(pivot: Expr[Prop])(conclusion: Sequent): ProofJudgement =
      K.Hypothesis(using library.theory)(conclusion.underlying, pivot.underlying)
        .mapLeft(liftError(file, line)(conclusion, pivot))
        .lift(conclusion.underlying)
        
    def apply(using library: Library, proof: Proof)(conclusion: Sequent): ProofJudgement =
      ???
