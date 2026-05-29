package lisa.maths.SetTheory.Types.ADTv2.API

import lisa.maths.SetTheory.Types.ADTv2.interface.{ADT, ADTFunction, RecFunction}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.syntax.CaseAccumulator
import lisa.maths.SetTheory.Types.ADTv2.functions.SemanticFunction
import lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.ProofTacticLib.Arity


def fun[N <: Arity](adt: ADT[N], returnType: Expr[Ind])(using
    name: sourcecode.Name,
    valueOfN: ValueOf[N]
)(
  cases: CaseAccumulator[N, Expr[Ind], Unit] ?=> Unit
): ADTFunction[N] = {
  val builder = CaseAccumulator[N, Expr[Ind], Unit](())
  cases(using builder)

  builder.isValid(adt) match
    case None =>
      val patternSystem: PatternSystem[N] = builder.buildPatternSystem
      val semantic = SemanticFunction[N](
        name.value,
        adt.semantic,
        patternSystem,
        returnType
      )
      new ADTFunction[N](semantic, adt)
    case Some(msg) => throw new IllegalArgumentException(msg)
}

/** Second version of REC ------------------------------------------------- */

def recFun[N <: Arity](adt: ADT[N], returnType: Expr[Ind])(using
    name: sourcecode.Name,
    valueOfN: ValueOf[N]
)(
    cases: Expr[Ind] => (CaseAccumulator[N, Expr[Ind], Unit] ?=> Unit)
): RecFunction[N] = {
  val builder = CaseAccumulator[N, Expr[Ind], Unit](())
  val self = RecFunction.selfPlaceholder(name.value)
  cases(self)(using builder)

  builder.isValid(adt) match
    case None =>
      val patternSystem: PatternSystem[N] = builder.buildPatternSystem
      val semantic = recursion.RecFunSemantics[N](
        name.value,
        adt.semantic,
        self,
        patternSystem,
        returnType
      )
      new RecFunction[N](semantic, adt)
    case Some(msg) => throw new IllegalArgumentException(msg)
}
