package lisa.maths.SetTheory.Types.ADTv2.API

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.syntax.CaseAccumulator
import lisa.maths.SetTheory.Types.ADTv2.functions.SemanticFunction
import lisa.maths.SetTheory.Types.ADTv2.interface.ADTFunction
import lisa.maths.SetTheory.Types.ADTv2.interface.RecFunction
import lisa.maths.SetTheory.Types.ADTv2.interface.SpecializedADT
import lisa.maths.SetTheory.Types.ADTv2.recursion
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.substitutionsFromArgs

def fun[S: Sort](adt: SpecializedADT[S], returnType: Expr[Ind])(using
    name: sourcecode.Name
)(
    cases: CaseAccumulator[Expr[Ind], Unit] ?=> Unit
): ADTFunction[S] = {
  val builder = CaseAccumulator[Expr[Ind], Unit](())
  cases(using builder)

  builder.compile(adt) match
    case Right(patternSystem) =>
      val semantic = SemanticFunction(
        name.value,
        adt.base.semantic,
        adt.term,
        patternSystem,
        returnType
      )
      new ADTFunction[S](semantic, adt.base)
    case Left(msg) => throw new IllegalArgumentException(msg)
}

def recFun[S: Sort](adt: SpecializedADT[S], returnType: Expr[Ind])(using
    name: sourcecode.Name
)(
    cases: Expr[Ind] => (CaseAccumulator[Expr[Ind], Unit] ?=> Unit)
): RecFunction[S] = {
  val builder = CaseAccumulator[Expr[Ind], Unit](())
  val self = RecFunction.selfPlaceholder(name.value)
  cases(self)(using builder)

  val effectiveTypeSubstitutions =
    substitutionsFromArgs("ADT", adt.base.name, adt.base.typeVariablesSeq, adt.typeArgs)
      .filter(substitution => substitution._2.asInstanceOf[Expr[Ind]] != substitution._1.asInstanceOf[Variable[Ind]])

  builder.compile(adt) match
    case Right(patternSystem) =>
      val semantic = (
        recursion.SemanticFunction(
          name.value,
          adt.base.semantic,
          adt.term,
          effectiveTypeSubstitutions,
          self,
          patternSystem,
          returnType
        )
      )
      new RecFunction[S](semantic, adt.base)
    case Left(msg) => throw new IllegalArgumentException(msg)
}
