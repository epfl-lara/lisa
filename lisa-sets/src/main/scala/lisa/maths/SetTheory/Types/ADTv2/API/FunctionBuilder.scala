package lisa.maths.SetTheory.Types.ADTv2.API

import lisa.maths.SetTheory.Types.ADTv2.interface.{ADT, ADTFunction, RecFunction, SpecializedADT}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.{PatternSystem, SpecializedPatternSystem}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.syntax.CaseAccumulator
import lisa.maths.SetTheory.Types.ADTv2.functions.SemanticFunction
import lisa.maths.SetTheory.Types.ADTv2.recursion
import lisa.maths.SetTheory.Types.ADTv2.support.Time
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.substitutionsFromArgs

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.ProofTacticLib.Arity


def fun[N <: Arity](adt: SpecializedADT[N], returnType: Expr[Ind])(using
    name: sourcecode.Name,
    valueOfN: ValueOf[N]
)(
  cases: CaseAccumulator[N, Expr[Ind], Unit] ?=> Unit
): ADTFunction[N] = {
  val builder = CaseAccumulator[N, Expr[Ind], Unit](())
  cases(using builder)

  val effectiveTypeSubstitutions =
    substitutionsFromArgs("ADT", adt.base.name, adt.base.typeVariablesSeq, adt.typeArgs)
      .filter(substitution =>
        substitution._2.asInstanceOf[Expr[Ind]] != substitution._1.asInstanceOf[Variable[Ind]]
      )

  builder.compile(adt.base) match
    case Right(patternSystem) =>
      val specializedPatternSystem = SpecializedPatternSystem(
        underlying = patternSystem,
        domain = adt.base.semantic,
        typeSubstitutions = effectiveTypeSubstitutions,
        specializedAdtTerm = adt.term
      )
      val semantic = SemanticFunction[N](
        name.value,
        adt.base.semantic,
        specializedPatternSystem,
        returnType
      )
      new ADTFunction[N](semantic, adt.base)
    case Left(msg) => throw new IllegalArgumentException(msg)
}

/** Second version of REC ------------------------------------------------- */

def recFun[N <: Arity](adt: SpecializedADT[N], returnType: Expr[Ind])(using
    name: sourcecode.Name,
    valueOfN: ValueOf[N]
)(
    cases: Expr[Ind] => (CaseAccumulator[N, Expr[Ind], Unit] ?=> Unit)
): RecFunction[N] = {
  val builder = CaseAccumulator[N, Expr[Ind], Unit](())
  val self = RecFunction.selfPlaceholder(name.value)
  cases(self)(using builder)

  val effectiveTypeSubstitutions =
    substitutionsFromArgs("ADT", adt.base.name, adt.base.typeVariablesSeq, adt.typeArgs)
      .filter(substitution =>
        substitution._2.asInstanceOf[Expr[Ind]] != substitution._1.asInstanceOf[Variable[Ind]]
      )

  builder.compile(adt.base) match
    case Right(patternSystem) =>
      val specializedPatternSystem = SpecializedPatternSystem(
        underlying = patternSystem,
        domain = adt.base.semantic,
        typeSubstitutions = effectiveTypeSubstitutions,
        specializedAdtTerm = adt.term
      )
      val semantic = recursion.RecFunSemantics[N](
        name.value,
        adt.base.semantic,
        self,
        specializedPatternSystem,
        returnType
      )
      new RecFunction[N](semantic, adt.base)
    case Left(msg) => throw new IllegalArgumentException(msg)
}
