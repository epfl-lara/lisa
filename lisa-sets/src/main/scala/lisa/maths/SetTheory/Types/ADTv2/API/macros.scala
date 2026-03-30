package lisa.maths.SetTheory.Types.ADTv2.API

import lisa.maths.SetTheory.Types.ADTv2.encoding.ADT

import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.maths.SetTheory.Types.TypingHelpers.{TypeAssign}
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.Function.app

private val T = variable[Ind]

extension [T <: Expr[Ind], N <: Arity](t: T) {
    infix def ::(adt: ADT[N]) = TypeAssign[T](t, adt())
    infix def ::(e: Expr[Ind]) = TypeAssign[T](t, e) 
}

extension (f: Expr[Ind]) {
    infix def *(arg: Expr[Ind]): Expr[Ind] = app(f)(arg)
}