package lisa.maths.SetTheory.Types.ADTv2.API

import lisa.maths.SetTheory.Types.ADTv2.interface.{ADT, Constructor, RecFunction}
import lisa.maths.SetTheory.Types.ADTv2.functions.ADTFunction
import lisa.maths.SetTheory.Types.ADTv2.support.toSeq

import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.TypingHelpers.TypeAssign
import lisa.maths.SetTheory.Functions.Function.app

private val T = variable[Ind]

extension [T <: Expr[Ind], N <: Arity](t: T) {
  infix def ::(adt: ADT[N]) = TypeAssign[T](t, adt.term)
  infix def ::(e: Expr[Ind]) = TypeAssign[T](t, e)
}

extension (f: Expr[Ind]) {
  infix def *(arg: Expr[Ind]): Expr[Ind] = app(f)(arg)
}

object Implicits {

  private def asMonomorphicTerm(kind: String, name: String, typeArgCount: Int)(
      term: => Expr[Ind]
  ): Expr[Ind] =
    require(
      typeArgCount == 0,
      s"$kind $name is polymorphic and needs $typeArgCount type argument(s)."
    )
    term

  implicit def adtToTerm(adt: ADT[?]): Expr[Ind] =
    asMonomorphicTerm("ADT", adt.name, adt.remainingTypeVariables.size)(adt.term)

  implicit def constructorToTerm(c: Constructor[?]): Expr[Ind] =
    asMonomorphicTerm("Constructor", c.name, c.remainingTypeVariables.size)(c.term)

  implicit def functionToTerm(f: ADTFunction[?]): Expr[Ind] =
    asMonomorphicTerm("Function", f.name, f.typeVariables.toSeq.size)(f.term)

  implicit def recFunctionToTerm(f: RecFunction[?]): Expr[Ind] =
    asMonomorphicTerm("RecFunction", f.name, f.remainingTypeVariables.size)(f.term)

}
