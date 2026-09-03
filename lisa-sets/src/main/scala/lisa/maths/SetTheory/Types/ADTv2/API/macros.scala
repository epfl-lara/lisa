package lisa.maths.SetTheory.Types.ADTv2.API

import lisa.maths.SetTheory.Functions.Function.app
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.TypingHelpers.TypeAssign
import lisa.utils.prooflib.ProofTacticLib.Arity

private val T = variable[Ind]

extension [T <: Expr[Ind], N <: Arity](t: T) {
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

}
