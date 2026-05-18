package lisa.maths.SetTheory.Types.ADTv2.API

import lisa.maths.SetTheory.Types.ADTv2.interface.{ADT, ADTFunction, Constructor, RecFunction}
import lisa.maths.SetTheory.Types.ADTv2.support.core.toSeq

import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.TypingHelpers.TypeAssign
import lisa.maths.SetTheory.Functions.Function.app

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

  // implicit def adtToTerm(adt: ADT[?]): Expr[Ind] =
  //   println(s"Converting ADT ${adt.name} to term") // Debug print
  //   asMonomorphicTerm("ADT", adt.name, adt.typeVariablesSeq.size)(adt.term)

  // implicit def constructorToTerm(c: Constructor[?]): Expr[Ind] =
  //   asMonomorphicTerm("Constructor", c.name, c.typeVariablesSeq.size)(c.term)

  // implicit def functionToTerm(f: ADTFunction[?]): Expr[Ind] =
  //   asMonomorphicTerm("Function", f.name, f.typeVariables.toSeq.size)(f.term)

  // implicit def recFunctionToTerm(f: RecFunction[?]): Expr[Ind] =
  //   asMonomorphicTerm("RecFunction", f.name, f.typeVariablesSeq.size)(f.term)

}
