package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.maths.SetTheory.Types.ADTv2.encoding.Utils.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.Pair.given
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.utils.prooflib.ProofTacticLib.Arity

private[encoding] trait SyntacticADTInduction[N <: Arity]
    extends SyntacticADTTerm[N] {
  this: SyntacticADT[N] =>

  private val Q = variable[Ind >>: Prop]

  // ************************
  // * STRUCTURAL INDUCTION *
  // ************************

  private[encoding] lazy val heightSuccessorStrong = Lemma(
    (hIsTheHeightFunction, in(n, N)) |- in(x, app(h, successor(n))) <=> isConstructor(
      x,
      app(h, n)
    )
  ) {
    have(thesis) by Sorry
  }

  lazy val inductiveCase: Map[SyntacticConstructor, Expr[Prop]] = constructors.map(c =>
    c -> c.signature.foldRight[Expr[Prop]](Q(c.term))((el, fc) =>
      val (v, ty) = el
      ty match
        case SelfRef => forall(v, in(v, term) ==> (Q(v) ==> fc))
        case RegularArg(tpe) => forall(v, in(v, typeExprToTerm(tpe)) ==> fc)
    )
  ).toMap

  lazy val induction = Lemma(using name=s"ADT_${name}_induction")(
    constructors.foldRight[Expr[Prop]](forall(x, in(x, term) ==> Q(x)))((c, f) =>
      inductiveCase(c) ==> f
    )
  ) {
    have(thesis) by Sorry
  }
}
