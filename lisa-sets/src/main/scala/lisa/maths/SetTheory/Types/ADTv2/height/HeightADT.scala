package lisa.maths.SetTheory.Types.ADTv2.height

import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.height.proofs.SuccessorFacts
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.semantics.DefinedProperty
import lisa.utils.prooflib.ProofTacticLib.Arity

final class HeightADT[N <: Arity](
    name: String,
    typeVariablesSeq: Seq[Variable[Ind]],
    isConstructor: Expr[Ind >>: Ind >>: Prop]
) {

  protected inline final def app(f: Expr[Ind], x: Expr[Ind]): Expr[Ind] =
    lisa.maths.SetTheory.Functions.Predef.app(f)(x)

  def inIntroImage(s: Expr[Ind])(y: Expr[Ind]): Expr[Prop] =
    isConstructor(y)(s) \/ in(y, s)

  def inExtIntroImage(f: Expr[Ind])(x: Expr[Ind]): Expr[Prop] =
    (f =/= ∅) /\ inIntroImage(unionRange(f))(x)

  def isHeightCore(h: Expr[Ind]): Expr[Prop] =
    function(h) /\
      (dom(h) === N) /\
      ∀(n ∈ N, ∀(x, in(x, app(h, n)) <=> inExtIntroImage(h ↾ n)(x)))

  // `isHeight` is an *opaque* defined predicate `${name}/isHeight[typeVars](h)` whose
  // definition unfolds to `isHeightCore(h)`. Keeping it opaque stops tactics (Tautology)
  // and the kernel checker from decomposing the ~400-char `isHeightCore` conjunction
  private val isHeightSym = DefinedProperty(
    s"$name/isHeight",
    typeVariablesSeq,
    h,
    isHeightCore
  )

  def isHeight(h: Expr[Ind]): Expr[Prop] = isHeightSym.term #@ h

  /**
   * Unfold `isHeight(h)` to its core conjunction.
   */
  private[ADTv2] val heightIsCore = isHeightSym.unfold

  /**
   * Fold the core conjunction back into the opaque `isHeight(h)`.
   */
  private[ADTv2] val coreIsHeight = isHeightSym.fold

  /**
   *  Lemma --- There is no element of height 0 in the ADT.
   *
   *  `!∃x ∈ adt. height(x) = 0`
   */
  val heightZero = Lemma(isHeight(h) |- !in(x, app(h, ∅))) {
    have(thesis) by Cut(
      heightIsCore,
      SuccessorFacts.heightZeroAt(isConstructor, h, x)
    )
  }
}
