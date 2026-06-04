package lisa.maths.SetTheory.Types.ADTv2.height

import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.SimpleDeducedSteps.*
import lisa.maths.SetTheory.Types.ADTv2.height.proofs.{CoreFacts, SuccessorFacts}

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

  def isHeight(h: Expr[Ind]): Expr[Prop] = isHeightCore(h)

  /** Unfold isHeight(h). */
  def unfoldIsHeight(using
      lib: lisa.utils.prooflib.Library,
      proof: lib.Proof
  ): proof.Fact = {
    lib.have(isHeight(h) |- isHeightCore(h)) by
      Restate
  }

  private[ADTv2] val heightIsCore = Lemma(isHeight(h) |- isHeightCore(h)) {
    have(thesis) by Restate.from(unfoldIsHeight)
  }

  /**
   *  Lemma --- The height function is not empty.
   *
   *  `height ≠ ∅`
   */
  val heightFunctionNonEmpty = Lemma(isHeight(h) |- !(h === ∅)) {
    have(thesis) by Tautology.from(heightIsCore, CoreFacts.domNImpliesNonEmptyAt(h))
  }

  /**
   *  Lemma --- The set of elements of height n or below is the image of the extended
   *  introduction function under the height function restricted to n.
   *
   *  `height(n) = extendedIntroductionFunction(height | n)`
   */
  val heightApplication = Lemma(
    (isHeight(h), in(n, N)) |-
      in(x, app(h, n)) <=>
      inExtIntroImage(h ↾ n)(x)
  ) {
    have(thesis) by Tautology.from(
      heightIsCore,
      CoreFacts.heightApplicationAt(isConstructor, h, n, x)
    )
  }

  /**
   *  Lemma --- There is no element of height 0 in the ADT.
   *
   *  `!∃x ∈ adt. height(x) = 0`
   */
  val heightZero = Lemma(isHeight(h) |- !in(x, app(h, ∅))) {
    have(thesis) by Tautology.from(
      heightIsCore,
      SuccessorFacts.heightZeroAt(isConstructor, h, x)
    )
  }
}
