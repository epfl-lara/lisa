package lisa.maths.SetTheory.Types.ADTv2.height

import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.SimpleDeducedSteps.*

final class HeightADT[N <: Arity](
  name: String,
  typeVariablesSeq: Seq[Variable[Ind]],
  isConstructor: Expr[Ind >>: Ind >>: Prop]
) {

  protected inline final def app(f: Expr[Ind], x: Expr[Ind]): Expr[Ind] =
    lisa.maths.SetTheory.Functions.Predef.app(f)(x)

  val arityTheory = new HeightArity[N]()

  def inIntroImage(s: Expr[Ind])(y: Expr[Ind]): Expr[Prop] =
    isConstructor(y)(s) \/ in(y, s)

  def inExtIntroImage(f: Expr[Ind])(x: Expr[Ind]): Expr[Prop] =
    (f =/= ∅) /\ inIntroImage(unionRange(f))(x)

  def isHeightCore(h: Expr[Ind]): Expr[Prop] =
    function(h) /\
      (dom(h) === N) /\
      ∀(n ∈ N, ∀(x, in(x, app(h, n)) <=> inExtIntroImage(h ↾ n)(x)))

  lazy val isHeight =
    DEF(using name = s"${name}/height")(
      λ(h, forallSeq(typeVariablesSeq, isHeightCore(h)))
    )

  /** Unfold isHeight(h) and instantiate all quantified type variables. */
  def unfoldIsHeight(using
      lib: lisa.utils.prooflib.Library,
      proof: lib.Proof
  ): proof.Fact = {
    val coreAll = forallSeq(typeVariablesSeq, isHeightCore(h))
    val withAllTypes = lib.have(isHeight(h) |- coreAll) by
      Tautology.from(isHeight.definition)
    lib.have(isHeight(h) |- isHeightCore(h)) by
      InstantiateForall(typeVariablesSeq*)(withAllTypes)
  }

  private[ADTv2] val heightIsCore = Lemma(isHeight(h) |- isHeightCore(h)) {
    have(thesis) by Restate.from(unfoldIsHeight)
  }

  /**
   *  Lemma --- There exists a unique height function for this ADT.
   *
   *  `∃!h. h = height`
   *
   *  TODO: Prove this using transfinite recursion
   */
  val heightFunUnique = Axiom(existsOne(h, isHeight(h)))

  /**
   *  Lemma --- The height function exists.
   *
   *  `∃h. h = height`
   */
  val heightExists = Lemma(exists(h, isHeight(h))) {
    have(thesis) by Cut(
      heightFunUnique.asInstanceOf,
      lisa.maths.Quantifiers.existsOneImpliesExists of
        (P := lam(h, isHeight(h)))
    )
  }

  /**
   *  Lemma --- If two functions are the height function then they are the same.
   *
   *  `f = height /\ h = height => f = h`
   */
  val heightFunUniqueEq = Lemma((isHeight(f), isHeight(h)) |- f === h) {
    have(thesis) by Cut(
      heightFunUnique,
      existsOneUniqueness of (P := lam(h, isHeight(h)), x := f, y := h)
    )
  }

  /**
   *  Lemma --- The height function is not empty.
   *
   *  `height ≠ ∅`
   */
  val heightFunctionNonEmpty = Lemma(isHeight(h) |- !(h === ∅)) {
    have(thesis) by Tautology.from(heightIsCore, HeightKernel.domNImpliesNonEmpty)
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
      HeightKernel.heightApplication of (HeightKernel.isConstructor := isConstructor)
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
      HeightKernel.heightZero of (HeightKernel.isConstructor := isConstructor)
    )
  }
}
