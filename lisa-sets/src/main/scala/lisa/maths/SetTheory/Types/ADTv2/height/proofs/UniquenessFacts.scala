package lisa.maths.SetTheory.Types.ADTv2.height.proofs

import lisa.maths.SetTheory.Base.Extensionality
import lisa.maths.SetTheory.Functions.BasicTheorems.extensionality
import lisa.maths.SetTheory.Functions.BasicTheorems.functionOnIffFunctionWithDomain
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Ordinals.Integer.omegaSuccessorInduction
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._

private[height] object UniquenessFacts {

  protected inline final def app(f: Expr[Ind], x: Expr[Ind]): Expr[Ind] =
    lisa.maths.SetTheory.Functions.Predef.app(f)(x)

  private def stageEq(k: Expr[Ind]): Expr[Prop] = app(f, k) === app(g, k)
  private val stageEqN = stageEq(n)
  private val stageEqSuccN = stageEq(S(n))

  private val zeroCase = Lemma(
    (CoreFacts.introFunctionMono, CoreFacts.isHeightCore(f), CoreFacts.isHeightCore(g)) |- stageEq(∅)
  ) {
    val fZero = have(
      (CoreFacts.introFunctionMono, CoreFacts.isHeightCore(f), CoreFacts.isHeightCore(g)) |- !in(x, app(f, ∅))
    ) by Tautology.from(SuccessorFacts.heightZero.of(h := f))
    val gZero = have(
      (CoreFacts.introFunctionMono, CoreFacts.isHeightCore(f), CoreFacts.isHeightCore(g)) |- !in(x, app(g, ∅))
    ) by Tautology.from(SuccessorFacts.heightZero.of(h := g))
    have(
      (CoreFacts.introFunctionMono, CoreFacts.isHeightCore(f), CoreFacts.isHeightCore(g)) |- in(x, app(f, ∅)) <=> in(x, app(g, ∅))
    ) by Tautology.from(fZero, gZero)
    thenHave(thesis) by Extensionality
  }

  private val succCase = Lemma(
    (CoreFacts.introFunctionMono, CoreFacts.isHeightCore(f), CoreFacts.isHeightCore(g), in(n, N), stageEqN) |- stageEqSuccN
  ) {
    val fSucc = have(
      (CoreFacts.introFunctionMono, CoreFacts.isHeightCore(f), CoreFacts.isHeightCore(g), in(n, N), stageEqN) |-
        in(x, app(f, S(n))) <=> CoreFacts.inIntroImage(app(f, n))(x)
    ) by Tautology.from(SuccessorFacts.heightSuccessorWeak.of(h := f))
    val gSucc = have(
      (CoreFacts.introFunctionMono, CoreFacts.isHeightCore(f), CoreFacts.isHeightCore(g), in(n, N), stageEqN) |-
        in(x, app(g, S(n))) <=> CoreFacts.inIntroImage(app(g, n))(x)
    ) by Tautology.from(SuccessorFacts.heightSuccessorWeak.of(h := g))

    have(
      (CoreFacts.introFunctionMono, CoreFacts.isHeightCore(f), CoreFacts.isHeightCore(g), in(n, N), stageEqN) |-
        CoreFacts.inIntroImage(app(f, n))(x) <=> CoreFacts.inIntroImage(app(g, n))(x)
    ) by Congruence

    have(
      (CoreFacts.introFunctionMono, CoreFacts.isHeightCore(f), CoreFacts.isHeightCore(g), in(n, N), stageEqN) |-
        in(x, app(f, S(n))) <=> in(x, app(g, S(n)))
    ) by Tautology.from(fSucc, gSucc, lastStep)
    thenHave(thesis) by Extensionality
  }

  val uniqueness = Lemma(
    (CoreFacts.introFunctionMono, CoreFacts.isHeightCore(f), CoreFacts.isHeightCore(g)) |- f === g
  ) {

    val induction = have(
      (
        CoreFacts.introFunctionMono,
        CoreFacts.isHeightCore(f),
        CoreFacts.isHeightCore(g),
        ∀(n, in(n, N) ==> (stageEqN ==> stageEqSuccN))
      ) |- ∀(n, in(n, N) ==> stageEqN)
    ) by Tautology.from(zeroCase, omegaSuccessorInduction of (P := lam(n, stageEqN)))

    have(
      (CoreFacts.introFunctionMono, CoreFacts.isHeightCore(f), CoreFacts.isHeightCore(g), in(n, N)) |- stageEqN ==> stageEqSuccN
    ) by RightImplies(succCase)
    thenHave(
      (CoreFacts.introFunctionMono, CoreFacts.isHeightCore(f), CoreFacts.isHeightCore(g)) |- in(n, N) ==> (stageEqN ==> stageEqSuccN)
    ) by RightImplies
    val stepForall = thenHave(
      (CoreFacts.introFunctionMono, CoreFacts.isHeightCore(f), CoreFacts.isHeightCore(g)) |- ∀(n, in(n, N) ==> (stageEqN ==> stageEqSuccN))
    ) by RightForall

    val stagesEqual = have(
      (CoreFacts.introFunctionMono, CoreFacts.isHeightCore(f), CoreFacts.isHeightCore(g)) |- ∀(n, in(n, N) ==> stageEqN)
    ) by Cut(stepForall, induction)

    val fOnN = have(
      (CoreFacts.introFunctionMono, CoreFacts.isHeightCore(f), CoreFacts.isHeightCore(g)) |- functionOn(f)(N)
    ) by Tautology.from(
      functionOnIffFunctionWithDomain of (f := f, A := N)
    )
    val gOnN = have(
      (CoreFacts.introFunctionMono, CoreFacts.isHeightCore(f), CoreFacts.isHeightCore(g)) |- functionOn(g)(N)
    ) by Tautology.from(
      functionOnIffFunctionWithDomain of (f := g, A := N)
    )

    have(thesis) by Tautology.from(
      fOnN,
      gOnN,
      stagesEqual,
      extensionality of (f := f, g := g, A := N)
    )
  }

  def uniquenessAt(
      isConstructor0: Expr[Ind >>: Ind >>: Prop],
      f0: Expr[Ind],
      g0: Expr[Ind]
  )(using proof: lisa.SetTheoryLibrary.Proof): proof.Fact =
    uniqueness.of(CoreFacts.isConstructor := isConstructor0, f := f0, g := g0)

  def initialize(): Unit = {
    val _ = zeroCase
    val _ = succCase
    val _ = uniqueness
  }
}
