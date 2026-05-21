package lisa.maths.SetTheory.Types.ADTv2.height

import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.Extensionality
import lisa.maths.SetTheory.Functions.BasicTheorems.{extensionality, functionOnIffFunctionWithDomain}
import lisa.maths.SetTheory.Functions.Predef.*

/**
 * Generic uniqueness of a height-core function.
 *
 * This part of the argument is independent of the concrete constructor
 * family: once two functions satisfy the same recursive characterization on
 * `ω`, they agree stage by stage by induction on naturals, hence are equal as
 * functions on `ω`.
 */
object HeightKernelUniqueness {

  protected inline final def app(f: Expr[Ind], x: Expr[Ind]): Expr[Ind] =
    lisa.maths.SetTheory.Functions.Predef.app(f)(x)

  private def stageEq(k: Expr[Ind]): Expr[Prop] = app(f, k) === app(g, k)
  private val stageEqN = stageEq(n)
  private val stageEqSuccN = stageEq(successor(n))

  private val zeroCase = Lemma(
    (HeightKernel.introFunctionMono, HeightKernel.isHeightCore(f), HeightKernel.isHeightCore(g)) |- stageEq(∅)
  ) {
    val fZero = have(
      (HeightKernel.introFunctionMono, HeightKernel.isHeightCore(f), HeightKernel.isHeightCore(g)) |- !in(x, app(f, ∅))
    ) by Tautology.from(HeightKernelSuccessor.heightZero of (h := f))
    val gZero = have(
      (HeightKernel.introFunctionMono, HeightKernel.isHeightCore(f), HeightKernel.isHeightCore(g)) |- !in(x, app(g, ∅))
    ) by Tautology.from(HeightKernelSuccessor.heightZero of (h := g))
    have(
      (HeightKernel.introFunctionMono, HeightKernel.isHeightCore(f), HeightKernel.isHeightCore(g)) |- in(x, app(f, ∅)) <=> in(x, app(g, ∅))
    ) by Tautology.from(fZero, gZero)
    thenHave(thesis) by Extensionality
  }


  private val succCase = Lemma(
    (HeightKernel.introFunctionMono, HeightKernel.isHeightCore(f), HeightKernel.isHeightCore(g), in(n, N), stageEqN) |- stageEqSuccN
  ) {
    val fSucc = have(
      (HeightKernel.introFunctionMono, HeightKernel.isHeightCore(f), HeightKernel.isHeightCore(g), in(n, N), stageEqN) |-
        in(x, app(f, successor(n))) <=> HeightKernel.inIntroImage(app(f, n))(x)
    ) by Tautology.from(HeightKernelSuccessor.heightSuccessorWeak of (h := f))
    val gSucc = have(
      (HeightKernel.introFunctionMono, HeightKernel.isHeightCore(f), HeightKernel.isHeightCore(g), in(n, N), stageEqN) |-
        in(x, app(g, successor(n))) <=> HeightKernel.inIntroImage(app(g, n))(x)
    ) by Tautology.from(HeightKernelSuccessor.heightSuccessorWeak of (h := g))

    have(
      (HeightKernel.introFunctionMono, HeightKernel.isHeightCore(f), HeightKernel.isHeightCore(g), in(n, N), stageEqN) |-
        HeightKernel.inIntroImage(app(f, n))(x) <=> HeightKernel.inIntroImage(app(g, n))(x)
    ) by Congruence

    have(
      (HeightKernel.introFunctionMono, HeightKernel.isHeightCore(f), HeightKernel.isHeightCore(g), in(n, N), stageEqN) |-
        in(x, app(f, successor(n))) <=> in(x, app(g, successor(n)))
    ) by Tautology.from(fSucc, gSucc, lastStep)
    thenHave(thesis) by Extensionality
  }


  val uniqueness = Lemma(
    (HeightKernel.introFunctionMono, HeightKernel.isHeightCore(f), HeightKernel.isHeightCore(g)) |- f === g
  ) {

    val induction = have(
      (
        HeightKernel.introFunctionMono,
        HeightKernel.isHeightCore(f),
        HeightKernel.isHeightCore(g),
        ∀(n, in(n, N) ==> (stageEqN ==> stageEqSuccN))
      ) |- ∀(n, in(n, N) ==> stageEqN)
    ) by Cut(zeroCase, natInduction of (P := lam(n, stageEqN)))

    have(
      (HeightKernel.introFunctionMono, HeightKernel.isHeightCore(f), HeightKernel.isHeightCore(g), in(n, N)) |- stageEqN ==> stageEqSuccN
    ) by RightImplies(succCase)
    thenHave(
      (HeightKernel.introFunctionMono, HeightKernel.isHeightCore(f), HeightKernel.isHeightCore(g)) |- in(n, N) ==> (stageEqN ==> stageEqSuccN)
    ) by RightImplies
    val stepForall = thenHave(
      (HeightKernel.introFunctionMono, HeightKernel.isHeightCore(f), HeightKernel.isHeightCore(g)) |- ∀(n, in(n, N) ==> (stageEqN ==> stageEqSuccN))
    ) by RightForall

    val stagesEqual = have(
      (HeightKernel.introFunctionMono, HeightKernel.isHeightCore(f), HeightKernel.isHeightCore(g)) |- ∀(n, in(n, N) ==> stageEqN)
    ) by Cut(stepForall, induction)

    val fOnN = have(
      (HeightKernel.introFunctionMono, HeightKernel.isHeightCore(f), HeightKernel.isHeightCore(g)) |- functionOn(f)(N)
    ) by Tautology.from(
      functionOnIffFunctionWithDomain of (f := f, A := N)
    )
    val gOnN = have(
      (HeightKernel.introFunctionMono, HeightKernel.isHeightCore(f), HeightKernel.isHeightCore(g)) |- functionOn(g)(N)
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
}
