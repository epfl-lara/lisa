package lisa.maths.SetTheory.Types.ADTv2.height.proofs

import lisa.maths.SetTheory.Base.Extensionality
import lisa.maths.SetTheory.Functions.BasicTheorems.extensionality
import lisa.maths.SetTheory.Functions.BasicTheorems.functionOnIffFunctionWithDomain
import lisa.maths.SetTheory.Ordinals.Integer.omegaSuccessorInduction
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.tactics.Cuts
import lisa.maths.SetTheory.Functions.Function.{function, functionOn, dom}

private[height] object UniquenessFacts {

  protected inline final def app(f: Expr[Ind], x: Expr[Ind]): Expr[Ind] =
    lisa.maths.SetTheory.Functions.Predef.app(f)(x)

  private def stageEq(k: Expr[Ind]): Expr[Prop] = app(f, k) === app(g, k)
  private val stageEqN = stageEq(n)
  private val stageEqSuccN = stageEq(S(n))

  private val zeroCase = Lemma(
    (CoreFacts.introFunctionMono, CoreFacts.isHeightCore(f), CoreFacts.isHeightCore(g)) |- stageEq(∅)
  ) {
    assume(CoreFacts.introFunctionMono, CoreFacts.isHeightCore(f), CoreFacts.isHeightCore(g))
    // x ∉ app(f, ∅) and x ∉ app(g, ∅), so both memberships are equivalent (both false).
    val contraF = have(x ∈ app(f, ∅) |- ()) by LeftNot(SuccessorFacts.heightZero.of(h := f))
    have(x ∈ app(f, ∅) |- x ∈ app(g, ∅)) by Weakening(contraF)
    val fwd = thenHave(x ∈ app(f, ∅) ==> x ∈ app(g, ∅)) by RightImplies
    val contraG = have(x ∈ app(g, ∅) |- ()) by LeftNot(SuccessorFacts.heightZero.of(h := g))
    have(x ∈ app(g, ∅) |- x ∈ app(f, ∅)) by Weakening(contraG)
    val bwd = thenHave(x ∈ app(g, ∅) ==> x ∈ app(f, ∅)) by RightImplies
    have((x ∈ app(f, ∅)) <=> (x ∈ app(g, ∅))) by RightIff(fwd, bwd)
    thenHave(thesis) by Extensionality
  }

  private val succCase = Lemma(
    (CoreFacts.introFunctionMono, CoreFacts.isHeightCore(f), CoreFacts.isHeightCore(g), n ∈ N, stageEqN) |- stageEqSuccN
  ) {
    assume(CoreFacts.introFunctionMono, CoreFacts.isHeightCore(f), CoreFacts.isHeightCore(g), n ∈ N, stageEqN)

    // heightSuccessorWeak rewrites each membership at S(n) to the intro-image at n; the assumed
    // stageEqN (app(f, n) === app(g, n)) makes those intro-images equal by congruence closure.
    have(x ∈ app(f, S(n)) <=> x ∈ app(g, S(n))) by Congruence.from(
      SuccessorFacts.heightSuccessorWeak.of(h := f),
      SuccessorFacts.heightSuccessorWeak.of(h := g)
    )
    thenHave(thesis) by Extensionality
  }

  val uniqueness = Lemma(
    (CoreFacts.introFunctionMono, CoreFacts.isHeightCore(f), CoreFacts.isHeightCore(g)) |- f === g
  ) {

    assume(CoreFacts.introFunctionMono, CoreFacts.isHeightCore(f), CoreFacts.isHeightCore(g))

    // Inductive step, packaged as a bounded ∀.
    have(n ∈ N ==> (stageEqN ==> stageEqSuccN)) by Restate.from(succCase)
    val stepForall = thenHave(∀(n, n ∈ N ==> (stageEqN ==> stageEqSuccN))) by RightForall

    // ω-induction: from stageEq(∅) (zeroCase) and the step, get ∀ n ∈ N, app(f, n) === app(g, n).
    val inductionInstance = have(
      (stageEq(∅), ∀(n, n ∈ N ==> (stageEqN ==> stageEqSuccN))) |- ∀(n, n ∈ N ==> stageEqN)
    ) by Weakening(omegaSuccessorInduction of (P := λ(n, stageEqN)))
    val allStageEq = have(∀(n, n ∈ N ==> stageEqN)) by Cuts(inductionInstance)(
      zeroCase,
      stepForall
    )

    // f and g are functions on N (isHeightCore gives function(·) ∧ dom(·) === N).
    val fProps = have(function(f) /\ (dom(f) === N)) by Restate
    have((function(f) /\ (dom(f) === N)) |- functionOn(f)(N)) by Weakening(
      functionOnIffFunctionWithDomain of (f := f, A := N)
    )
    val fOnN = have(functionOn(f)(N)) by Cut(fProps, lastStep)

    val gProps = have(function(g) /\ (dom(g) === N)) by Restate
    have((function(g) /\ (dom(g) === N)) |- functionOn(g)(N)) by Weakening(
      functionOnIffFunctionWithDomain of (f := g, A := N)
    )
    val gOnN = have(functionOn(g)(N)) by Cut(gProps, lastStep)

    // Functional extensionality on N.
    have(thesis) by Cuts(extensionality of (f := f, g := g, A := N))(
      allStageEq,
      fOnN,
      gOnN
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
