package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.Quantifiers
import lisa.maths.SetTheory.Functions.BasicTheorems
import lisa.maths.SetTheory.Functions.Function.abs
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Functions.Predef.app
import lisa.maths.SetTheory.Functions.Predef.functionOn
import lisa.maths.SetTheory.Functions.Predef.↾
import lisa.maths.SetTheory.Ordinals.Integer.{emptyInOmega, omegaSuccessorInduction, selfInSuccessor, successorInOmega}
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.Ordinals.OmegaFacts
import lisa.maths.SetTheory.Ordinals.TransfiniteRecursion
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Ordinals.Integer
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.prooflib.BasicStepTactic.Cut
import lisa.utils.prooflib.BasicStepTactic.LeftExists
import lisa.utils.prooflib.BasicStepTactic.RightForall
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 *  Approximant sequence construction.
 *
 *  Builds the height-indexed approximant sequence G : ω → (A→T) defined by transfinite
 *  recursion on ω:
 *
 *  G(0) = W(g₀) 
 *  G(n+1) = W(G(n))
 *
 *  Exports:
 *    - [[G]] — the approximant sequence
 *    - [[approxSucc]] — ∀k ∈ ω, G(S(k)) = W(G(k))
 *    - [[approxHasType]] — ∀n ∈ ω, G(n) :: spec.typ
 */
private[recursion] final class ApproxSequence[N <: Arity](
    val spec: FunSpec[N],
    val recWitness: Witness[N]
) {

  // ─────────────────────────────────────────────────────────────────────────
  // Fresh variables (distinct from Utils)
  // ─────────────────────────────────────────────────────────────────────────

  val f0 = variable[Ind] // seed placeholder for ε
  val nVar = variable[Ind] // ℕ index
  val kVar = variable[Ind] // predecessor index (outer lemma variable)
  val jVar = variable[Ind] // ∃-bound variable in stepFunc
  val hist = variable[Ind] // history function (restriction of approxSeq)
  val yVar = variable[Ind] // ε-witness for step function value
  val Func = variable[Ind >>: Ind >>: Ind]

  // ─────────────────────────────────────────────────────────────────────────
  // Lemma A — seedExists: ∃g₀, g₀ :: spec.typ
  // ─────────────────────────────────────────────────────────────────────────

  private val seedExists: THM = Lemma(∃(f0, f0 :: spec.typ)) {
    spec.cases.find(_.binders.isEmpty) match {

      case Some(pattern) =>
        val body = pattern.body
        val seedArg = variable[Ind]
        val seed = abs(spec.argType)(λ(seedArg, body))
        have(seed :: spec.typ) by Typecheck.prove
        thenHave(thesis) by RightExists

      case None =>
        throw new IllegalArgumentException("Cannot construct seed function for approximant sequence: no nullary constructor case found.")
    }
  }

  /**
   * ε-chosen seed function g₀ :: spec.typ.
   */
  private val g0: Expr[Ind] = ε(f0, f0 :: spec.typ)

  // ─────────────────────────────────────────────────────────────────────────
  // Lemma B — approxSeq: the approximant sequence G : ω → (A→T)
  // ─────────────────────────────────────────────────────────────────────────

  private val stepFunc = λ(
    nVar,
    λ(
      hist,
      ε(
        yVar,
        ((nVar === ∅) /\ (yVar === recWitness(g0))) \/ ∃(
          jVar,
          (jVar ∈ N) /\ (nVar === S(jVar)) /\ (yVar === recWitness(app(hist)(jVar)))
        )
      )
    )
  )

  /**
   * G : ω → (A→T) defined by transfinite recursion.
   */
  private val approxSeq: Expr[Ind] = TransfiniteRecursion
    .transfiniteRecursionFunction(stepFunc)(N)

  private val recSpec: THM = Lemma(
    functionOn(approxSeq)(N) /\ ∀(x ∈ N, app(approxSeq)(x) === stepFunc(x)(approxSeq ↾ x))
  ) {
    have(thesis) by Tautology.from(
      OmegaFacts.isOrdinal,
      TransfiniteRecursion.transfiniteRecursionFunctionSpec.of(Func := stepFunc, α := N)
    )
  }

  def G(n: Expr[Ind]): Expr[Ind] = app(approxSeq)(n)

  // ─────────────────────────────────────────────────────────────────────────
  // Shared recursion-step machinery
  // ─────────────────────────────────────────────────────────────────────────

  /**
   * Evaluates the approximant sequence at `index`, reducing the goal to the ε-step.
   *
   * Both [[approxZero]] and [[approxSucc]] reduce `G(index)` to the ε-chosen value
   * `ε(yVar, Q(yVar))` and then identify that value with `target`. Everything except
   * the choice of `Q`/`target` and the existence/uniqueness arguments is identical, so
   * it is factored here.
   *
   * @param index      the evaluation point (∅ or S(k))
   * @param indexInN   proof that `index ∈ N`
   * @param Q          the ε-predicate, i.e. `stepFunc(index)(approxSeq ↾ index) = ε(yVar, Q(yVar))`
   * @param target     the claimed value of `G(index)`
   * @param existence  proof of `∃yVar, Q(yVar)`
   * @param uniqueness proof of `∀yVar, Q(yVar) ⟹ yVar = target`
   * @return a fact establishing `G(index) === target`
   */
  private def approxValueAt(using proof: lisa.SetTheoryLibrary.Proof)(
      index: Expr[Ind],
      indexInN: proof.Fact,
      Q: Expr[Ind >>: Prop],
      target: Expr[Ind],
      existence: proof.Fact,
      uniqueness: proof.Fact
  ): proof.Fact = {
    val eqAll = have(∀(x ∈ N, app(approxSeq)(x) === stepFunc(x)(approxSeq ↾ x))) by
      Weakening(recSpec)

    val eqIdx = have(
      index ∈ N |- app(approxSeq)(index) === stepFunc(index)(approxSeq ↾ index)
    ) by InstantiateForall(index)(eqAll)

    val betaEq = have(stepFunc(index)(approxSeq ↾ index) === ε(yVar, Q(yVar))) by Restate

    val epsQ = have(Q(ε(yVar, Q(yVar)))) by
      Cut(existence, Quantifiers.existsEpsilon.of(x := yVar, P := Q))
    val epsImp = have(Q(ε(yVar, Q(yVar))) ==> (ε(yVar, Q(yVar)) === target)) by
      InstantiateForall(ε(yVar, Q(yVar)))(uniqueness)
    val epsEq = have(ε(yVar, Q(yVar)) === target) by Tautology.from(epsQ, epsImp)

    val recIdx = have(index ∈ N |- G(index) === target) by Congruence.from(eqIdx, betaEq, epsEq)
    have(G(index) === target) by Cut(indexInN, recIdx)
  }

  // ─────────────────────────────────────────────────────────────────────────
  // approxZero: G(0) = W(g₀)
  // ─────────────────────────────────────────────────────────────────────────

  private val approxZero: THM = Lemma(G(∅) === recWitness(g0)) {
    val succBody =
      (jVar ∈ N) /\ (∅ === S(jVar)) /\ (yVar === recWitness(app(approxSeq ↾ ∅)(jVar)))
    val Q = λ(yVar, ((∅ === ∅) /\ (yVar === recWitness(g0))) \/ ∃(jVar, succBody))

    have(Q(recWitness(g0))) by Tautology
    val exists = thenHave(∃(yVar, Q(yVar))) by RightExists

    // The ∃j disjunct forces ∅ === S(j), which is impossible.
    val zEqSj = have(succBody |- ∅ === S(jVar)) by Tautology
    val SjEq0 = have(succBody |- S(jVar) === ∅) by Congruence.from(zEqSj)
    val noSucc = have(succBody |- ()) by Tautology.from(SjEq0, Integer.zeroIsNotSucc.of(n := jVar))

    val noSuccEx = have(∃(jVar, succBody) |- ()) by LeftExists(noSucc)
    val disj = have(Q(yVar) |- ((∅ === ∅) /\ (yVar === recWitness(g0))) \/ ∃(jVar, succBody)) by Restate
    have(Q(yVar) ==> (yVar === recWitness(g0))) by Tautology.from(disj, noSuccEx)
    val uniqueness = thenHave(∀(yVar, Q(yVar) ==> (yVar === recWitness(g0)))) by RightForall

    val emptyInN = have(∅ ∈ N) by Restate.from(emptyInOmega)
    have(thesis) by Restate.from(
      approxValueAt(∅, emptyInN, Q, recWitness(g0), exists, uniqueness)
    )
  }

  // ─────────────────────────────────────────────────────────────────────────
  // approxSucc: ∀k ∈ ℕ, G(S(k)) = W(G(k))
  // ─────────────────────────────────────────────────────────────────────────

  val approxSucc: THM = Lemma(∀(kVar ∈ N, G(S(kVar)) === recWitness(G(kVar)))) {
    have(kVar ∈ N |- G(S(kVar)) === recWitness(G(kVar))) subproof {
      val kInNat = assume(kVar ∈ N)
      val SkInNat = have(S(kVar) ∈ N) by Tautology.from(kInNat, successorInOmega.of(n := kVar))

      val hSk = approxSeq ↾ S(kVar)
      val succBody =
        (jVar ∈ N) /\ (S(kVar) === S(jVar)) /\ (yVar === recWitness(app(hSk)(jVar)))
      val Q = λ(yVar, ((S(kVar) === ∅) /\ (yVar === recWitness(g0))) \/ ∃(jVar, succBody))

      // Existence: recWitness(app(hSk)(k)) satisfies Q via the witness j := k.
      have(
        (kVar ∈ N) /\ (S(kVar) === S(kVar)) /\
          (recWitness(app(hSk)(kVar)) === recWitness(app(hSk)(kVar)))
      ) by Restate.from(kInNat)
      thenHave(
        ∃(jVar,
          (jVar ∈ N) /\ (S(kVar) === S(jVar)) /\
            (recWitness(app(hSk)(kVar)) === recWitness(app(hSk)(jVar)))
        )
      ) by RightExists
      thenHave(Q(recWitness(app(hSk)(kVar)))) by Tautology
      val exY = thenHave(∃(yVar, Q(yVar))) by RightExists

      // Uniqueness: the ∃j disjunct gives S(k) === S(j), so injectivity forces j === k;
      // the S(k) === ∅ disjunct is impossible.
      val yEq = have(succBody |- yVar === recWitness(app(hSk)(jVar))) by Restate
      val jEqK = have(succBody |- kVar === jVar) by 
        Tautology.from(Integer.successorInjectivity.of(n := kVar, m := jVar))
      have(succBody |- yVar === recWitness(app(hSk)(kVar))) by Congruence.from(yEq, jEqK)
      val fromExJ =
        thenHave(∃(jVar, succBody) |- yVar === recWitness(app(hSk)(kVar))) by LeftExists

      val disj = have(
        Q(yVar) |- ((S(kVar) === ∅) /\ (yVar === recWitness(g0))) \/ ∃(jVar, succBody)
      ) by Restate
      val exJ = have(Q(yVar) |- ∃(jVar, succBody)) by Tautology.from(
        disj, 
        Integer.zeroIsNotSucc.of(n := kVar)
      )
      have(Q(yVar) |- yVar === recWitness(app(hSk)(kVar))) by Cut(exJ, fromExJ)
      thenHave(Q(yVar) ==> (yVar === recWitness(app(hSk)(kVar)))) by Restate
      val uniq =
        thenHave(∀(yVar, Q(yVar) ==> (yVar === recWitness(app(hSk)(kVar))))) by RightForall
        

      val kInSk = have(kVar ∈ S(kVar)) by Weakening(selfInSuccessor.of(n := kVar))
      val GmOn = have(functionOn(approxSeq)(N)) by Weakening(recSpec)
      val GmDom = have(dom(approxSeq) === N) by
        Tautology.from(GmOn, BasicTheorems.functionOnDomain.of(f := approxSeq, A := N))
      val kInDom = have(kVar ∈ dom(approxSeq)) by Congruence.from(kInNat, GmDom)
      val hSkAtK = have(app(hSk)(kVar) === G(kVar)) by
        Tautology.from(
          Restriction.restrictedApp.of(f := approxSeq, x := kVar, A := S(kVar)),
          BasicTheorems.functionOnIsFunction.of(f := approxSeq, A := N),
          GmOn, 
          kInDom,
          kInSk
        )

      have(thesis) by Congruence.from(
        approxValueAt(S(kVar), SkInNat, Q, recWitness(app(hSk)(kVar)), exY, uniq), 
        hSkAtK
      )
    }
    thenHave(kVar ∈ N ==> (G(S(kVar)) === recWitness(G(kVar)))) by RightImplies
    thenHave(thesis) by RightForall
  }

  // ─────────────────────────────────────────────────────────────────────────
  // approxHasType: ∀n ∈ ℕ, G(n) :: spec.typ
  // ─────────────────────────────────────────────────────────────────────────

  val approxHasType: THM = Lemma(∀(nVar ∈ N, G(nVar) :: spec.typ)) {
    val P = variable[Ind >>: Prop]
    val prop = λ(nVar, G(nVar) :: spec.typ)

    val epsStep = have(∃(f0, f0 :: spec.typ) |- g0 :: spec.typ) by
      Restate.from(Quantifiers.existsEpsilon.of(x := f0, P := λ(f0, f0 :: spec.typ)))
    val g0Typed = have(g0 :: spec.typ) by Cut(seedExists, epsStep)

    // Base case: G(0) = W(g₀), typed because g₀ is.
    val witnessAtG0Typed = have(recWitness(g0) :: spec.typ) by
      Tautology.from(g0Typed, recWitness.witnessHasType.of(spec.selfPlaceholder := g0))
    have(G(∅) :: spec.typ) by Congruence.from(approxZero, witnessAtG0Typed)
    val base = thenHave(prop(∅)) by Restate

    // Step: G(S(n)) = W(G(n)), typed because G(n) is (induction hypothesis). The
    // assumptions on n are scoped to the inner subproof so n stays generalizable.
    have((nVar ∈ N) ==> (prop(nVar) ==> prop(S(nVar)))) subproof {
      val nInNat = assume(nVar ∈ N)
      val ih = assume(prop(nVar))

      val approxSuccAtN = have(nVar ∈ N ==> (G(S(nVar)) === recWitness(G(nVar)))) by
        InstantiateForall(nVar)(approxSucc)
      val gSuccEq = have(G(S(nVar)) === recWitness(G(nVar))) by
        Tautology.from(nInNat, approxSuccAtN)
      val witnessAtGnTyped = have(recWitness(G(nVar)) :: spec.typ) by
        Tautology.from(ih, recWitness.witnessHasType.of(spec.selfPlaceholder := G(nVar)))
      have(G(S(nVar)) :: spec.typ) by Congruence.from(gSuccEq, witnessAtGnTyped)
      thenHave(thesis) by Restate
    }
    val step = thenHave(∀(nVar, (nVar ∈ N) ==> (prop(nVar) ==> prop(S(nVar))))) by RightForall

    have(∀(nVar, (nVar ∈ N) ==> prop(nVar))) by
      Tautology.from(omegaSuccessorInduction of (P := prop), base, step)
    thenHave(thesis) by Restate
  }
}
