package lisa.maths.SetTheory.Types.ADT.recursion

import lisa.maths.SetTheory.Functions.BasicTheorems.funcBetweenEqInFuncSpace
import lisa.maths.SetTheory.Functions.BasicTheorems.functionalExtentionality
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Ordinals.Integer.subsetSuccessor
import lisa.maths.SetTheory.Ordinals.Integer.successorInOmega
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.recursion.proofs.ApproximationChainFacts
import lisa.maths.SetTheory.Types.ADT.recursion.proofs.LimitKernel
import lisa.maths.SetTheory.Types.ADT.support.core.Utils
import lisa.maths.SetTheory.Types.ADT.support.core.Utils._
import lisa.maths.SetTheory.Types.ADT.support.tactics.Cuts
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.fol.FOL.SubstPair
import lisa.utils.prooflib.Thm

/**
 * Layer 3 — Existence without circularity.
 *
 * Delegates approximant construction to [[ApproxSequence]] and stabilization lemmas
 * to [[ApproxStabilization]], then proves:
 *
 *   limitIsFixedPoint : W(limitFun) = limitFun
 *   fixedPointExists  : ∃f :: A→T, W(f) = f
 *   defAtFixedPoint   : (f :: A→T) ∧ W(f) = f ⊢ Def(f)
 *   witnessExists     : ∃f, Def(f)
 *
 * Exported:
 *   - [[witnessExists]] — ∃f, Def(f)
 */
private[recursion] final class Existence(
    val spec: FunSpec,
    val recWitness: Witness,
    val approxSeq: ApproxSequence,
    val approxStab: ApproxStabilization,
    val limitConstruction: LimitConstruction,
    val witnessAgreement: helpers.WitnessAgreement
) {

  private val a = spec.proofVariable("a")
  private val f = spec.proofVariable("f")
  private def heightMembershipMonotonic(using proof: lisa.SetTheoryLibrary.ProofBuilder)(substitutions: Seq[SubstPair]): Thm =
    spec.adt.height.membershipMonotonicAt(spec.typeSubstitutions, substitutions)

  import approxSeq.G
  import spec.{heightFun, heightFunValid}
  import approxStab.stabilization
  import limitConstruction.{limitFun, limitHasType, limitIndex}

  private val pointParam = spec.proofVariable("pointParam")
  private val indexParam = spec.proofVariable("indexParam")
  private val approximantFamily = λ(indexParam, G(indexParam))
  private val chosenIndexFamily = λ(pointParam, limitIndex(pointParam))

  // ─────────────────────────────────────────────────────────────────────────
  // Lemma F — limitIsFixedPoint: W(limitFun) = limitFun
  // ─────────────────────────────────────────────────────────────────────────

  private val limitIsFixedPoint: Theorem = (Lemma.generated(recWitness(limitFun) === limitFun) {

    val funTyping = have((f :: spec.typ) |- functionBetween(f)(spec.argType)(spec.returnType)) by Weakening(
      funcBetweenEqInFuncSpace of (Utils.f := f, A := spec.argType, B := spec.returnType)
    )
    val limitBetween = have(functionBetween(limitFun)(spec.argType)(spec.returnType)) by Cut(
      limitHasType,
      funTyping of (f := limitFun)
    )
    val witnessAtLimitBetween = have(functionBetween(recWitness(limitFun))(spec.argType)(spec.returnType)) by Cuts(
      funTyping of (f := recWitness(limitFun))
    )(
      have((limitFun :: spec.typ) |- (recWitness(limitFun) :: spec.typ)) by Restate.from(
        recWitness.witnessHasType.of(spec.selfPlaceholder := limitFun)
      ),
      limitHasType
    )

    val pointwiseGoal = app(recWitness(limitFun))(a) === app(limitFun)(a)

    have((a ∈ spec.argType) ==> pointwiseGoal) subproof {
      val aInArgType = assume(a ∈ spec.argType)

      // ── Height index for a ──────────────────────────────────────────────────
      val indexWitness = have(
        (limitIndex(a) ∈ N) /\ (a ∈ app(heightFun)(limitIndex(a)))
      ) by Cuts(
        LimitKernel.limitIndexWitnessAt(spec.argType, heightFun, chosenIndexFamily, a)
      )(
        spec.adt.height.termHasHeightAt(spec.typeSubstitutions, Seq(x := a, h := heightFun)),
        heightFunValid,
        aInArgType
      )

      val n0 = limitIndex(a)
      val indexInN = have(n0 ∈ N) by Weakening(indexWitness)
      val aInHeightN0 = have(a ∈ app(heightFun)(n0)) by Weakening(indexWitness)

      val succN0InN = have(S(n0) ∈ N) by Cut(
        indexInN,
        have((n0 ∈ N) |- (S(n0) ∈ N)) by Weakening(successorInOmega.of(n := n0))
      )

      // a ∈ h(S(n0))
      val aInHeightSuccN0 = have(a ∈ app(heightFun)(S(n0))) by Cuts(
        spec.adt.height.successorInclusionAt(spec.typeSubstitutions, Seq(h := heightFun, n := n0, x := a))
      )(heightFunValid, indexInN, aInHeightN0)

      // ── G(n0) type and stabilization chain ─────────────────────────────────
      val approxAtN0Inst = have(n0 ∈ N ==> (G(n0) :: spec.typ)) by InstantiateForall(n0)(approxSeq.approxHasType)
      val approxSuccAtN0Impl = have(n0 ∈ N ==> (G(S(n0)) === recWitness(G(n0)))) by
        InstantiateForall(n0)(approxSeq.approxSucc)
      val gN0HasType = have(G(n0) :: spec.typ) by Cut(
        indexInN,
        have((n0 ∈ N) |- (G(n0) :: spec.typ)) by Restate.from(approxAtN0Inst)
      )
      val gSuccN0EqWitness = have(G(S(n0)) === recWitness(G(n0))) by Cut(
        indexInN,
        have((n0 ∈ N) |- (G(S(n0)) === recWitness(G(n0)))) by Restate.from(approxSuccAtN0Impl)
      )

      // G(n0)(a) = G(Succ(n0))(a) via approximantsAgreeFromSubset (avoids capture of `a` in stabilization)
      val stabAtAFact = have(app(G(n0))(a) === app(G(S(n0)))(a)) by Cuts(
        ApproximationChainFacts.approximantsAgreeFromSubsetAt(
          heightFun,
          approximantFamily,
          n0,
          S(n0),
          a,
          stabilization,
          heightMembershipMonotonic,
          heightFunValid
        )
      )(
        indexInN,
        succN0InN,
        subsetSuccessor.of(n := n0),
        aInHeightN0
      )
      val gN0AtAEqWitness = have(app(recWitness(G(n0)))(a) === app(G(n0))(a)) by
        Congruence.from(stabAtAFact, gSuccN0EqWitness)

      // ── Witness agreement at a via the shared WitnessAgreement lemma ────────
      // limitFun and G(n0) agree on the height slice h(n0): at each point the
      // limit value is the stabilized approximant value G(n0). This is exactly
      // the slice-agreement premise of WitnessAgreement.witnessAgreementAtSucc.
      val sliceVar = spec.proofVariable("sliceVar")

      val limitEqApprox = have(
        (sliceVar ∈ app(heightFun)(n0)) ==> (app(limitFun)(sliceVar) === app(G(n0))(sliceVar))
      ) by Cuts(
        LimitKernel.limitAtHeightAt(
          spec.argType,
          heightFun,
          limitFun,
          approximantFamily,
          chosenIndexFamily,
          sliceVar,
          n0,
          stabilization,
          heightMembershipMonotonic,
          heightFunValid
        )
      )(
        spec.adt.height.termHasHeightAt(spec.typeSubstitutions, Seq(x := sliceVar, h := heightFun)),
        heightFunValid,
        indexInN
      )

      val limitAtAEqGN0 = have(app(limitFun)(a) === app(G(n0))(a)) by Cut(
        aInHeightN0,
        have((a ∈ app(heightFun)(n0)) |- (app(limitFun)(a) === app(G(n0))(a))) by Restate.from(
          limitEqApprox of (sliceVar := a)
        )
      )
      val sliceAgreement = have(
        ∀(sliceVar ∈ app(heightFun)(n0), app(limitFun)(sliceVar) === app(G(n0))(sliceVar))
      ) by RightForall(limitEqApprox)

      // ∀x ∈ h(Succ n0), W(limitFun)(x) = W(G(n0))(x).
      // n0 = limitIndex(a) mentions the free variable `a`, so we must not rebind
      // `a` here: take the lemma's conclusion verbatim (its bound variable is
      // already renamed away from `a`) and instantiate it at `a`.
      // Chain: W(limit)(a) === W(G(n0))(a) === G(n0)(a) === limit(a), with the
      // first link supplied by the witness agreement and the rest as bridges.
      have(pointwiseGoal) by Restate.from(
        witnessAgreement.witnessesAgreeAt(
          lhs = limitFun,
          rhs = G(n0),
          index = n0,
          lhsTyped = limitHasType,
          rhsTyped = gN0HasType,
          indexInN = indexInN,
          sliceAgreement = sliceAgreement,
          pointInHeightSucc = aInHeightSuccN0,
          goal = pointwiseGoal,
          bridges = Seq(gN0AtAEqWitness, limitAtAEqGN0)
        )
      )
    }

    val forallPointwise = thenHave(∀(a, (a ∈ spec.argType) ==> pointwiseGoal)) by RightForall

    have(
      (functionBetween(recWitness(limitFun))(spec.argType)(spec.returnType), functionBetween(limitFun)(spec.argType)(spec.returnType), ∀(a, (a ∈ spec.argType) ==> pointwiseGoal)) |- (recWitness(
        limitFun
      ) === limitFun)
    ) by Restate.from(
      functionalExtentionality of (Utils.f := recWitness(limitFun), g := limitFun, A := spec.argType, B := spec.returnType)
    )
    have(recWitness(limitFun) === limitFun) by Cuts(lastStep)(
      witnessAtLimitBetween,
      limitBetween,
      forallPointwise
    )
    thenHave(thesis) by Restate
  })

  // ─────────────────────────────────────────────────────────────────────────
  // witnessExists: ∃f, Def(f)
  // ─────────────────────────────────────────────────────────────────────────

  val witnessExists: Theorem = Lemma.generated(∃(f, spec.definitionAt(f))) {

    val wfEqF = have(recWitness(f) === f |- recWitness(f) === f) by Hypothesis
    val fTyped = have(spec.typeConstraint(f) |- spec.typeConstraint(f)) by Hypothesis

    val caseFacts = spec.patternMatching.clauses
      .map(pattern =>
        val body = pattern.body.substitute(spec.selfPlaceholder := f)
        val witnessCaseSchema = recWitness.witnessCase(pattern).of(spec.selfPlaceholder := f)

        val allForalls = have(
          spec.typeConstraint(f) |- forallSeq(pattern.binders, pattern.branchPremise ==> (recWitness(f) * pattern.inputTerm === body))
        ) by Tautology.from(witnessCaseSchema)

        have((spec.typeConstraint(f), recWitness(f) === f) |- spec.patternConstraint(pattern, f)) by Substitute(wfEqF)(allForalls)
      )
      .toSeq

    have((spec.typeConstraint(f), recWitness(f) === f) |- spec.equationConstraint(f)) by Tautology.from(caseFacts*)
    have((spec.typeConstraint(f), recWitness(f) === f) |- spec.definitionAt(f)) by RightAnd(fTyped, lastStep)
    have(spec.definitionAt(limitFun)) by Cuts(lastStep of (f := limitFun))(limitHasType, limitIsFixedPoint)
    thenHave(thesis) by RightExists

  }
}
