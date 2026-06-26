package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Functions.BasicTheorems.funcBetweenEqInFuncSpace
import lisa.maths.SetTheory.Functions.BasicTheorems.functionalExtentionality
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Ordinals.Integer.{elementsTransitive, selfInSuccessor, successorInOmega}
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.Ordinals.TransitiveSet
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.FunctionCore.ExistenceProof
import lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.ApproximationChainFacts
import lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.LimitKernel
import lisa.utils.debug.Time
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.prooflib.ProofTacticLib.Arity

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
private[recursion] final class Existence[N <: Arity](
    val spec: FunSpec[N],
    val recWitness: Witness[N],
    val approxSeq: ApproxSequence[N],
    val approxStab: ApproxStabilization[N],
    val limitConstruction: LimitConstruction[N],
    val witnessAgreement: helpers.WitnessAgreement[N]
) extends ExistenceProof[N] {

  val nVar = variable[Ind]
  private val heightSuccessorInclusion = spec.adt.height.successorInclusionAt(spec.typeSubstitutions)
  private val heightMembershipMonotonic = spec.adt.height.membershipMonotonicAt(spec.typeSubstitutions)
  private val termHasHeight = spec.adt.height.termHasHeightAt(spec.typeSubstitutions)

  import approxSeq.G
  import spec.{heightFun, heightFunValid, isHeightPred}
  import approxStab.stabilization
  import limitConstruction.{limitFun, limitHasType, limitIndex}

  private val pointParam = variable[Ind]
  private val indexParam = variable[Ind]
  private val approximantFamily = λ(indexParam, G(indexParam))
  private val chosenIndexFamily = λ(pointParam, ε(nVar, (nVar ∈ N) /\ (pointParam ∈ app(heightFun)(nVar))))

  // ─────────────────────────────────────────────────────────────────────────
  // Lemma F — limitIsFixedPoint: W(limitFun) = limitFun
  // ─────────────────────────────────────────────────────────────────────────

  private val limitIsFixedPoint: THM = Time.measure(s"Ex/limitIsFixedPoint")(Lemma(recWitness(limitFun) === limitFun) {
    val hValid = have(isHeightPred(heightFun)) by Restate.from(heightFunValid)
    val stabilizationSchema = ApproximationChainFacts.stabilizationSchemaAt(heightFun, approximantFamily, stabilization)
    val heightMembershipMonotonicSchema = ApproximationChainFacts.heightMembershipMonotonicSchemaAt(
      heightFun,
      heightMembershipMonotonic
    )(hValid)

    val limitBetween = have(functionBetween(limitFun)(spec.argType)(spec.returnType)) by Tautology.from(
      funcBetweenEqInFuncSpace of (f := limitFun, A := spec.argType, B := spec.returnType),
      limitHasType
    )
    val witnessAtLimitBetween = have(functionBetween(recWitness(limitFun))(spec.argType)(spec.returnType)) by Tautology.from(
      funcBetweenEqInFuncSpace of (f := recWitness(limitFun), A := spec.argType, B := spec.returnType),
      limitHasType,
      recWitness.witnessHasType.of(spec.selfPlaceholder := limitFun)
    )

    val pointwiseGoal = app(recWitness(limitFun))(a) === app(limitFun)(a)

    have((a ∈ spec.argType) ==> pointwiseGoal) subproof {
      val aInArgType = assume(a ∈ spec.argType)

      // ── Height index for a ──────────────────────────────────────────────────
      val indexWitness = have(
        (limitIndex(a) ∈ N) /\ (a ∈ app(heightFun)(limitIndex(a)))
      ) by Tautology.from(
        hValid,
        termHasHeight of (x := a, h := heightFun),
        aInArgType,
        LimitKernel.limitIndexWitnessAt(spec.argType, heightFun, chosenIndexFamily, a)
      )

      val n0 = limitIndex(a)
      val indexInN = have(n0 ∈ N) by Weakening(indexWitness)
      val aInHeightN0 = have(a ∈ app(heightFun)(n0)) by Weakening(indexWitness)

      val n0SubSuccN0 = have(n0 ⊆ S(n0)) by Tautology.from(
        selfInSuccessor.of(n := n0),
        indexInN,
        successorInOmega.of(n := n0), 
        elementsTransitive.of(n := S(n0)),
        TransitiveSet.elementIsSubset.of(A := S(n0), x := n0)
      )

      // a ∈ h(S(n0))
      val aInHeightSuccN0 = have(a ∈ app(heightFun)(S(n0))) by Tautology.from(
        hValid,
        indexInN,
        aInHeightN0,
        heightSuccessorInclusion.of(h := heightFun, n := n0, x := a)
      )

      // ── G(n0) type and stabilization chain ─────────────────────────────────
      val approxAtN0Inst = have(n0 ∈ N ==> (G(n0) :: spec.typ)) by InstantiateForall(n0)(approxSeq.approxHasType)
      val approxSuccAtN0Impl = have(n0 ∈ N ==> (G(S(n0)) === recWitness(G(n0)))) by
        InstantiateForall(n0)(approxSeq.approxSucc)
      val gN0HasType = have(G(n0) :: spec.typ) by Tautology.from(indexInN, approxAtN0Inst)
      val gSuccN0EqWitness = have(G(S(n0)) === recWitness(G(n0))) by
        Tautology.from(indexInN, approxSuccAtN0Impl)

      // G(n0)(a) = G(Succ(n0))(a) via approximantsAgreeFromSubset (avoids capture of `a` in stabilization)
      val stabAtAFact = have(app(G(n0))(a) === app(G(S(n0)))(a)) by Tautology.from(
        indexInN,
        successorInOmega.of(n := n0),
        n0SubSuccN0,
        aInHeightN0,
        ApproximationChainFacts.approximantsAgreeFromSubsetAt(
          heightFun,
          approximantFamily,
          n0,
          S(n0),
          a
        )(stabilizationSchema, heightMembershipMonotonicSchema)
      )
      val gN0AtAEqWitness = have(app(recWitness(G(n0)))(a) === app(G(n0))(a)) by
        Congruence.from(stabAtAFact, gSuccN0EqWitness)
      

      // ── Witness agreement at a via the shared WitnessAgreement lemma ────────
      // limitFun and G(n0) agree on the height slice h(n0): at each point the
      // limit value is the stabilized approximant value G(n0). This is exactly
      // the slice-agreement premise of WitnessAgreement.witnessAgreementAtSucc.
      val sliceVar = variable[Ind]
      val limitEqApprox = have((sliceVar ∈ app(heightFun)(n0)) ==> (app(limitFun)(sliceVar) === app(G(n0))(sliceVar))) by Tautology.from(
        hValid,
        termHasHeight.of(x := sliceVar, h := heightFun),
        indexInN,
        ApproximationChainFacts.approximantsAgreeAcrossHeightsAt(
          heightFun,
          approximantFamily,
          chosenIndexFamily(sliceVar),
          n0,
          sliceVar,
          stabilizationSchema, 
          heightMembershipMonotonicSchema
        ),
        LimitKernel.limitAtHeightAt(
          spec.argType,
          heightFun,
          limitFun,
          approximantFamily,
          chosenIndexFamily,
          sliceVar,
          n0
        )
      )

      
      val limitAtAEqGN0 = have(app(G(n0))(a) === app(limitFun)(a)) by Tautology.from(
        aInHeightN0,
        limitEqApprox of (sliceVar := a)
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

    thenHave(∀(a, (a ∈ spec.argType) ==> pointwiseGoal)) by RightForall

    have(recWitness(limitFun) === limitFun) by Tautology.from(
      witnessAtLimitBetween,
      limitBetween,
      lastStep,
      functionalExtentionality of (f := recWitness(limitFun), g := limitFun, A := spec.argType, B := spec.returnType)
    )
    thenHave(thesis) by Restate
  })

  // ─────────────────────────────────────────────────────────────────────────
  // defAtFixedPoint: (f :: A→T) ∧ W(f) = f ⊢ Def(f)
  // ─────────────────────────────────────────────────────────────────────────

  private val defAtFixedPoint: THM = Lemma(
    ((f :: spec.typ) /\ (recWitness(f) === f)) |- spec.untypedDefinition(f)
  ) {

    val fTyped = assume(f :: spec.typ)
    val wfEqF = assume(recWitness(f) === f)

    val caseFacts = spec.patternMatching.patterns
      .map(pattern =>
        val vars = pattern.binders
        val body = pattern.body.substitute(spec.selfPlaceholder := f).asInstanceOf[Expr[Ind]]
        val witnessCaseSchema = recWitness.witnessCase(pattern).of(spec.selfPlaceholder := f)

        val allForalls = have(
          forallSeq(vars, pattern.branchPremiseAt(vars) ==> (recWitness(f) * pattern.inputTermAt(vars) === body))
        ) by Tautology.from(witnessCaseSchema)

        val instantiated = vars.foldLeft(allForalls)((acc, v) =>
          acc.statement.right.head match
            case forall(_, phi) => thenHave(phi) by InstantiateForall(v)
            case _ => acc
        )

        val withF = have(pattern.branchPremiseAt(vars) ==> (f * pattern.inputTermAt(vars) === body)) by
          Substitute(wfEqF)(instantiated)

        vars.foldRight(withF)((v, acc) => thenHave(∀(v, acc.statement.right.head)) by RightForall)
      )
      .toSeq

    have(thesis) by RightAnd((fTyped +: caseFacts)*)
  }
  

  // ─────────────────────────────────────────────────────────────────────────
  // witnessExists: ∃f, Def(f)
  // ─────────────────────────────────────────────────────────────────────────

  val witnessExists: THM = Lemma(∃(f, spec.untypedDefinition(f))) {

    have(((limitFun :: spec.typ) /\ (recWitness(limitFun) === limitFun))) by
        RightAnd(limitHasType, limitIsFixedPoint)
    have(spec.untypedDefinition(limitFun)) by Cut(lastStep, defAtFixedPoint of (f := limitFun))

    thenHave(thesis) by RightExists
  }
}
