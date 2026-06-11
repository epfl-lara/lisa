package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.ADTv2.recursion.helpers.RecursiveAgreement
import lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.ConstructorSemanticFacts.{specializedConstructors}
import lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.{ApproximationChainFacts, LimitKernel}
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.{altEqualityTransitivity}
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.NatFacts
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.NatFacts.Succ
import lisa.maths.SetTheory.Types.ADTv2.support.Time


import lisa.maths.SetTheory.Functions.BasicTheorems.{funcBetweenEqInFuncSpace, functionalExtentionality}
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Ordinals.TransitiveSet
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.TypingHelpers.*
import lisa.utils.prooflib.BasicStepTactic.{LeftExists, Cut, RightForall}
import lisa.utils.prooflib.ProofTacticLib.Arity


/**
 * Layer 3 — Existence without circularity.
 *
 * Delegates approximant construction to [[Approx]] and stabilization lemmas
 * to [[ApproxProp]], then proves:
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
  val approx: Approx[N],
  val approxProp: ApproxProp[N],
  val limitConstruction: LimitConstruction[N],
  val witnessAgreement: lisa.maths.SetTheory.Types.ADTv2.recursion.helpers.WitnessAgreement[N]
) {

  val nVar = variable[Ind]
  private val heightSuccessorInclusion = spec.adt.height.successorInclusionAt(spec.typeSubstitutions)
  private val heightMembershipMonotonic = spec.adt.height.membershipMonotonicAt(spec.typeSubstitutions)
  private val termHasHeight = spec.adt.height.termHasHeightAt(spec.typeSubstitutions)
  
  import approx.G
  import approxProp.{heightFun, heightFunValid, isHeightPred, stabilization}
  import limitConstruction.{limitFun, limitHasType, limitIndex}

  private val pointParam = variable[Ind]
  private val indexParam = variable[Ind]
  private val approximantFamily = λ(indexParam, G(indexParam))
  private val chosenIndexFamily = λ(pointParam, ε(nVar, (nVar ∈ N) /\ (pointParam ∈ app(heightFun)(nVar))))
  private val limitFunDef = LimitKernel.limitFunDefinition(
    spec.argType,
    limitFun,
    approximantFamily,
    chosenIndexFamily
  )

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

    val T, e2 = variable[Ind]
    val e = variable[Ind >>: Ind]

    val witnessAtLimitTyped = have(recWitness(limitFun) :: spec.typ) by Tautology.from(
      limitHasType,
      recWitness.witnessHasType.of(spec.selfPlaceholder := limitFun)
    )
    val limitBetween = have(functionBetween(limitFun)(spec.argType)(spec.returnType)) by Tautology.from(
      funcBetweenEqInFuncSpace of (f := limitFun, A := spec.argType, B := spec.returnType),
      limitHasType
    )
    val witnessAtLimitBetween = have(functionBetween(recWitness(limitFun))(spec.argType)(spec.returnType)) by Tautology.from(
      funcBetweenEqInFuncSpace of (f := recWitness(limitFun), A := spec.argType, B := spec.returnType),
      witnessAtLimitTyped
    )

    val pointwiseGoal = app(recWitness(limitFun))(a) === app(limitFun)(a)

    val pointwiseAtA = have((a ∈ spec.argType) ==> pointwiseGoal) subproof {
      val aInArgType = assume(a ∈ spec.argType)
      val aHeightChar = have(LimitKernel.pointHeightCharAt(spec.argType, heightFun, a)) by
        Tautology.from(hValid, termHasHeight of (x := a, h := heightFun))

      // ── Height index for a ──────────────────────────────────────────────────
      val indexWitness = have(
        (limitIndex(a) ∈ N) /\ (a ∈ app(heightFun)(limitIndex(a)))
      ) by Tautology.from(
        aHeightChar,
        have(LimitKernel.limitIndexDefinitionAt(heightFun, chosenIndexFamily, a)) by Restate,
        aInArgType,
        LimitKernel.limitIndexWitnessAt(spec.argType, heightFun, chosenIndexFamily, a)
      )

      val n0         = limitIndex(a)
      val indexInN   = have(n0 ∈ N)   by Tautology.from(indexWitness)
      val aInHeightN0 = have(a ∈ app(heightFun)(n0)) by Tautology.from(indexWitness)

      val succN0InN   = have(Succ(n0) ∈ N)   by Tautology.from(indexInN, NatFacts.succIntro.of(n := n0))
      val succEqN0    = have(Succ(n0) === successor(n0)) by
        Tautology.from(Succ.definition of (x := n0))

      val n0InSuccN0 = have(n0 ∈ Succ(n0)) by Weakening(NatFacts.nInSucc.of(n := n0))
      val n0SubSuccN0 = have(n0 ⊆ Succ(n0)) by Tautology.from(
        n0InSuccN0,
        have(TransitiveSet.transitiveSet(Succ(n0))) by
          Tautology.from(succN0InN, NatFacts.elementsTransitive.of(n := Succ(n0))),
        TransitiveSet.elementIsSubset.of(A := Succ(n0), x := n0)
      )

      // a ∈ h(successor(n0))
      val aInHeightOrd = have(a ∈ app(heightFun)(successor(n0))) by Tautology.from(
        hValid,
        indexInN,
        aInHeightN0,
        heightSuccessorInclusion.of(h := heightFun, n := n0, x := a)
      )

      // ── G(n0) type and stabilization chain ─────────────────────────────────
      val approxAtN0Inst = have(n0 ∈ N ==> (G(n0) :: spec.typ)) by InstantiateForall(n0)(approx.approxHasType)
      val gN0HasType = have(G(n0) :: spec.typ) by Tautology.from(indexInN, approxAtN0Inst)
      val approxSuccAtN0Impl = have(n0 ∈ N ==> (G(Succ(n0)) === recWitness(G(n0)))) by
        InstantiateForall(n0)(approx.approxSucc)
      val gSuccN0EqWitness = have(G(Succ(n0)) === recWitness(G(n0))) by
        Tautology.from(indexInN, approxSuccAtN0Impl)

      // G(n0)(a) = G(Succ(n0))(a) via approximantsAgreeFromSubset (avoids capture of `a` in stabilization)
      val stabAtAFact = have(app(G(n0))(a) === app(G(Succ(n0)))(a)) by Tautology.from(
        indexInN,
        succN0InN,
        n0SubSuccN0,
        aInHeightN0,
        ApproximationChainFacts.approximantsAgreeFromSubsetAt(
          heightFun,
          approximantFamily,
          n0,
          Succ(n0),
          a
        )(stabilizationSchema, heightMembershipMonotonicSchema)
      )
      val gN0AtAEqWitness = have(app(recWitness(G(n0)))(a) === app(G(n0))(a)) by
        Congruence.from(stabAtAFact, gSuccN0EqWitness)

      // ── Beta reduction: app(limitFun)(a) = app(G(n0))(a) ───────────────────
      val limitAtAEqGN0 = have(app(G(n0))(a) === app(limitFun)(a)) by Congruence.from(
        have(app(limitFun)(a) === app(G(n0))(a)) by Tautology.from(
          aHeightChar,
          have(LimitKernel.limitIndexDefinitionAt(heightFun, chosenIndexFamily, a)) by Restate,
          have(limitFunDef) by Restate,
          have(LimitKernel.approxAgreementAt(heightFun, approximantFamily, a, limitIndex(a), n0)) by
            Tautology.from(
              ApproximationChainFacts.approximantsAgreeAcrossHeightsAt(
                heightFun,
                approximantFamily,
                limitIndex(a),
                n0,
                a
              )(stabilizationSchema, heightMembershipMonotonicSchema)
            ),
          indexInN,
          aInHeightN0,
          LimitKernel.limitAtHeightAt(
            spec.argType,
            heightFun,
            limitFun,
            approximantFamily,
            chosenIndexFamily,
            a,
            n0
          )
        )
      )

      // ── Witness agreement at a via the shared WitnessAgreement lemma ────────
      // limitFun and G(n0) agree on the height slice h(n0): at each point the
      // limit value is the stabilized approximant value G(n0). This is exactly
      // the slice-agreement premise of WitnessAgreement.witnessAgreementAtSucc.
      val sliceVar = variable[Ind]
      val sliceAgreement = have(
        ∀(sliceVar ∈ app(heightFun)(n0), app(limitFun)(sliceVar) === app(G(n0))(sliceVar))
      ) subproof {
        have((sliceVar ∈ app(heightFun)(n0)) ==> (app(limitFun)(sliceVar) === app(G(n0))(sliceVar))) subproof {
          val vInSlice = assume(sliceVar ∈ app(heightFun)(n0))
          val limitEqApprox = RecursiveAgreement.selfAgreementWithLimit(
            argType = spec.argType,
            heightFun = heightFun,
            limitFun = limitFun,
            approximantFamily = approximantFamily,
            chosenIndexFamily = chosenIndexFamily,
            limitFunDef = limitFunDef,
            termHasHeight = termHasHeight,
            stabilizationSchema = stabilizationSchema,
            heightMembershipMonotonicSchema = heightMembershipMonotonicSchema,
            hValid = hValid,
            currentIndex = n0,
            currentIndexInN = indexInN,
            point = sliceVar,
            pointInHeight = vInSlice
          )
          have(app(limitFun)(sliceVar) === app(G(n0))(sliceVar)) by Restate.from(limitEqApprox)
        }
        thenHave(thesis) by RightForall
      }

      val aInHeightSuccN0 = have(a ∈ app(heightFun)(Succ(n0))) by
        Congruence.from(aInHeightOrd, succEqN0)

      // ∀x ∈ h(Succ n0), W(limitFun)(x) = W(G(n0))(x).
      // n0 = limitIndex(a) mentions the free variable `a`, so we must not rebind
      // `a` here: take the lemma's conclusion verbatim (its bound variable is
      // already renamed away from `a`) and instantiate it at `a`.
      val witnessAgreeLemma = witnessAgreement.witnessAgreementAtSucc.of(
        witnessAgreement.leftFun := limitFun,
        witnessAgreement.rightFun := G(n0),
        witnessAgreement.nVar := n0
      )
      val witnessAgreeOnSucc = have(witnessAgreeLemma.statement.right.head) by Tautology.from(
        witnessAgreeLemma,
        limitHasType,
        gN0HasType,
        indexInN,
        sliceAgreement
      )
      val witnessAgreeImpl = have(
        (a ∈ app(heightFun)(Succ(n0))) ==> (app(recWitness(limitFun))(a) === app(recWitness(G(n0)))(a))
      ) by InstantiateForall(a)(witnessAgreeOnSucc)
      val witnessesAgreeAtA = have(
        app(recWitness(limitFun))(a) === app(recWitness(G(n0)))(a)
      ) by Tautology.from(witnessAgreeImpl, aInHeightSuccN0)

      have(pointwiseGoal) by Tautology.from(
        altEqualityTransitivity of (
          x := app(recWitness(limitFun))(a),
          y := app(recWitness(G(n0)))(a),
          z := app(G(n0))(a)
        ),
        altEqualityTransitivity of (
          x := app(recWitness(limitFun))(a),
          y := app(G(n0))(a),
          z := app(limitFun)(a)
        ),
        witnessesAgreeAtA,
        gN0AtAEqWitness,
        limitAtAEqGN0
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
  // Lemma G — fixedPointExists: ∃f :: A→T, W(f) = f
  // ─────────────────────────────────────────────────────────────────────────

  private val fixedPointExists: THM = Time.measure(s"Ex/fixedPointExists")(Lemma(
    ∃(f, (f :: spec.typ) /\ (recWitness(f) === f))
  ) {
    have(((limitFun :: spec.typ) /\ (recWitness(limitFun) === limitFun))) by
      Tautology.from(limitHasType, limitIsFixedPoint)
    thenHave(thesis) by RightExists
  })

  // ─────────────────────────────────────────────────────────────────────────
  // defAtFixedPoint: (f :: A→T) ∧ W(f) = f ⊢ Def(f)
  // ─────────────────────────────────────────────────────────────────────────

  private val defAtFixedPoint: THM = Time.measure(s"Ex/defAtFixedPoint")(Lemma(
    ((f :: spec.typ) /\ (recWitness(f) === f)) |- spec.untypedDefinition(f)
  ) {

    val fTyped = assume(f :: spec.typ)
    assume(recWitness(f) === f)
    val wfEqF = have(recWitness(f) === f) by Tautology

    val caseFacts = spec.patternMatching.patterns.map(pattern =>
      val vars = pattern.binders
      val body = pattern.body.substitute(spec.selfPlaceholder := f).asInstanceOf[Expr[Ind]]
      val witnessCaseSchema = recWitness.witnessCase(pattern).of(spec.selfPlaceholder := f)

      val allForalls = have(
        forallSeq(vars, pattern.branchPremiseAt(vars) ==> (recWitness(f) * pattern.inputTermAt(vars) === body))
      ) by Tautology.from(fTyped, witnessCaseSchema)

      val instantiated = vars.foldLeft(allForalls)((acc, v) =>
        acc.statement.right.head match
          case forall(_, phi) => thenHave(phi) by InstantiateForall(v)
          case _              => acc
      )

      val appEq = have(recWitness(f) * pattern.inputTermAt(vars) === f * pattern.inputTermAt(vars)) by
        Congruence.from(wfEqF)

      val withF = have(pattern.branchPremiseAt(vars) ==> (f * pattern.inputTermAt(vars) === body)) by
        Congruence.from(instantiated, appEq)

      vars.foldRight(withF)((v, acc) =>
        thenHave(∀(v, acc.statement.right.head)) by RightForall
      )
    ).toSeq

    have(thesis) by Tautology.from((fTyped +: caseFacts)*)
  })

  // ─────────────────────────────────────────────────────────────────────────
  // witnessExists: ∃f, Def(f)
  // ─────────────────────────────────────────────────────────────────────────

  val witnessExists: THM = Lemma(∃(f, spec.untypedDefinition(f))) {

    have(((f :: spec.typ) /\ (recWitness(f) === f)) |- spec.untypedDefinition(f)) by
      Restate.from(defAtFixedPoint)
    thenHave(((f :: spec.typ) /\ (recWitness(f) === f)) |- ∃(f, spec.untypedDefinition(f))) by
      RightExists
    thenHave(∃(f, (f :: spec.typ) /\ (recWitness(f) === f)) |- ∃(f, spec.untypedDefinition(f))) by
      LeftExists

    have(thesis) by Cut(fixedPointExists, lastStep)
  }
}
