package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.{specializeFormula, specializeTerm}
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.{altEqualityTransitivity, equivalenceRevApply, equivalenceApply}
import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.NatFacts
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.NatFacts.Succ
import lisa.maths.SetTheory.Types.ADTv2.support.core.InstantiateForallSeq
import lisa.maths.SetTheory.Types.ADTv2.support.Time

import lisa.maths.SetTheory.Base.Subset
import lisa.maths.SetTheory.Functions.BasicTheorems.{funcBetweenEqInFuncSpace, functionalExtentionality}
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Ordinals.TransitiveSet
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.TypingHelpers.*
import lisa.maths.SetTheory.Types.TypingRules.BetaReduction //On

import lisa.maths.Quantifiers
import lisa.utils.prooflib.BasicStepTactic.{LeftExists, Cut, RightForall}
import lisa.utils.prooflib.ProofTacticLib.Arity

import ApproxPropShared.{constructorBranchesAtHeight, constructorDisjunctionAtHeight, specializedConstructors}

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
  val approxProp: ApproxProp[N]
) {

  val nVar = variable[Ind]
  val mVar = variable[Ind]
  val kVar = variable[Ind]
  private val constructorsAt = specializedConstructors(spec.adt.constructors, spec.typeSubstitutions)
  private val heightSuccStrong = spec.adt.height.successorStrongAt(spec.typeSubstitutions)
  private val heightSuccessorInclusion = spec.adt.height.successorInclusionAt(spec.typeSubstitutions)
  private val termHasHeight    = spec.adt.height.termHasHeightAt(spec.typeSubstitutions)
  
  import approx.G
  import approxProp.{
    heightFun, heightFunValid, isHeightPred,
    approximantsAgreeFromSubset, approximantsAgreeAcrossHeights,
    limitFun, limitHasType, limitIndex
  }

  // ─────────────────────────────────────────────────────────────────────────
  // Lemma F — limitIsFixedPoint: W(limitFun) = limitFun
  // ─────────────────────────────────────────────────────────────────────────

  private val limitIsFixedPoint: THM = Time.measure(s"limitIsFixedPoint for ${spec.functionName}")(Lemma(recWitness(limitFun) === limitFun) {
    val hValid = have(isHeightPred(heightFun)) by Restate.from(heightFunValid)

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

      // ── Height index for a ──────────────────────────────────────────────────
      val hasSomeHeight = have(∃(nVar, (nVar ∈ N) /\ (a ∈ app(heightFun)(nVar)))) by Tautology.from(
        hValid,
        aInArgType,
        termHasHeight of (x := a, h := heightFun),
        equivalenceApply of (p1 := in(a, spec.argType), p2 := ∃(nVar, in(nVar, N) /\ in(a, app(heightFun)(nVar))))
      )
      val indexWitness = have(
        (limitIndex(a) ∈ N) /\ (a ∈ app(heightFun)(limitIndex(a)))
      ) by Cut(
        hasSomeHeight,
        Quantifiers.existsEpsilon.of(x := nVar, P := λ(nVar, (nVar ∈ N) /\ (a ∈ app(heightFun)(nVar))))
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

      // ── Decompose a into constructor form ───────────────────────────────────
      val constructorBranch =
        constructorBranchesAtHeight(constructorsAt, app(heightFun)(n0), a)
      val constructorDisjunction =
        constructorDisjunctionAtHeight(constructorsAt, app(heightFun)(n0), a)

      val decomposeAtA = have(constructorDisjunction) by Tautology.from(
        hValid,
        indexInN,
        aInHeightOrd,
        heightSuccStrong of (h := heightFun, n := n0, x := a),
        equivalenceApply of (p1 := in(a, app(heightFun)(successor(n0))), p2 := constructorDisjunction)
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
        approximantsAgreeFromSubset.of(nVar := n0, mVar := Succ(n0))
      )
      val gN0AtAEqWitness = have(app(recWitness(G(n0)))(a) === app(G(n0))(a)) by
        Congruence.from(stabAtAFact, gSuccN0EqWitness)

      // ── Beta reduction: app(limitFun)(a) = app(G(n0))(a) ───────────────────
      val limitAtAEqGN0 = have(app(G(n0))(a) === app(limitFun)(a)) by
        Tautology.from(
          aInArgType,
          BetaReduction of (T := spec.argType, e := λ(a, app(G(limitIndex(a)))(a)), e2 := a)
        )

      // ── Per-constructor branches ────────────────────────────────────────────
      val branchEqualities = constructorsAt.map(sc =>
        val c = sc.underlying
        val constructorPatterns = spec.patternMatching.patternsFor(c)

        val directBranch = have(
          sc.branchPremiseAtHeight(app(heightFun)(n0), a) |- pointwiseGoal
        ) subproof {
          assume(sc.branchPremiseAtHeight(app(heightFun)(n0), a))
          val branchPremise = have(sc.branchPremiseAtHeight(app(heightFun)(n0), a)) by Hypothesis
          val argsTypedAtHeight =
            have(sc.heightTypingFormula(app(heightFun)(n0))) by Tautology
          val argsTypedSemantic = have(wellTypedFormula(sc.semanticSignature2)) by
            Tautology.from(
              hValid,
              indexInN,
              argsTypedAtHeight,
              sc.semanticTypingFromHeight(heightFun, n0)
            )
          val aEqApplied = have(a === sc.appliedTerm2) by
            Tautology.from(
              hValid,
              indexInN,
              branchPremise,
              sc.appliedEqualityFromStructural(heightFun, n0, a)
            )

          // Recursive arg equalities: app(limitFun)(v) = app(G(n0))(v) for each SelfRef v
          val selfArgEqualities = sc.selfRefVariables2.map(v =>
              val vInHn0 = have(v ∈ app(heightFun)(n0)) by Tautology.from(argsTypedAtHeight)

              // v ∈ spec.argType
              val vExistsHeight = have(
                ∃(nVar, (nVar ∈ N) /\ (v ∈ app(heightFun)(nVar)))
              ) subproof {
                have((n0 ∈ N) /\ (v ∈ app(heightFun)(n0))) by Tautology.from(indexInN, vInHn0)
                thenHave(thesis) by RightExists
              }
              val vInArgType = have(v ∈ spec.argType) by Tautology.from(
                hValid,
                vExistsHeight,
                termHasHeight of (x := v, h := heightFun),
                equivalenceRevApply of (
                  p1 := in(v, spec.argType),
                  p2 := ∃(nVar, in(nVar, N) /\ in(v, app(heightFun)(nVar)))
                )
              )

              // app(limitFun)(v) = app(G(limitIndex(v)))(v) by beta reduction
              val limitAtVEqGLV = have(app(limitFun)(v) === app(G(limitIndex(v)))(v)) by
                Tautology.from(
                  vInArgType,
                  BetaReduction of (T := spec.argType, e := λ(a, app(G(limitIndex(a)))(a)), e2 := v)
                )

              // limitIndex(v) ∈ N, v ∈ h(limitIndex(v))
              val vIndexWitness = have(
                (limitIndex(v) ∈ N) /\ (v ∈ app(heightFun)(limitIndex(v)))
              ) by Cut(
                vExistsHeight,
                Quantifiers.existsEpsilon.of(x := nVar, P := λ(nVar, (nVar ∈ N) /\ (v ∈ app(heightFun)(nVar))))
              )
              val vIndexInN = have(limitIndex(v) ∈ N) by Tautology.from(vIndexWitness)
              val vInHLV = have(v ∈ app(heightFun)(limitIndex(v))) by Tautology.from(vIndexWitness)

              // app(G(limitIndex(v)))(v) = app(G(n0))(v) by approximantsAgreeAcrossHeights
              val agreeGLVGN0 = have(app(G(limitIndex(v)))(v) === app(G(n0))(v)) by Tautology.from(
                vIndexInN,
                indexInN,
                vInHLV,
                vInHn0,
                approximantsAgreeAcrossHeights.of(nVar := limitIndex(v), mVar := n0, a := v)
              )

              // Combine: app(limitFun)(v) = app(G(n0))(v)
              have(app(limitFun)(v) === app(G(n0))(v)) by Tautology.from(
                altEqualityTransitivity of (x := app(limitFun)(v), y := app(G(limitIndex(v)))(v), z := app(G(n0))(v)),
                limitAtVEqGLV,
                  agreeGLVGN0
              )
          )

          val selectionSchema = spec.patternMatching.branchSelectionFor(c, a)
          val selectionSchemaInContext = have(selectionSchema.statement.right.head) by
            Tautology.from(selectionSchema)
          val selectionAtCtorVars = have(
            (wellTypedFormula(sc.semanticSignature2) /\ (a === sc.appliedTerm2)) |-
              seqOr(constructorPatterns.map(pattern =>
                pattern.freshBranchCondition /\ (a === pattern.freshInputTerm)
              ))
          ) by InstantiateForallSeq(c.variables2)(selectionSchemaInContext)
          val selectedBranch = have(
            seqOr(constructorPatterns.map(pattern =>
              pattern.freshBranchCondition /\ (a === pattern.freshInputTerm)
            ))
          ) by Tautology.from(selectionAtCtorVars, argsTypedSemantic, aEqApplied)

          val patternEqualities = constructorPatterns.map(pattern =>
            have(
              (pattern.freshBranchCondition /\ (a === pattern.freshInputTerm)) |- pointwiseGoal
            ) subproof {
              val selectedPattern = assume(pattern.freshBranchCondition /\ (a === pattern.freshInputTerm))
              val patternGuard = have(pattern.freshBranchCondition) by Tautology.from(selectedPattern)
              val aEqPattern = have(a === pattern.freshInputTerm) by Tautology.from(selectedPattern)
              val patternPremise = have(pattern.freshBranchPremise) by Tautology.from(
                argsTypedSemantic,
                patternGuard
              )
              val witnessesAgreeAtA = WitnessCaseExtensionality.proveOnSelectedPattern(
                spec = spec,
                recWitness = recWitness,
                pattern = pattern,
                ambientTerm = a,
                leftSelf = limitFun,
                rightSelf = G(n0),
                leftSelfTyped = limitHasType,
                rightSelfTyped = gN0HasType,
                patternPremise = patternPremise,
                ambientEqInput = aEqPattern,
                selfArgEqualities = selfArgEqualities
              )

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
          )

          val branchesToGoal =
            if patternEqualities.size == 1 then
              have(selectedBranch.statement.right.head |- pointwiseGoal) by Restate.from(patternEqualities.head)
            else
              have(selectedBranch.statement.right.head |- pointwiseGoal) by LeftOr(patternEqualities*)

          have(pointwiseGoal) by Cut(selectedBranch, branchesToGoal)
        }
        ConstructorCaseAssembly.liftConstructorCase(
          sc = sc,
          heightSet = app(heightFun)(n0),
          ambientTerm = a,
          goal = pointwiseGoal,
          directBranch = directBranch
        )
      )

      ConstructorCaseAssembly.assemblePointwiseFromConstructors(
        constructorDisjunction = constructorDisjunction,
        decomposeFact = decomposeAtA,
        constructorFacts = branchEqualities,
        antecedent = a ∈ spec.argType,
        goal = pointwiseGoal
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

  private val fixedPointExists: THM = Time.measure(s"fixedPointExists for ${spec.functionName}")(Lemma(
    ∃(f, (f :: spec.typ) /\ (recWitness(f) === f))
  ) {
    have(((limitFun :: spec.typ) /\ (recWitness(limitFun) === limitFun))) by
      Tautology.from(limitHasType, limitIsFixedPoint)
    thenHave(thesis) by RightExists
  })

  // ─────────────────────────────────────────────────────────────────────────
  // defAtFixedPoint: (f :: A→T) ∧ W(f) = f ⊢ Def(f)
  // ─────────────────────────────────────────────────────────────────────────

  private val defAtFixedPoint: THM = Time.measure(s"defAtFixedPoint for ${spec.functionName}")(Lemma(
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

  val witnessExists: THM = Time.measure(s"witnessExists for ${spec.functionName}")(Lemma(∃(f, spec.untypedDefinition(f))) {

    have(((f :: spec.typ) /\ (recWitness(f) === f)) |- spec.untypedDefinition(f)) by
      Restate.from(defAtFixedPoint)
    thenHave(((f :: spec.typ) /\ (recWitness(f) === f)) |- ∃(f, spec.untypedDefinition(f))) by
      RightExists
    thenHave(∃(f, (f :: spec.typ) /\ (recWitness(f) === f)) |- ∃(f, spec.untypedDefinition(f))) by
      LeftExists

    have(thesis) by Cut(fixedPointExists, lastStep)
  })
}
