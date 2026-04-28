package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Types.ADTv2.support.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.UsefulTheorems.{altEqualityTransitivity, equivalenceRevApply, equivalenceApply}
import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.ADTv2.recursion.Nums.Succ

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

  private val heightSuccStrong = spec.adt.externalHeightSuccessorStrong
  private val heightMonotonic  = spec.adt.externalHeightMonotonic
  private val termHasHeight    = spec.adt.externalTermHasHeight
  
  import approx.G
  import approxProp.{
    heightFun, heightFunValid, isHeightPred,
    approximantsAgreeFromSubset, approximantsAgreeAcrossHeights,
    limitFun, limitHasType, limitIndex
  }

  // ─────────────────────────────────────────────────────────────────────────
  // Lemma F — limitIsFixedPoint: W(limitFun) = limitFun
  // ─────────────────────────────────────────────────────────────────────────

  private val limitIsFixedPoint: THM = Lemma(recWitness(limitFun) === limitFun) {
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

      val succN0InN   = have(Succ(n0) ∈ N)   by Tautology.from(indexInN, Nums.succIntro.of(n := n0))
      val succEqN0    = have(Succ(n0) === successor(n0)) by
        Tautology.from(Nums.Succ.definition of (x := n0))

      // n0 ⊆ Succ(n0)  (n0 ∈ Succ(n0) + Succ(n0) is transitive)
      val n0InSuccN0 = have(n0 ∈ Succ(n0)) by Weakening(Nums.nInSucc.of(n := n0))
      val succN0Trans = have(TransitiveSet.transitiveSet(Succ(n0))) by
        Tautology.from(succN0InN, Nums.elementsTransitive.of(n := Succ(n0)))
      val n0SubSuccN0 = have(n0 ⊆ Succ(n0)) by Tautology.from(
        n0InSuccN0,
        succN0Trans,
        TransitiveSet.elementIsSubset.of(A := Succ(n0), x := n0)
      )

      // h(n0) ⊆ h(Succ(n0))  (heightMonotonic)
      val hN0SubHSuccN0 = have(app(heightFun)(n0) ⊆ app(heightFun)(Succ(n0))) by Tautology.from(
        hValid,
        succN0InN,
        indexInN,
        n0SubSuccN0,
        heightMonotonic of (h := heightFun, n := Succ(n0), m := n0)
      )

      // a ∈ h(Succ(n0))
      val aInHeightSuccN0 = have(a ∈ app(heightFun)(Succ(n0))) by Tautology.from(
        hN0SubHSuccN0,
        aInHeightN0,
        Subset.membership of (x := app(heightFun)(n0), y := app(heightFun)(Succ(n0)), z := a)
      )
      val aInHeightOrd = have(a ∈ app(heightFun)(successor(n0))) by
        Congruence.from(aInHeightSuccN0, succEqN0)

      // ── Decompose a into constructor form ───────────────────────────────────
      val constructorBranch = spec.adt.constructors.map(c =>
        c -> existsSeq(
          c.variables2,
          wellTypedFormula(c.underlying.signature2)(app(heightFun)(n0)) /\ (a === c.structuralTerm2)
        )
      ).toMap
      val constructorDisjunction = seqOr(spec.adt.constructors.map(c => constructorBranch(c)))

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
      val gN0AtAEqWitness = have(app(G(n0))(a) === app(recWitness(G(n0)))(a)) by
        Congruence.from(stabAtAFact, gSuccN0EqWitness)

      // ── Beta reduction: app(limitFun)(a) = app(G(n0))(a) ───────────────────
      val limitAtAEqGN0 = have(app(limitFun)(a) === app(G(n0))(a)) by
        Tautology.from(
          aInArgType,
          BetaReduction of (T := spec.argType, e := λ(a, app(G(limitIndex(a)))(a)), e2 := a)
        )

      // ── Per-constructor branches ────────────────────────────────────────────
      val branchEqualities = spec.adt.constructors.map(c =>
        val (caseVars, rawBody) = spec.rawCases(c)
        val bodyAtLimitFun = rawBody
          .substitute(spec.selfPlaceholder := limitFun)
          .substitute(caseVars.zip(c.variables2).map((from, to) => from := to)*)
          .asInstanceOf[Expr[Ind]]
        val bodyAtGN0 = rawBody
          .substitute(spec.selfPlaceholder := G(n0))
          .substitute(caseVars.zip(c.variables2).map((from, to) => from := to)*)
          .asInstanceOf[Expr[Ind]]

        val directBranch = have(
          wellTypedFormula(c.underlying.signature2)(app(heightFun)(n0)) /\ (a === c.structuralTerm2) |- pointwiseGoal
        ) subproof {
          assume(wellTypedFormula(c.underlying.signature2)(app(heightFun)(n0)) /\ (a === c.structuralTerm2))
          val argsTypedAtHeight =
            have(wellTypedFormula(c.underlying.signature2)(app(heightFun)(n0))) by Tautology
          val aEqStructural = have(a === c.structuralTerm2) by Tautology

          // Upgrade typing to term/semantic level
          val exTypedAtHeight = have(
            ∃(kVar, (kVar ∈ N) /\ wellTypedFormula(c.underlying.signature2)(app(heightFun)(kVar)))
          ) subproof {
            have((n0 ∈ N) /\ wellTypedFormula(c.underlying.signature2)(app(heightFun)(n0))) by
              Tautology.from(indexInN, argsTypedAtHeight)
            thenHave(thesis) by RightExists
          }
          val termsHaveHeightAtH = have(
            wellTypedFormula(c.underlying.signature2)(spec.adt.term) <=>
              ∃(kVar, (kVar ∈ N) /\ wellTypedFormula(c.underlying.signature2)(app(heightFun)(kVar)))
          ) by Tautology.from(
            hValid,
            spec.adt.externalTermsHaveHeight(c.underlying).of(h := heightFun)
              .of(c.underlying.variables.zip(c.underlying.variables2).map((from, to) => from := to)*)
          )
          val argsTypedAtTerm = have(wellTypedFormula(c.underlying.signature2)(spec.adt.term)) by
            Tautology.from(termsHaveHeightAtH, exTypedAtHeight)
          val argsTypedSemantic = have(wellTypedFormula(c.semanticSignature2)) by
            Restate.from(argsTypedAtTerm)

          // a = c.appliedTerm2
          val shortBase = have(c.shortDefinition.statement.right.head) by Tautology.from(c.shortDefinition)
          val shortAtVars2 = c.variables2.foldLeft(shortBase)((_, v2) =>
            lastStep.statement.right.head match
              case forall(v, phi) =>
                thenHave(phi.substituteUnsafe(Map(v -> v2)).asInstanceOf[Expr[Prop]]) by InstantiateForall(v2)
              case _ => throw UnreachableException
          )
          val appliedEqStructural = shortAtVars2.statement.right.head match
            case _ ==> consequent =>
              have(consequent) by Tautology.from(shortAtVars2, argsTypedSemantic)
            case _ => throw UnreachableException
          val structuralEqApplied = have(c.structuralTerm2 === c.appliedTerm2) by
            Congruence.from(appliedEqStructural)
          val aEqApplied = have(a === c.appliedTerm2) by Tautology.from(
            altEqualityTransitivity of (x := a, y := c.structuralTerm2, z := c.appliedTerm2),
            aEqStructural,
            structuralEqApplied
          )

          // Recursive arg equalities: app(limitFun)(v) = app(G(n0))(v) for each SelfRef v
          val selfArgEqualities = c.syntacticSignature(c.variables2).collect {
            case (v, lisa.maths.SetTheory.Types.ADTv2.syntax.AST.SelfRef) =>
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
          }

          // body_c[limitFun] = body_c[G(n0)]  (Congruence from recursive arg equalities)
          val bodyEq =
            if selfArgEqualities.isEmpty then have(bodyAtLimitFun === bodyAtGN0) by RightRefl
            else have(bodyAtLimitFun === bodyAtGN0) by Congruence.from(selfArgEqualities*)

          // recWitness(limitFun)(c(x̄)) = bodyAtLimitFun
          val witnessCaseLimitSchema = recWitness.witnessCaseByConstructor(c).of(spec.selfPlaceholder := limitFun)
          val witnessCaseLimitBase = witnessCaseLimitSchema.statement.right.head match
            case _ ==> consequent =>
              have(consequent) by Tautology.from(witnessCaseLimitSchema, limitHasType)
            case _ => throw UnreachableException
          val witnessCaseLimitAtVars2 = c.variables2.foldLeft(witnessCaseLimitBase)((_, v2) =>
            lastStep.statement.right.head match
              case forall(v, phi) =>
                thenHave(phi.substituteUnsafe(Map(v -> v2)).asInstanceOf[Expr[Prop]]) by InstantiateForall(v2)
              case _ => throw UnreachableException
          )
          val witnessAtLimitAtCtor = witnessCaseLimitAtVars2.statement.right.head match
            case _ ==> consequent =>
              have(consequent) by Tautology.from(witnessCaseLimitAtVars2, argsTypedSemantic)
            case _ => throw UnreachableException
          // witnessAtLimitAtCtor: app(recWitness(limitFun))(c.appliedTerm2) === bodyAtLimitFun

          // recWitness(G(n0))(c(x̄)) = bodyAtGN0
          val witnessCaseGN0Schema = recWitness.witnessCaseByConstructor(c).of(spec.selfPlaceholder := G(n0))
          val witnessCaseGN0Base = witnessCaseGN0Schema.statement.right.head match
            case _ ==> consequent =>
              have(consequent) by Tautology.from(witnessCaseGN0Schema, gN0HasType)
            case _ => throw UnreachableException
          val witnessCaseGN0AtVars2 = c.variables2.foldLeft(witnessCaseGN0Base)((_, v2) =>
            lastStep.statement.right.head match
              case forall(v, phi) =>
                thenHave(phi.substituteUnsafe(Map(v -> v2)).asInstanceOf[Expr[Prop]]) by InstantiateForall(v2)
              case _ => throw UnreachableException
          )
          val witnessAtGN0AtCtor = witnessCaseGN0AtVars2.statement.right.head match
            case _ ==> consequent =>
              have(consequent) by Tautology.from(witnessCaseGN0AtVars2, argsTypedSemantic)
            case _ => throw UnreachableException
          // witnessAtGN0AtCtor: app(recWitness(G(n0)))(c.appliedTerm2) === bodyAtGN0

          // ── Chain: app(recWitness(limitFun))(a) = app(limitFun)(a) ────────────
          val step1 = have(app(recWitness(limitFun))(a) === app(recWitness(limitFun))(c.appliedTerm2)) by
            Congruence.from(aEqApplied)
          val step2 = have(app(recWitness(limitFun))(a) === bodyAtLimitFun) by Tautology.from(
            altEqualityTransitivity of (
              x := app(recWitness(limitFun))(a),
              y := app(recWitness(limitFun))(c.appliedTerm2),
              z := bodyAtLimitFun
            ),
            step1,
            witnessAtLimitAtCtor
          )
          val step3 = have(app(recWitness(limitFun))(a) === bodyAtGN0) by Tautology.from(
            altEqualityTransitivity of (
              x := app(recWitness(limitFun))(a), y := bodyAtLimitFun, z := bodyAtGN0
            ),
            step2, bodyEq
          )
          val step4 = have(bodyAtGN0 === app(recWitness(G(n0)))(c.appliedTerm2)) by
            Congruence.from(witnessAtGN0AtCtor)
          val step5 = have(app(recWitness(limitFun))(a) === app(recWitness(G(n0)))(c.appliedTerm2)) by
            Tautology.from(
              altEqualityTransitivity of (
                x := app(recWitness(limitFun))(a), y := bodyAtGN0, z := app(recWitness(G(n0)))(c.appliedTerm2)
              ),
              step3, step4
            )
          val step6 = have(app(recWitness(G(n0)))(c.appliedTerm2) === app(recWitness(G(n0)))(a)) by
            Congruence.from(aEqApplied)
          val step7 = have(app(recWitness(limitFun))(a) === app(recWitness(G(n0)))(a)) by Tautology.from(
            altEqualityTransitivity of (
              x := app(recWitness(limitFun))(a),
              y := app(recWitness(G(n0)))(c.appliedTerm2),
              z := app(recWitness(G(n0)))(a)
            ),
            step5, step6
          )
          val step8 = have(app(recWitness(G(n0)))(a) === app(G(n0))(a)) by
            Congruence.from(gN0AtAEqWitness)
          val step9 = have(app(recWitness(limitFun))(a) === app(G(n0))(a)) by Tautology.from(
            altEqualityTransitivity of (
              x := app(recWitness(limitFun))(a), y := app(recWitness(G(n0)))(a), z := app(G(n0))(a)
            ),
            step7, step8
          )
          val step10 = have(app(G(n0))(a) === app(limitFun)(a)) by Congruence.from(limitAtAEqGN0)

          have(pointwiseGoal) by Tautology.from(
            altEqualityTransitivity of (
              x := app(recWitness(limitFun))(a), y := app(G(n0))(a), z := app(limitFun)(a)
            ),
            step9, step10
          )
        }

        val rawBranch = c.variables2.reverse.foldLeft(directBranch)((fact, v) =>
          thenHave(∃(v, fact.statement.left.head) |- pointwiseGoal) by LeftExists
        )
        have(constructorBranch(c) |- pointwiseGoal) by Tautology.from(rawBranch)
      )

      val branchesToGoal =
        if branchEqualities.size == 1 then
          have(constructorDisjunction |- pointwiseGoal) by Restate.from(branchEqualities.head)
        else
          have(constructorDisjunction |- pointwiseGoal) by LeftOr(branchEqualities*)

      have(pointwiseGoal) by Cut(decomposeAtA, branchesToGoal)
      thenHave(thesis) by RightImplies.withParameters(a ∈ spec.argType, pointwiseGoal)
    }

    thenHave(∀(a, (a ∈ spec.argType) ==> pointwiseGoal)) by RightForall

    have(recWitness(limitFun) === limitFun) by Tautology.from(
      witnessAtLimitBetween,
      limitBetween,
      lastStep,
      functionalExtentionality of (f := recWitness(limitFun), g := limitFun, A := spec.argType, B := spec.returnType)
    )
    thenHave(thesis) by Restate
  }

  // ─────────────────────────────────────────────────────────────────────────
  // Lemma G — fixedPointExists: ∃f :: A→T, W(f) = f
  // ─────────────────────────────────────────────────────────────────────────

  private val fixedPointExists: THM = Lemma(
    ∃(f, (f :: spec.typ) /\ (recWitness(f) === f))
  ) {
    have(((limitFun :: spec.typ) /\ (recWitness(limitFun) === limitFun))) by
      Tautology.from(limitHasType, limitIsFixedPoint)
    thenHave(thesis) by RightExists
  }

  // ─────────────────────────────────────────────────────────────────────────
  // defAtFixedPoint: (f :: A→T) ∧ W(f) = f ⊢ Def(f)
  // ─────────────────────────────────────────────────────────────────────────

  private val defAtFixedPoint: THM = Lemma(
    ((f :: spec.typ) /\ (recWitness(f) === f)) |- spec.untypedDefinition(f)
  ) {

    val fTyped = assume(f :: spec.typ)
    assume(recWitness(f) === f)
    val wfEqF = have(recWitness(f) === f) by Tautology

    val caseFacts = spec.adt.constructors.map(c =>
      val (vars, rawBody) = spec.rawCases(c)
      val body = rawBody.substitute(spec.selfPlaceholder := f).asInstanceOf[Expr[Ind]]
      val witnessCaseSchema = recWitness.witnessCaseByConstructor(c).of(spec.selfPlaceholder := f)

      val allForalls = have(
        forallSeq(vars, wellTypedFormula(c.semanticSignature(vars)) ==> (recWitness(f) * c.appliedTerm(vars) === body))
      ) by Tautology.from(fTyped, witnessCaseSchema)

      val instantiated = vars.foldLeft(allForalls)((acc, v) =>
        acc.statement.right.head match
          case forall(_, phi) => thenHave(phi) by InstantiateForall(v)
          case _              => acc
      )

      val appEq = have(recWitness(f) * c.appliedTerm(vars) === f * c.appliedTerm(vars)) by
        Congruence.from(wfEqF)

      val withF = have(wellTypedFormula(c.semanticSignature(vars)) ==> (f * c.appliedTerm(vars) === body)) by
        Congruence.from(instantiated, appEq)

      vars.foldRight(withF)((v, acc) =>
        thenHave(∀(v, acc.statement.right.head)) by RightForall
      )
    ).toSeq

    have(thesis) by Tautology.from((fTyped +: caseFacts)*)
  }

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
