package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.{altEqualityTransitivity, equivalenceApply, unionOfTwoNats}
import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.NatFacts
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.NatFacts.{Zero, Succ}

import lisa.maths.SetTheory.Base.{Union, Comprehension,FoundationAxiom,Subset}
import lisa.maths.SetTheory.Base.Comprehension.{|}
import lisa.maths.SetTheory.Base.Union.∪
import lisa.maths.SetTheory.Functions.BasicTheorems.{appTyping, funcBetweenEqInFuncSpace}
import lisa.maths.SetTheory.Functions.Function.abs
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Ordinals.TransitiveSet
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.TypingHelpers.*
import lisa.maths.SetTheory.Types.TypingRules.TAbs

import lisa.maths.Quantifiers
import lisa.utils.prooflib.BasicStepTactic.{LeftExists, Cut}
import lisa.utils.prooflib.ProofTacticLib.Arity

import ApproxPropShared.{TAbsConstOn, constructorBranchesAtHeight, constructorDisjunctionAtHeight, subsetBelowSuccN, substitutedCaseBody}

/**
 * Approximant properties.
 *
 * Proves stabilization of the approximant sequence and constructs the limit function:
 *
 *   stabilization : ∀n ∈ ω, ∀a ∈ h(n), G(n)(a) = G(Succ(n))(a)
 *   limitFun      : λ(a). G(ε n. a ∈ h(n))(a)
 *   limitHasType  : limitFun :: spec.typ
 *
 * Exports:
 *   - [[heightFun]], [[heightFunValid]]
 *   - [[approximantsAgreeFromSubset]], [[approximantsAgreeAcrossHeights]]
 *   - [[limitFun]], [[limitHasType]]
 */
private[recursion] final class ApproxProp[N <: Arity](
  val spec: FunSpec[N],
  val recWitness: Witness[N],
  val approx: Approx[N]
) {

  val nVar = variable[Ind]
  val mVar = variable[Ind]
  val kVar = variable[Ind]
  import approx.G

  // ─────────────────────────────────────────────────────────────────────────
  // Height function — ε-chosen concrete height function
  // ─────────────────────────────────────────────────────────────────────────

  def isHeightPred(hh: Expr[Ind]): Expr[Prop] = spec.adt.height.predicate(hh)

  val heightFun: Expr[Ind] = spec.adt.height.function

  val heightFunValid: THM = spec.adt.height.valid

  private val heightSuccStrong = spec.adt.height.successorStrong
  private val heightMonotonic  = spec.adt.height.monotonic
  private val termHasHeight    = spec.adt.height.termHasHeight

  private val predVar = variable[Ind >>: Prop]

  // ─────────────────────────────────────────────────────────────────────────
  // Lemma D — stabilization
  // ∀n ∈ ω, ∀a ∈ h(n), G(n)(a) = G(Succ(n))(a)
  // ─────────────────────────────────────────────────────────────────────────

  private val stabilization: THM = Lemma(
    ∀(nVar ∈ N, ∀(a ∈ app(heightFun)(nVar), app(G(nVar))(a) === app(G(Succ(nVar)))(a)))
  ) {
    val Pred = variable[Ind >>: Prop]
    val P = λ(nVar, ∀(a ∈ app(heightFun)(nVar), app(G(nVar))(a) === app(G(Succ(nVar)))(a)))

    val hValid = have(isHeightPred(heightFun)) by Weakening(heightFunValid)

    val zeroDef = have(Zero === ∅) by Restate.from(Zero.definition)
    val noElemAtEmpty = have(!in(a, app(heightFun)(∅))) by Cut(
      hValid,
      spec.adt.height.zero of (h := heightFun, x := a)
    )
    val noElemAtZero = have(!in(a, app(heightFun)(Zero))) by Congruence.from(noElemAtEmpty, zeroDef)

    val base = have(P(Zero)) subproof {
      have(a ∈ app(heightFun)(Zero) |- app(G(Zero))(a) === app(G(Succ(Zero)))(a)) by
        Tautology.from(noElemAtZero)
      thenHave(
        (a ∈ app(heightFun)(Zero)) ==> (app(G(Zero))(a) === app(G(Succ(Zero)))(a))
      ) by RightImplies
      thenHave(
        ∀(a, (a ∈ app(heightFun)(Zero)) ==> (app(G(Zero))(a) === app(G(Succ(Zero)))(a)))
      ) by RightForall
      thenHave(thesis) by Restate
    }

    val step = have(∀(nVar, (nVar ∈ N) ==> (P(nVar) ==> P(Succ(nVar))))) subproof {
      have((nVar ∈ N) ==> (P(nVar) ==> P(Succ(nVar)))) subproof {
        val nInN = assume(nVar ∈ N)
        val ih     = assume(P(nVar))

        val succEq = have(Succ(nVar) === successor(nVar)) by
          Tautology.from(Succ.definition of (x := nVar))

        val pointwiseAtSucc = have(
          (a ∈ app(heightFun)(Succ(nVar))) ==> (app(G(Succ(nVar)))(a) === app(G(Succ(Succ(nVar))))(a))
        ) subproof {
          val goalAtA = app(G(Succ(nVar)))(a) === app(G(Succ(Succ(nVar))))(a)
          val aInHeightSucc = assume(a ∈ app(heightFun)(Succ(nVar)))

          val aInHeightOrd = have(a ∈ app(heightFun)(successor(nVar))) by
            Congruence.from(aInHeightSucc, succEq)

          val constructorBranch =
            constructorBranchesAtHeight(spec.adt.constructors, app(heightFun)(nVar), a)

          val constructorDisjunction =
            constructorDisjunctionAtHeight(spec.adt.constructors, app(heightFun)(nVar), a)

          val decomposeAtA = have(constructorDisjunction) by Tautology.from(
            hValid,
            nInN,
            aInHeightOrd,
            heightSuccStrong of (h := heightFun, n := nVar, x := a),
            equivalenceApply of (
              p1 := in(a, app(heightFun)(successor(nVar))),
              p2 := constructorDisjunction
            )
          )

          val succInN = have(Succ(nVar) ∈ N) by
            Tautology.from(nInN, NatFacts.succIntro.of(n := nVar))

          val approxSuccAtN = have(nVar ∈ N ==> (G(Succ(nVar)) === recWitness(G(nVar)))) by
            InstantiateForall(nVar)(approx.approxSucc)
          val gSuccEq = have(G(Succ(nVar)) === recWitness(G(nVar))) by
            Tautology.from(nInN, approxSuccAtN)

          val approxSuccAtSuccN = have(
            Succ(nVar) ∈ N ==> (G(Succ(Succ(nVar))) === recWitness(G(Succ(nVar))))
          ) by InstantiateForall(Succ(nVar))(approx.approxSucc)
          val gSuccSuccEq = have(G(Succ(Succ(nVar))) === recWitness(G(Succ(nVar)))) by
            Tautology.from(succInN, approxSuccAtSuccN)

          val approxTypeAtN = have(nVar ∈ N ==> (G(nVar) :: spec.typ)) by
            InstantiateForall(nVar)(approx.approxHasType)
          val gNHasType = have(G(nVar) :: spec.typ) by Tautology.from(nInN, approxTypeAtN)
          val approxTypeAtSuccN = have(Succ(nVar) ∈ N ==> (G(Succ(nVar)) :: spec.typ)) by
            InstantiateForall(Succ(nVar))(approx.approxHasType)
          val gSuccHasType = have(G(Succ(nVar)) :: spec.typ) by Tautology.from(
            succInN,
            approxTypeAtSuccN
          )

          val branchEqualities = spec.adt.constructors.map(c =>
            val bodyAtGn = substitutedCaseBody(spec, c, G(nVar))
            val bodyAtGSucc = substitutedCaseBody(spec, c, G(Succ(nVar)))

            val directBranch = have(
              c.branchPremiseAtHeight(app(heightFun)(nVar), a) |- goalAtA
            ) subproof {
              assume(c.branchPremiseAtHeight(app(heightFun)(nVar), a))
              val branchPremise = have(c.branchPremiseAtHeight(app(heightFun)(nVar), a)) by Hypothesis
              val argsTypedAtHeight = have(c.heightTypingFormula(app(heightFun)(nVar))) by Tautology
              val argsTypedSemantic = have(wellTypedFormula(c.semanticSignature2)) by
                Tautology.from(
                  hValid,
                  nInN,
                  argsTypedAtHeight,
                  c.semanticTypingFromHeight(heightFun, nVar)
                )
              val aEqApplied = have(a === c.appliedTerm2) by
                Tautology.from(
                  hValid,
                  nInN,
                  branchPremise,
                  c.appliedEqualityFromStructural(heightFun, nVar, a)
                )

              val selfArgEqualities = c.selfRefVariables2.map(v =>
                  val ihAtN = have(
                    ∀(a, (a ∈ app(heightFun)(nVar)) ==> (app(G(nVar))(a) === app(G(Succ(nVar)))(a)))
                  ) by Restate.from(ih)
                  val ihAtV = have(
                    (v ∈ app(heightFun)(nVar)) ==> (app(G(nVar))(v) === app(G(Succ(nVar)))(v))
                  ) by InstantiateForall(v)(ihAtN)
                  have(app(G(nVar))(v) === app(G(Succ(nVar)))(v)) by
                    Tautology.from(argsTypedAtHeight, ihAtV)
              )

              val bodyEq =
                LambdaBodyEquality.prove(bodyAtGn, bodyAtGSucc, selfArgEqualities)

              val witnessCaseNSchema = recWitness.witnessCaseByConstructor(c).of(spec.selfPlaceholder := G(nVar))
              val witnessCaseNBase = witnessCaseNSchema.statement.right.head match
                case _ ==> consequent =>
                  have(consequent) by Tautology.from(witnessCaseNSchema, gNHasType)
                case _ => throw UnreachableException
              val witnessCaseNAtVars2 = c.variables2.foldLeft(witnessCaseNBase)((_, v2) =>
                lastStep.statement.right.head match
                  case forall(v, phi) =>
                    thenHave(phi.substituteUnsafe(Map(v -> v2)).asInstanceOf[Expr[Prop]]) by
                      InstantiateForall(v2)
                  case _ => throw UnreachableException
              )
              val witnessAtCtorN = witnessCaseNAtVars2.statement.right.head match
                case _ ==> consequent =>
                  have(consequent) by Tautology.from(witnessCaseNAtVars2, argsTypedSemantic)
                case _ => throw UnreachableException

              val witnessCaseSuccSchema = recWitness.witnessCaseByConstructor(c).of(spec.selfPlaceholder := G(Succ(nVar)))
              val witnessCaseSuccBase = witnessCaseSuccSchema.statement.right.head match
                case _ ==> consequent =>
                  have(consequent) by Tautology.from(witnessCaseSuccSchema, gSuccHasType)
                case _ => throw UnreachableException
              val witnessCaseSuccAtVars2 = c.variables2.foldLeft(witnessCaseSuccBase)((_, v2) =>
                lastStep.statement.right.head match
                  case forall(v, phi) =>
                    thenHave(phi.substituteUnsafe(Map(v -> v2)).asInstanceOf[Expr[Prop]]) by
                      InstantiateForall(v2)
                  case _ => throw UnreachableException
              )
              val witnessAtCtorSucc = witnessCaseSuccAtVars2.statement.right.head match
                case _ ==> consequent =>
                  have(consequent) by Tautology.from(witnessCaseSuccAtVars2, argsTypedSemantic)
                case _ => throw UnreachableException

              val gSuccAtAIsWitness = have(app(G(Succ(nVar)))(a) === app(recWitness(G(nVar)))(a)) by
                Congruence.from(gSuccEq)
              val witnessAtGnInput = have(
                app(recWitness(G(nVar)))(a) === app(recWitness(G(nVar)))(c.appliedTerm2)
              ) by Congruence.from(aEqApplied)
              val witnessAtGnAtA = have(app(recWitness(G(nVar)))(a) === bodyAtGn) by Tautology.from(
                altEqualityTransitivity of (
                  x := app(recWitness(G(nVar)))(a),
                  y := app(recWitness(G(nVar)))(c.appliedTerm2),
                  z := bodyAtGn
                ),
                witnessAtGnInput,
                witnessAtCtorN
              )
              val gSuccAtA = have(app(G(Succ(nVar)))(a) === bodyAtGn) by Tautology.from(
                altEqualityTransitivity of (
                  x := app(G(Succ(nVar)))(a),
                  y := app(recWitness(G(nVar)))(a),
                  z := bodyAtGn
                ),
                gSuccAtAIsWitness,
                witnessAtGnAtA
              )

              val gSuccSuccAtAIsWitness = have(
                app(G(Succ(Succ(nVar))))(a) === app(recWitness(G(Succ(nVar))))(a)
              ) by Congruence.from(gSuccSuccEq)
              val witnessAtGSuccInput = have(
                app(recWitness(G(Succ(nVar))))(a) === app(recWitness(G(Succ(nVar))))(c.appliedTerm2)
              ) by Congruence.from(aEqApplied)
              val witnessAtGSuccAtA = have(app(recWitness(G(Succ(nVar))))(a) === bodyAtGSucc) by
                Tautology.from(
                  altEqualityTransitivity of (
                    x := app(recWitness(G(Succ(nVar))))(a),
                    y := app(recWitness(G(Succ(nVar))))(c.appliedTerm2),
                    z := bodyAtGSucc
                  ),
                  witnessAtGSuccInput,
                  witnessAtCtorSucc
                )
              val gSuccSuccAtA = have(app(G(Succ(Succ(nVar))))(a) === bodyAtGSucc) by Tautology.from(
                altEqualityTransitivity of (
                  x := app(G(Succ(Succ(nVar))))(a),
                  y := app(recWitness(G(Succ(nVar))))(a),
                  z := bodyAtGSucc
                ),
                gSuccSuccAtAIsWitness,
                witnessAtGSuccAtA
              )
              val gSuccSuccAtARev = have(bodyAtGSucc === app(G(Succ(Succ(nVar))))(a)) by
                Congruence.from(gSuccSuccAtA)

              have(goalAtA) by Tautology.from(
                altEqualityTransitivity of (
                  x := app(G(Succ(nVar)))(a),
                  y := bodyAtGn,
                  z := app(G(Succ(Succ(nVar))))(a)
                ),
                gSuccAtA,
                have(bodyAtGn === app(G(Succ(Succ(nVar))))(a)) by Tautology.from(
                  altEqualityTransitivity of (
                    x := bodyAtGn,
                    y := bodyAtGSucc,
                    z := app(G(Succ(Succ(nVar))))(a)
                  ),
                  bodyEq,
                  gSuccSuccAtARev
                )
              )
            }

            val rawBranch = c.variables2.reverse.foldLeft(directBranch)((fact, v) =>
              thenHave(∃(v, fact.statement.left.head) |- goalAtA) by LeftExists
            )

            have(constructorBranch(c) |- goalAtA) by Tautology.from(rawBranch)
          )

          val branchesToGoal =
            if branchEqualities.size == 1 then
              have(constructorDisjunction |- goalAtA) by Restate.from(branchEqualities.head)
            else
              have(constructorDisjunction |- goalAtA) by LeftOr(branchEqualities*)

          have(goalAtA) by Cut(decomposeAtA, branchesToGoal)
          thenHave(thesis) by RightImplies.withParameters(
            a ∈ app(heightFun)(Succ(nVar)),
            goalAtA
          )
        }
        have(
          a ∈ app(heightFun)(Succ(nVar)) ==> (app(G(Succ(nVar)))(a) === app(G(Succ(Succ(nVar))))(a))
        ) by Restate.from(pointwiseAtSucc)
        thenHave(
          ∀(a ∈ app(heightFun)(Succ(nVar)), app(G(Succ(nVar)))(a) === app(G(Succ(Succ(nVar))))(a))
        ) by RightForall
      }
      thenHave(thesis) by RightForall
    }

    val all = have(∀(nVar, (nVar ∈ N) ==> P(nVar))) by
      Tautology.from(NatFacts.induction of (Pred := P), base, step)
    thenHave(thesis) by Restate
  }

  // ─────────────────────────────────────────────────────────────────────────
  // subsetBelowSuccN, approximantsAgreeFromSubset, approximantsAgreeAcrossHeights
  // ─────────────────────────────────────────────────────────────────────────

  val approximantsAgreeFromSubset: THM = Lemma(
    (nVar ∈ N, mVar ∈ N, nVar ⊆ mVar, a ∈ app(heightFun)(nVar)) |-
      app(G(nVar))(a) === app(G(mVar))(a)
  ) {
    val nInN = assume(nVar ∈ N)
    val mInN = assume(mVar ∈ N)
    val nSubM = assume(nVar ⊆ mVar)
    val aInHn = assume(a ∈ app(heightFun)(nVar))

    val hValid = have(isHeightPred(heightFun)) by Weakening(heightFunValid)

    val uVar = variable[Ind]
    val propM = λ(
      uVar,
      (nVar ⊆ uVar) ==> (
        (a ∈ app(heightFun)(nVar)) ==> (app(G(nVar))(a) === app(G(uVar))(a))
      )
    )

    val base = have(propM(Zero)) subproof {
      val zeroDef = have(Zero === ∅) by Weakening(Zero.definition)
      have((nVar ⊆ Zero) ==> ((a ∈ app(heightFun)(nVar)) ==> (app(G(nVar))(a) === app(G(Zero))(a)))) subproof {
        val nSubZero = assume(nVar ⊆ Zero)
        val nSubEmpty = have(nVar ⊆ ∅) by Congruence.from(nSubZero, zeroDef)
        val nEqEmpty = have(nVar === ∅) by Tautology.from(
          nSubEmpty,
          Subset.rightEmpty of (x := nVar),
          equivalenceApply of (p1 := subset(nVar, ∅), p2 := nVar === ∅)
        )
        val emptyEqZero = have(∅ === Zero) by Congruence.from(zeroDef)
        val nEqZero = have(nVar === Zero) by Tautology.from(
          altEqualityTransitivity of (x := nVar, y := ∅, z := Zero),
          nEqEmpty,
          emptyEqZero
        )
        val eqAtZero = have(app(G(nVar))(a) === app(G(Zero))(a)) by Congruence.from(nEqZero)
        have(thesis) by Tautology.from(eqAtZero)
      }
      thenHave(thesis) by Restate
    }

    val step = have(∀(uVar, (uVar ∈ N) ==> (propM(uVar) ==> propM(Succ(uVar))))) subproof {
      have((uVar ∈ N) ==> (propM(uVar) ==> propM(Succ(uVar)))) subproof {
        val uInNStep = assume(uVar ∈ N)
        val ih = assume(propM(uVar))

        val goalAtSucc = have(propM(Succ(uVar))) subproof {
          have(
            (nVar ⊆ Succ(uVar)) ==> (
              (a ∈ app(heightFun)(nVar)) ==> (app(G(nVar))(a) === app(G(Succ(uVar)))(a))
            )
          ) subproof {
            val nSubSuccU = assume(nVar ⊆ Succ(uVar))
            val aInHeightN = assume(a ∈ app(heightFun)(nVar))

            val split = have((nVar === Succ(uVar)) \/ (nVar ⊆ uVar)) by Tautology.from(
              nInN,
              uInNStep,
              nSubSuccU,
              subsetBelowSuccN.of(nVar := nVar, kVar := uVar)
            )

            val caseEq = have(
              nVar === Succ(uVar) |- app(G(nVar))(a) === app(G(Succ(uVar)))(a)
            ) by Congruence

            val caseSub = have(
              nVar ⊆ uVar |- app(G(nVar))(a) === app(G(Succ(uVar)))(a)
            ) subproof {
              val nSubUCase = assume(nVar ⊆ uVar)
              val eqNu = have(app(G(nVar))(a) === app(G(uVar))(a)) by Tautology.from(
                ih,
                nSubUCase,
                aInHeightN
              )

              val hSubset = have(
                subset(app(heightFun)(nVar), app(heightFun)(uVar))
              ) by Tautology.from(
                hValid,
                uInNStep,
                nInN,
                nSubUCase,
                heightMonotonic.of(h := heightFun, n := uVar, m := nVar)
              )

              val aInHu = have(a ∈ app(heightFun)(uVar)) by Tautology.from(
                hSubset,
                aInHeightN,
                Subset.membership of (x := app(heightFun)(nVar), y := app(heightFun)(uVar), z := a)
              )

              val stabAtU = have(
                uVar ∈ N ==> ∀(a ∈ app(heightFun)(uVar), app(G(uVar))(a) === app(G(Succ(uVar)))(a))
              ) by InstantiateForall(uVar)(stabilization)
              val stabU = have(
                ∀(a ∈ app(heightFun)(uVar), app(G(uVar))(a) === app(G(Succ(uVar)))(a))
              ) by Tautology.from(uInNStep, stabAtU)
              val stabAtA = have(
                a ∈ app(heightFun)(uVar) ==> (app(G(uVar))(a) === app(G(Succ(uVar)))(a))
              ) by InstantiateForall(a)(stabU)
              val eqUSu = have(app(G(uVar))(a) === app(G(Succ(uVar)))(a)) by
                Tautology.from(aInHu, stabAtA)

              have(thesis) by Tautology.from(
                altEqualityTransitivity of (
                  x := app(G(nVar))(a),
                  y := app(G(uVar))(a),
                  z := app(G(Succ(uVar)))(a)
                ),
                eqNu,
                eqUSu
              )
            }

            have(app(G(nVar))(a) === app(G(Succ(uVar)))(a)) by
              Tautology.from(split, caseEq, caseSub)
            have(
              (a ∈ app(heightFun)(nVar)) ==> (app(G(nVar))(a) === app(G(Succ(uVar)))(a))
            ) by Tautology.from(lastStep)
            thenHave(thesis) by Restate
          }
          thenHave(thesis) by Restate
        }

        val imp = have(propM(uVar) ==> propM(Succ(uVar))) by Tautology.from(goalAtSucc)
        have(thesis) by Tautology.from(imp)
      }
      thenHave(thesis) by RightForall
    }

    val Pred = variable[Ind >>: Prop]
    val indInst = have(
      (propM(Zero), ∀(uVar, (uVar ∈ N) ==> (propM(uVar) ==> propM(Succ(uVar))))) |-
        ∀(uVar, (uVar ∈ N) ==> propM(uVar))
    ) by Weakening(NatFacts.induction of (Pred := propM))
    val all = have(∀(uVar, (uVar ∈ N) ==> propM(uVar))) by
      Tautology.from(base, step, indInst)
    val atM = have(mVar ∈ N ==> propM(mVar)) by InstantiateForall(mVar)(all)
    val propAtM = have(propM(mVar)) by Tautology.from(mInN, atM)

    have(app(G(nVar))(a) === app(G(mVar))(a)) by Tautology.from(propAtM, nSubM, aInHn)
    thenHave(thesis) by Restate
  }

  val approximantsAgreeAcrossHeights: THM = Lemma(
    (nVar ∈ N, mVar ∈ N, a ∈ app(heightFun)(nVar), a ∈ app(heightFun)(mVar)) |-
      app(G(nVar))(a) === app(G(mVar))(a)
  ) {
    val nInN = assume(nVar ∈ N)
    val mInN = assume(mVar ∈ N)
    val aInHn = assume(a ∈ app(heightFun)(nVar))
    val aInHm = assume(a ∈ app(heightFun)(mVar))

    val upperInN = have((nVar ∪ mVar) ∈ N) by Tautology.from(
      nInN,
      mInN,
      unionOfTwoNats.of(a := nVar, b := mVar)
    )

    val nSubUpper = have(nVar ⊆ (nVar ∪ mVar)) by
      Tautology.from(Union.leftSubset of (x := nVar, y := mVar))
    val mSubUpper = have(mVar ⊆ (nVar ∪ mVar)) by
      Tautology.from(Union.rightSubset of (x := nVar, y := mVar))

    val eqNUpper = have(app(G(nVar))(a) === app(G(nVar ∪ mVar))(a)) by Tautology.from(
      nInN,
      upperInN,
      nSubUpper,
      aInHn,
      approximantsAgreeFromSubset.of(nVar := nVar, mVar := nVar ∪ mVar)
    )
    val eqMUpper = have(app(G(mVar))(a) === app(G(nVar ∪ mVar))(a)) by Tautology.from(
      mInN,
      upperInN,
      mSubUpper,
      aInHm,
      approximantsAgreeFromSubset.of(nVar := mVar, mVar := nVar ∪ mVar)
    )
    val eqUpperM = have(app(G(nVar ∪ mVar))(a) === app(G(mVar))(a)) by
      Congruence.from(eqMUpper)

    have(app(G(nVar))(a) === app(G(mVar))(a)) by Tautology.from(
      altEqualityTransitivity of (
        x := app(G(nVar))(a),
        y := app(G(nVar ∪ mVar))(a),
        z := app(G(mVar))(a)
      ),
      eqNUpper,
      eqUpperM
    )
    thenHave(thesis) by Restate
  }

  // ─────────────────────────────────────────────────────────────────────────
  // Helper
  // ─────────────────────────────────────────────────────────────────────────

  // ─────────────────────────────────────────────────────────────────────────
  // Lemma E — limit function
  // limitFun := λ(a ∈ argType). G(ε n. a ∈ h(n))(a)
  // ─────────────────────────────────────────────────────────────────────────

  def limitIndex(point: Expr[Ind]): Expr[Ind] =
    ε(nVar, (nVar ∈ N) /\ (point ∈ app(heightFun)(nVar)))

  val limitFun: Expr[Ind] =
    abs(spec.argType)(λ(a, app(G(limitIndex(a)))(a)))

  val limitHasType: THM = Lemma(limitFun :: spec.typ) {
    val hValid = have(isHeightPred(heightFun)) by Restate.from(heightFunValid)

    val everyValueTyped = have(
      ∀(a ∈ spec.argType, app(G(limitIndex(a)))(a) ∈ spec.returnType)
    ) subproof {
      val pointwiseAtA = have(
        (a ∈ spec.argType) ==> (app(G(limitIndex(a)))(a) ∈ spec.returnType)
      ) subproof {
        val aInArgType = assume(a ∈ spec.argType)

        val hasSomeHeight = have(
          ∃(nVar, (nVar ∈ N) /\ (a ∈ app(heightFun)(nVar)))
        ) by Tautology.from(
          hValid,
          aInArgType,
          termHasHeight of (x := a, h := heightFun),
          equivalenceApply of (
            p1 := in(a, spec.argType),
            p2 := ∃(nVar, in(nVar, N) /\ in(a, app(heightFun)(nVar)))
          )
        )

        val indexWitness = have(
          (limitIndex(a) ∈ N) /\ (a ∈ app(heightFun)(limitIndex(a)))
        ) by Cut(
          hasSomeHeight,
          Quantifiers.existsEpsilon.of(
            x := nVar,
            P := λ(nVar, (nVar ∈ N) /\ (a ∈ app(heightFun)(nVar)))
          )
        )

        val indexInN = have(limitIndex(a) ∈ N) by Tautology.from(indexWitness)

        val approxAtIndex = have(limitIndex(a) ∈ N ==> (G(limitIndex(a)) :: spec.typ)) by
          InstantiateForall(limitIndex(a))(approx.approxHasType)
        val approxTyped = have(G(limitIndex(a)) :: spec.typ) by
          Tautology.from(indexInN, approxAtIndex)

        val approxBetween = have(
          functionBetween(G(limitIndex(a)))(spec.argType)(spec.returnType)
        ) by Tautology.from(
          funcBetweenEqInFuncSpace of (
            f := G(limitIndex(a)),
            A := spec.argType,
            B := spec.returnType
          ),
          approxTyped
        )

        have(app(G(limitIndex(a)))(a) ∈ spec.returnType) by Tautology.from(
          approxBetween,
          aInArgType,
          appTyping of (
            f := G(limitIndex(a)),
            A := spec.argType,
            B := spec.returnType,
            x := a
          )
        )
        thenHave(thesis) by RightImplies.withParameters(
          a ∈ spec.argType,
          app(G(limitIndex(a)))(a) ∈ spec.returnType
        )
      }
      have(
        (a ∈ spec.argType) ==> (app(G(limitIndex(a)))(a) ∈ spec.returnType)
      ) by Restate.from(pointwiseAtA)
      thenHave(
        ∀(a, (a ∈ spec.argType) ==> (app(G(limitIndex(a)))(a) ∈ spec.returnType))
      ) by RightForall
      thenHave(thesis) by Restate
    }

    val absTypedAtPi = have(
      abs(spec.argType)(λ(a, app(G(limitIndex(a)))(a))) ∈ Pi(spec.argType)(λ(y, spec.returnType))
    ) by Tautology.from(
      everyValueTyped,
      TAbsConstOn(spec.argType, spec.returnType, λ(a, app(G(limitIndex(a)))(a)))
    )

    have(limitFun :: spec.typ) by Congruence.from(absTypedAtPi)
    thenHave(thesis) by Restate
  }
}
