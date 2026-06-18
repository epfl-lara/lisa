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
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.PropositionalFacts.altEqualityTransitivity
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
 *  G(0) = W(g₀) G(n+1) = W(G(n))
 *
 *  Exports:
 *    - [[approxSeq]], [[G]] — the sequence itself
 *    - [[approxZero]] — G(0) = W(g₀)
 *    - [[approxSucc]] — ∀k ∈ ω, G(S(k)) = W(G(k))
 *    - [[approxHasType]] — ∀n ∈ ω, G(n) :: spec.typ
 */
private[recursion] final class Approx[N <: Arity](
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

  def G(n: Expr[Ind]): Expr[Ind] = app(approxSeq)(n)

  // ─────────────────────────────────────────────────────────────────────────
  // approxZero: G(0) = W(g₀)
  // ─────────────────────────────────────────────────────────────────────────

  private val approxZero: THM = Lemma(G(∅) === recWitness(g0)) {
    val eqAll = have(∀(x ∈ N, app(approxSeq)(x) === stepFunc(x)(approxSeq ↾ x))) by
      Tautology.from(
        OmegaFacts.isOrdinal,
        TransfiniteRecursion.transfiniteRecursionFunctionSpec.of(Func := stepFunc, α := N)
      )

    val eq0 =
      have(∅ ∈ N |- app(approxSeq)(∅) === stepFunc(∅)(approxSeq ↾ ∅)) by
        InstantiateForall(∅)(eqAll)

    val Q = λ(
      yVar,
      ((∅ === ∅) /\ (yVar === recWitness(g0))) \/ ∃(
        jVar,
        (jVar ∈ N) /\ (∅ === S(jVar)) /\
          (yVar === recWitness(app(approxSeq ↾ ∅)(jVar)))
      )
    )

    val Fm0 = have(stepFunc(∅)(approxSeq ↾ ∅) === ε(yVar, Q(yVar))) by Restate

    val Qw = have(Q(recWitness(g0))) by Tautology

    val uniq = have(∀(yVar, Q(yVar) ==> (yVar === recWitness(g0)))) subproof {
      have(Q(yVar) |- yVar === recWitness(g0)) subproof {
        assume(Q(yVar))

        val disj = have(
          ((∅ === ∅) /\ (yVar === recWitness(g0))) \/ ∃(
            jVar,
            (jVar ∈ N) /\ (∅ === S(jVar)) /\
              (yVar === recWitness(app(approxSeq ↾ ∅)(jVar)))
          )
        ) by Restate

        val case1 = have(
          ((∅ === ∅) /\ (yVar === recWitness(g0))) ==> (yVar === recWitness(g0))
        ) by Tautology

        val contra = have(
          ∃(
            jVar,
            (jVar ∈ N) /\ (∅ === S(jVar)) /\
              (yVar === recWitness(app(approxSeq ↾ ∅)(jVar)))
          ) |- ()
        ) subproof {
          assume(
            ∃(
              jVar,
              (jVar ∈ N) /\ (∅ === S(jVar)) /\
                (yVar === recWitness(app(approxSeq ↾ ∅)(jVar)))
            )
          )
          have(
            (jVar ∈ N) /\ (∅ === S(jVar)) /\
              (yVar === recWitness(app(approxSeq ↾ ∅)(jVar))) |- ()
          ) subproof {
            val jInNat = have(
              (jVar ∈ N) /\ (∅ === S(jVar)) /\
                (yVar === recWitness(app(approxSeq ↾ ∅)(jVar))) |- jVar ∈ N
            ) by Tautology
            val zEqSj = have(
              (jVar ∈ N) /\ (∅ === S(jVar)) /\
                (yVar === recWitness(app(approxSeq ↾ ∅)(jVar))) |- ∅ === S(jVar)
            ) by Tautology
            val SjEq0 = have(
              (jVar ∈ N) /\ (∅ === S(jVar)) /\
                (yVar === recWitness(app(approxSeq ↾ ∅)(jVar))) |- S(jVar) === ∅
            ) by Congruence.from(zEqSj)
            val SjNe0 = have(jVar ∈ N |- (S(jVar) =/= ∅)) by
              Weakening(Integer.zeroIsNotSucc.of(n := jVar))
            val notSjEq0 = have(
              (jVar ∈ N) /\ (∅ === S(jVar)) /\
                (yVar === recWitness(app(approxSeq ↾ ∅)(jVar))) |-
                ¬(S(jVar) === ∅)
            ) by Tautology.from(SjNe0, jInNat)
            have(thesis) by Tautology.from(SjEq0, notSjEq0)
          }
          thenHave(thesis) by LeftExists
        }

        val case2 = have(
          ∃(
            jVar,
            (jVar ∈ N) /\ (∅ === S(jVar)) /\
              (yVar === recWitness(app(approxSeq ↾ ∅)(jVar)))
          ) ==> (yVar === recWitness(g0))
        ) by Restate.from(
          have(
            ∃(
              jVar,
              (jVar ∈ N) /\ (∅ === S(jVar)) /\
                (yVar === recWitness(app(approxSeq ↾ ∅)(jVar)))
            ) |- yVar === recWitness(g0)
          ) by Weakening(contra)
        )

        have(thesis) by Tautology.from(disj, case1, case2)
      }
      thenHave(Q(yVar) ==> (yVar === recWitness(g0))) by Restate
      thenHave(thesis) by RightForall
    }

    val epsEq = have(ε(yVar, Q(yVar)) === recWitness(g0)) subproof {
      val exQ = have(∃(yVar, Q(yVar))) subproof {
        have(Q(recWitness(g0))) by Restate.from(Qw)
        thenHave(thesis) by RightExists
      }
      val epsQ = have(Q(ε(yVar, Q(yVar)))) by
        Cut(exQ, Quantifiers.existsEpsilon.of(x := yVar, P := Q))
      val epsImp = have(Q(ε(yVar, Q(yVar))) ==> (ε(yVar, Q(yVar)) === recWitness(g0))) by
        InstantiateForall(ε(yVar, Q(yVar)))(uniq)
      have(thesis) by Tautology.from(epsQ, epsImp)
    }

    val rhsEq = have(stepFunc(∅)(approxSeq ↾ ∅) === recWitness(g0)) by
      Congruence.from(Fm0, epsEq)
    val rec0 = have(∅ ∈ N |- G(∅) === recWitness(g0)) by Congruence.from(eq0, rhsEq)
    have(∅ ∈ N) by Restate.from(emptyInOmega)
    have(thesis) by Cut(lastStep, rec0)
  }

  // ─────────────────────────────────────────────────────────────────────────
  // approxSucc: ∀k ∈ ℕ, G(S(k)) = W(G(k))
  // ─────────────────────────────────────────────────────────────────────────

  val approxSucc: THM = Lemma(∀(kVar ∈ N, G(S(kVar)) === recWitness(G(kVar)))) {
    have(kVar ∈ N |- G(S(kVar)) === recWitness(G(kVar))) subproof {
      val kInNat = assume(kVar ∈ N)

      val SkInNat = have(S(kVar) ∈ N) by Tautology.from(kInNat, successorInOmega.of(n := kVar))

      val recSpec = have(
        functionOn(approxSeq)(N) /\
          ∀(x ∈ N, app(approxSeq)(x) === stepFunc(x)(approxSeq ↾ x))
      ) by Tautology.from(
        OmegaFacts.isOrdinal,
        TransfiniteRecursion.transfiniteRecursionFunctionSpec.of(Func := stepFunc, α := N)
      )

      val eqAll = have(∀(x ∈ N, app(approxSeq)(x) === stepFunc(x)(approxSeq ↾ x))) by
        Tautology.from(recSpec)

      val eqSk = have(
        S(kVar) ∈ N |-
          app(approxSeq)(S(kVar)) === stepFunc(S(kVar))(approxSeq ↾ S(kVar))
      ) by InstantiateForall(S(kVar))(eqAll)

      val hSk = approxSeq ↾ S(kVar)

      val Q = λ(
        yVar,
        ((S(kVar) === ∅) /\ (yVar === recWitness(g0))) \/ ∃(
          jVar,
          (jVar ∈ N) /\ (S(kVar) === S(jVar)) /\
            (yVar === recWitness(app(hSk)(jVar)))
        )
      )

      val FmSk = have(stepFunc(S(kVar))(hSk) === ε(yVar, Q(yVar))) by Restate

      val exY = have(∃(yVar, Q(yVar))) subproof {
        have(
          (kVar ∈ N) /\ (S(kVar) === S(kVar)) /\
            (recWitness(app(hSk)(kVar)) === recWitness(app(hSk)(kVar)))
        ) by Tautology.from(kInNat)
        thenHave(
          ∃(
            jVar,
            (jVar ∈ N) /\ (S(kVar) === S(jVar)) /\
              (recWitness(app(hSk)(kVar)) === recWitness(app(hSk)(jVar)))
          )
        ) by RightExists
        thenHave(Q(recWitness(app(hSk)(kVar)))) by Tautology
        thenHave(thesis) by RightExists
      }

      val uniq =
        have(∀(yVar, Q(yVar) ==> (yVar === recWitness(app(hSk)(kVar))))) subproof {
          have(Q(yVar) |- yVar === recWitness(app(hSk)(kVar))) subproof {
            assume(Q(yVar))

            val SkNe0 = have(S(kVar) =/= ∅) by
              Weakening(Integer.zeroIsNotSucc.of(n := kVar))
            val notCase1 = have(¬((S(kVar) === ∅) /\ (yVar === recWitness(g0)))) by
              Tautology.from(SkNe0)

            val disj = have(
              ((S(kVar) === ∅) /\ (yVar === recWitness(g0))) \/ ∃(
                jVar,
                (jVar ∈ N) /\ (S(kVar) === S(jVar)) /\
                  (yVar === recWitness(app(hSk)(jVar)))
              )
            ) by Restate

            val exJ = have(
              ∃(
                jVar,
                (jVar ∈ N) /\ (S(kVar) === S(jVar)) /\
                  (yVar === recWitness(app(hSk)(jVar)))
              )
            ) by Tautology.from(disj, notCase1)

            val fromExJ = have(
              ∃(
                jVar,
                (jVar ∈ N) /\ (S(kVar) === S(jVar)) /\
                  (yVar === recWitness(app(hSk)(jVar)))
              ) |- yVar === recWitness(app(hSk)(kVar))
            ) subproof {
              assume(
                ∃(
                  jVar,
                  (jVar ∈ N) /\ (S(kVar) === S(jVar)) /\
                    (yVar === recWitness(app(hSk)(jVar)))
                )
              )
              have(
                (jVar ∈ N) /\ (S(kVar) === S(jVar)) /\
                  (yVar === recWitness(app(hSk)(jVar))) |-
                  yVar === recWitness(app(hSk)(kVar))
              ) subproof {
                val SkEqSj = have(
                  (jVar ∈ N) /\ (S(kVar) === S(jVar)) /\
                    (yVar === recWitness(app(hSk)(jVar))) |- S(kVar) === S(jVar)
                ) by Tautology
                val yEq = have(
                  (jVar ∈ N) /\ (S(kVar) === S(jVar)) /\
                    (yVar === recWitness(app(hSk)(jVar))) |-
                    yVar === recWitness(app(hSk)(jVar))
                ) by Tautology

                val inj = have(S(kVar) === S(jVar) |- kVar === jVar) by
                  Tautology.from(Integer.successorInjectivity.of(n := kVar, m := jVar))

                val kEqJ = have(
                  (jVar ∈ N) /\ (S(kVar) === S(jVar)) /\
                    (yVar === recWitness(app(hSk)(jVar))) |- kVar === jVar
                ) by Cut(SkEqSj, inj)
                val jEqK = have(
                  (jVar ∈ N) /\ (S(kVar) === S(jVar)) /\
                    (yVar === recWitness(app(hSk)(jVar))) |- jVar === kVar
                ) by Congruence.from(kEqJ)

                val hjEqhk = have(
                  (jVar ∈ N) /\ (S(kVar) === S(jVar)) /\
                    (yVar === recWitness(app(hSk)(jVar))) |-
                    app(hSk)(jVar) === app(hSk)(kVar)
                ) by Congruence.from(jEqK)
                val whjEqwhk = have(
                  (jVar ∈ N) /\ (S(kVar) === S(jVar)) /\
                    (yVar === recWitness(app(hSk)(jVar))) |-
                    recWitness(app(hSk)(jVar)) === recWitness(app(hSk)(kVar))
                ) by Congruence.from(hjEqhk)

                have(thesis) by Congruence.from(yEq, whjEqwhk)
              }
              thenHave(thesis) by LeftExists
            }

            have(thesis) by Cut(exJ, fromExJ)
          }
          thenHave(Q(yVar) ==> (yVar === recWitness(app(hSk)(kVar)))) by Restate
          thenHave(thesis) by RightForall
        }

      val epsEq = have(ε(yVar, Q(yVar)) === recWitness(app(hSk)(kVar))) subproof {
        val epsQ = have(Q(ε(yVar, Q(yVar)))) by
          Cut(exY, Quantifiers.existsEpsilon.of(x := yVar, P := Q))
        val epsImp = have(
          Q(ε(yVar, Q(yVar))) ==> (ε(yVar, Q(yVar)) === recWitness(app(hSk)(kVar)))
        ) by InstantiateForall(ε(yVar, Q(yVar)))(uniq)
        have(thesis) by Tautology.from(epsQ, epsImp)
      }

      val hSkAtK = have(app(hSk)(kVar) === G(kVar)) subproof {
        val kInSk = have(kVar ∈ S(kVar)) by Weakening(selfInSuccessor.of(n := kVar))
        val GmOn = have(functionOn(approxSeq)(N)) by Tautology.from(recSpec)
        val GmFun = have(function(approxSeq)) by
          Tautology
            .from(GmOn, BasicTheorems.functionOnIsFunction.of(f := approxSeq, A := N))
        val GmDom = have(dom(approxSeq) === N) by
          Tautology.from(GmOn, BasicTheorems.functionOnDomain.of(f := approxSeq, A := N))
        val kInDom = have(kVar ∈ dom(approxSeq)) by Congruence.from(kInNat, GmDom)
        val restEq = have(app(approxSeq ↾ S(kVar))(kVar) === app(approxSeq)(kVar)) by
          Tautology.from(
            Restriction.restrictedApp.of(f := approxSeq, x := kVar, A := S(kVar)),
            GmFun,
            kInDom,
            kInSk
          )
        have(thesis) by Restate.from(restEq)
      }

      val whSkEqwG = have(recWitness(app(hSk)(kVar)) === recWitness(G(kVar))) by
        Congruence.from(hSkAtK)

      have(stepFunc(S(kVar))(hSk) === recWitness(app(hSk)(kVar))) by
        Congruence.from(FmSk, epsEq)
      val rhsEq = have(stepFunc(S(kVar))(hSk) === recWitness(G(kVar))) by
        Tautology.from(
          lastStep,
          whSkEqwG,
          altEqualityTransitivity of
            (
              x := stepFunc(S(kVar))(hSk),
              y := recWitness(app(hSk)(kVar)),
              z := recWitness(G(kVar))
            )
        )

      val rec = have(S(kVar) ∈ N |- G(S(kVar)) === recWitness(G(kVar))) by
        Congruence.from(eqSk, rhsEq)

      have(thesis) by Cut(SkInNat, rec)
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

    val g0Typed = have(g0 :: spec.typ) subproof {
      val seedPred = λ(f0, f0 :: spec.typ)
      val epsStep = have(∃(f0, f0 :: spec.typ) |- g0 :: spec.typ) by
        Restate.from(Quantifiers.existsEpsilon.of(x := f0, P := seedPred))
      have(thesis) by Cut(seedExists, epsStep)
    }

    val base = have(prop(∅)) subproof {
      val witnessAtG0Typed = have(recWitness(g0) :: spec.typ) by
        Tautology.from(g0Typed, recWitness.witnessHasType.of(spec.selfPlaceholder := g0))
      val g0Eq = have(G(∅) === recWitness(g0)) by Restate.from(approxZero)
      val g0ApproxTyped = have(G(∅) :: spec.typ) by
        Congruence.from(g0Eq, witnessAtG0Typed)
      have(thesis) by Restate.from(g0ApproxTyped)
    }

    val step = have(∀(nVar, (nVar ∈ N) ==> (prop(nVar) ==> prop(S(nVar))))) subproof {
      have((nVar ∈ N) ==> (prop(nVar) ==> prop(S(nVar)))) subproof {
        val nInNat = assume(nVar ∈ N)
        val ih = assume(prop(nVar))

        val approxSuccAtN = have(nVar ∈ N ==> (G(S(nVar)) === recWitness(G(nVar)))) by
          InstantiateForall(nVar)(approxSucc)
        val gSuccEq = have(G(S(nVar)) === recWitness(G(nVar))) by
          Tautology.from(nInNat, approxSuccAtN)

        val witnessAtGnTyped = have(recWitness(G(nVar)) :: spec.typ) by
          Tautology
            .from(ih, recWitness.witnessHasType.of(spec.selfPlaceholder := G(nVar)))
        val gSuccTyped = have(G(S(nVar)) :: spec.typ) by
          Congruence.from(gSuccEq, witnessAtGnTyped)
        have(thesis) by Restate.from(gSuccTyped)
      }
      thenHave(thesis) by RightForall
    }

    val all = have(∀(nVar, (nVar ∈ N) ==> prop(nVar))) by
      Tautology.from(omegaSuccessorInduction of (P := prop), base, step)
    have(thesis) by Restate.from(all)
  }
}
