package lisa.hol.basics

import lisa.automation.Substitution.{Apply => Substitute}
import lisa.hol.HOLHelperTheorems._
import lisa.hol.HOLSteps._
import lisa.hol.basics.Truth.{holT, holTruth, SYM}
import lisa.hol.basics.Forall.{hforall, hforallCorrect}
import lisa.hol.basics.Connectives.{himp, himpCorrect, hnot, hnotCorrect, p}
import lisa.hol.VarsAndFunctions._
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.utils.prooflib.BasicStepTactic._
import lisa.utils.prooflib.Library
import lisa.utils.prooflib.ProofTacticLib._
import lisa.utils.prooflib.SimpleDeducedSteps._

/**
 * HOL Light existential quantifier.
 *
 * Defines:
 *  - hexists (polymorphic constant)
 *  - hexistsCorrect (correctness theorem)
 */
object Exists extends lisa.HOL {

  val A = typevar

  val x = typedvar(A)
  val P = typedvar(A ->: 𝔹)
  val q = typedvar(𝔹)

  val lib = summon[Library]

  /**
   * Higher-order embedded existential quantifier.
   *
   * Defined as in HOL Light:
   * `(?) = \P:A->bool. !q. (!x. P x ==> q) ==> q`
   */
  val hexists: HOLPolymorphicConstant[Ind >>: Ind] = {

    val P = typedvar(A ->: 𝔹)
    val q = typedvar(𝔹)
    val x = typedvar(A)
    val y = typedvar(𝔹)
    val z = variable[Ind]

    val hexists = DEF(λ(A, fun(P, hforall(𝔹) * fun(q, himp * (hforall(A) * fun(x, himp * (P * x) * q)) * q))))
    val typing_of_exists = Theorem(∀(A, nonEmpty(A) ==> hexists(A) :: ((A ->: 𝔹) ->: 𝔹))):

      val faType = hforall(A) :: ((A ->: 𝔹) ->: 𝔹)
      val fbType = hforall(𝔹) :: ((𝔹 ->: 𝔹) ->: 𝔹)
      val impType = himp :: (𝔹 ->: 𝔹 ->: 𝔹)

      val faStep = have(faType) by Restate.from(hforall.justif of A)
      val fbStep = have(fbType) by Tautology.from(hforall.justif of 𝔹, 𝔹.nonEmptyThm)
      val imStep = have(impType) by Restate.from(himp.justif)

      have((faType, fbType, impType, exists(q, q :: 𝔹), nonEmpty(A)) |- fun(P, hforall(𝔹) * fun(q, himp * (hforall(A) * fun(x, himp * (P * x) * q)) * q)) :: ((A ->: 𝔹) ->: 𝔹)) by Typecheck.prove
      thenHave((faType, fbType, impType, exists(q, q :: 𝔹), nonEmpty(A)) |- hexists(A) :: ((A ->: 𝔹) ->: 𝔹)) by Substitute(hexists.definition)
      lib.have(nonEmpty(A) ==> hexists(A) :: ((A ->: 𝔹) ->: 𝔹)) by Tautology.from(lastStep, hforall.justif of A, hforall.justif of 𝔹, himp.justif, 𝔹.nonEmptyThm)
      thenHave(thesis) by RightForall

    HOLPolymorphicConstant[Ind >>: Ind](hexists.id, FunctionalClass(List(None), List(A), ((A ->: 𝔹) ->: 𝔹)), typing_of_exists)
  }

  val hexistsCorrect = HOLTheorem(
    (hexists(A) * P) <=> ∃(x :: A, P * x)
  ):
    assumeAll

    // Abbreviations for the body of hexists(A) * P
    val innerImp = himp * (P * x) * q // himp (P x) q
    val innerPred = fun(x, innerImp) // λx. himp (P x) q
    val innerFA = hforall(A) * innerPred // hforall A (λx. himp (P x) q)
    val outerImp = himp * innerFA * q // himp (hforall A (λx. himp (P x) q)) q
    val outerPred = fun(q, outerImp) // λq. himp (hforall A (λx. himp (P x) q)) q
    val body = hforall(𝔹) * outerPred // hforall 𝔹 (λq. ...)

    // Step 1: Beta-reduce hexists(A) * P to body
    val beta = have(hexists(A) * P === body) subproof:
      BETA_CONV(fun(P, body) * P)
      val betaRed = thenHave((hexists(A) * P) =:= body) by Substitute(hexists.definition)
      have(thesis) by Tautology.from(
        betaRed,
        eqAlign of (A := 𝔹, x := hexists(A) * P, y := body),
        have(HOLProofType(hexists(A) * P)),
        have(HOLProofType(body))
      )

    // Correctness lemmas for the HOL connectives
    // Note: these use the outer (free) variables x, q

    // himp * (P * x) * q <=> (P * x ==> q)
    val innerImpLift = have(innerImp <=> (P * x ==> q)) subproof:
      have(thesis) by Tautology.from(
        himpCorrect of (p := P * x, q := q),
        have(HOLProofType(P * x)),
        have(HOLProofType(q))
      )

    // hforall(A) * innerPred <=> ∀(x :: A, innerPred * x)
    val innerFALift = have(innerFA <=> ∀(x :: A, innerPred * x)) subproof:
      val typing = have(HOLProofType(innerPred))
      val inst = have((innerPred :: (A ->: 𝔹), nonEmpty(A)) |- (innerFA <=> ∀(x :: A, innerPred * x))) by Weakening(hforallCorrect of (P := innerPred, x := x))
      have(thesis) by Cut(typing, inst)

    // himp * innerFA * q <=> (innerFA ==> q)
    val outerImpLift = have(outerImp <=> (innerFA ==> q)) subproof:
      have(thesis) by Tautology.from(
        himpCorrect of (p := innerFA, q := q),
        have(HOLProofType(innerFA)),
        have(HOLProofType(q))
      )

    // hforall(𝔹) * outerPred <=> ∀(q :: 𝔹, outerPred * q)
    val outerFALift = have(body <=> ∀(q :: 𝔹, outerPred * q)) subproof:
      val typing = have(HOLProofType(outerPred))
      have(thesis) by Tautology.from(
        hforallCorrect of (A := 𝔹, P := outerPred, x := q),
        typing,
        𝔹.nonEmptyThm
      )

    // Beta reductions
    val outerBeta = have(outerPred * q === outerImp) subproof:
      val bc = BETA_CONV(outerPred * q)
      have(thesis) by Tautology.from(
        bc,
        eqAlign of (A := 𝔹, x := outerPred * q, y := outerImp),
        have(HOLProofType(outerPred * q)),
        have(HOLProofType(outerImp))
      )

    val innerBeta = have(innerPred * x === innerImp) subproof:
      val bc = BETA_CONV(innerPred * x)
      have(thesis) by Tautology.from(
        bc,
        eqAlign of (A := 𝔹, x := innerPred * x, y := innerImp),
        have(HOLProofType(innerPred * x)),
        have(HOLProofType(innerImp))
      )

    // Forward direction: hexists(A) * P |- ∃(x :: A, P * x)
    val fwd = have((hexists(A) * P) ==> ∃(x :: A, P * x)) subproof:
      // Instantiate q := Zero for the forward direction
      val innerImp0 = himp * (P * x) * Zero
      val innerPred0 = fun(x, innerImp0)
      val innerFA0 = hforall(A) * innerPred0
      val outerImp0 = himp * innerFA0 * Zero

      // Beta and correctness with q=Zero
      val outerBeta0 = have(outerPred * Zero === outerImp0) subproof:
        val bc = BETA_CONV(outerPred * Zero)
        have(thesis) by Tautology.from(
          bc,
          eqAlign of (A := 𝔹, x := outerPred * Zero, y := outerImp0),
          have(HOLProofType(outerPred * Zero)),
          have(HOLProofType(outerImp0))
        )

      val outerImpLift0 = have(outerImp0 <=> (innerFA0 ==> Zero)) subproof:
        have(thesis) by Tautology.from(
          himpCorrect of (p := innerFA0, q := Zero),
          have(HOLProofType(innerFA0)),
          Zero.justif
        )

      val innerFALift0 = have(innerFA0 <=> ∀(x :: A, innerPred0 * x)) subproof:
        have(thesis) by Tautology.from(
          hforallCorrect of (P := innerPred0, x := x),
          have(HOLProofType(innerPred0))
        )

      val innerBeta0 = have(innerPred0 * x === innerImp0) subproof:
        val bc = BETA_CONV(innerPred0 * x)
        have(thesis) by Tautology.from(
          bc,
          eqAlign of (A := 𝔹, x := innerPred0 * x, y := innerImp0),
          have(HOLProofType(innerPred0 * x)),
          have(HOLProofType(innerImp0))
        )

      val innerImpLift0 = have(innerImp0 <=> (P * x ==> Zero)) subproof:
        have(thesis) by Tautology.from(
          himpCorrect of (p := P * x, q := Zero),
          have(HOLProofType(P * x)),
          Zero.justif
        )

      // innerPred0 * x <=> ¬(P * x)
      // because: innerPred0 * x === innerImp0 (by innerBeta0)
      //          innerImp0 <=> (P * x ==> Zero) (by innerImpLift0)
      //          (P * x ==> Zero) <=> ¬(P * x) (since 0 ≠ 1)
      val innerPredNeg = have(innerPred0 * x <=> !(P * x)) subproof:
        have(innerImp0 <=> !(P * x)) by Tautology.from(innerImpLift0, `0 != 1`)
        thenHave(thesis) by Substitute(innerBeta0)

      // Main argument:
      // From hexists(A) * P, derive body, then ∀(q :: 𝔹, outerPred * q)
      // Instantiate q := Zero: outerPred * Zero
      // outerPred * Zero === outerImp0, so outerImp0
      // outerImp0 <=> (innerFA0 ==> Zero), with 0 ≠ 1: ¬innerFA0
      // innerFA0 <=> ∀(x :: A, innerPred0 * x), so ¬∀(x :: A, innerPred0 * x)
      // innerPred0 * x <=> ¬(P * x), so ¬∀(x :: A, ¬(P * x))
      // Classically: ∃(x :: A, P * x)

      assume(hexists(A) * P)
      // hexists(A) * P |- body, using beta: hexists(A) * P === body
      have(hexists(A) * P) by Restate
      thenHave(body) by Substitute(beta)
      have(∀(q :: 𝔹, outerPred * q)) by Tautology.from(lastStep, outerFALift)
      thenHave((Zero :: 𝔹) ==> (outerPred * Zero)) by InstantiateForall(Zero)
      have(outerPred * Zero) by Tautology.from(lastStep, Zero.justif)
      // outerPred * Zero |- outerImp0, using outerBeta0: outerPred * Zero === outerImp0
      thenHave(outerImp0) by Substitute(outerBeta0)
      have(innerFA0 ==> Zero) by Tautology.from(lastStep, outerImpLift0)
      have(!(innerFA0)) by Tautology.from(lastStep, `0 != 1`)
      have(!(∀(x :: A, innerPred0 * x))) by Tautology.from(lastStep, innerFALift0)

      // Now: ¬∀(x :: A, innerPred0 * x) and innerPred0 * x <=> ¬(P * x)
      // Need: ∃(x :: A, P * x)
      // Strategy: convert ¬∀ to ∃¬ (quantifier duality via Restate),
      // then bridge ∃(x :: A, ¬(innerPred0 * x)) to ∃(x :: A, P * x)
      // using innerPredNeg + RightExists + LeftExists.

      // Step 1: ¬∀(x :: A, innerPred0 * x) ↔ ∃(x :: A, ¬(innerPred0 * x))
      // (Restate handles this since ∃ unfolds to ¬∀¬ in the equivalence checker)
      val existsNotInner = have(∃(x :: A, !(innerPred0 * x))) by Restate.from(lastStep)

      // Step 2: Bridge: ∃(x :: A, ¬(innerPred0 * x)) ⊢ ∃(x :: A, P * x)
      // From innerPredNeg: innerPred0 * x <=> ¬(P * x), so ¬(innerPred0 * x) <=> P * x
      have((x :: A, !(innerPred0 * x)) |- (x :: A) /\ (P * x)) by Tautology.from(innerPredNeg)
      thenHave((x :: A, !(innerPred0 * x)) |- ∃(x :: A, P * x)) by RightExists
      // Merge separate x ∈ A into the conjunction for LeftExists
      thenHave((x :: A) /\ !(innerPred0 * x) |- ∃(x :: A, P * x)) by Restate
      thenHave(∃(x :: A, !(innerPred0 * x)) |- ∃(x :: A, P * x)) by LeftExists

      // Step 3: Combine
      have(thesis) by Tautology.from(existsNotInner, lastStep)

    // Backward direction: ∃(x :: A, P * x) |- hexists(A) * P
    val bwd = have(∃(x :: A, P * x) ==> (hexists(A) * P)) subproof:
      // Goal: ∃(x :: A, P * x) |- hexists(A) * P
      // Strategy: prove FOL core ∃(x :: A, P * x) |- ∀(q :: 𝔹, ∀(x :: A, P*x ==> q) ==> q)
      // then lift back to HOL terms.

      // FOL core:
      have((x :: A, q :: 𝔹, P * x, (x :: A) ==> ((P * x) ==> q)) |- q) by Restate
      thenHave((x :: A, q :: 𝔹, P * x, ∀(x :: A, (P * x) ==> q)) |- q) by LeftForall
      thenHave((x :: A) /\ (P * x) |- (q :: 𝔹) ==> (∀(x :: A, (P * x) ==> q) ==> q)) by Restate
      thenHave(∃(x, (x :: A) /\ (P * x)) |- (q :: 𝔹) ==> (∀(x :: A, (P * x) ==> q) ==> q)) by LeftExists
      thenHave(∃(x :: A, P * x) |- (q :: 𝔹) ==> (∀(x :: A, (P * x) ==> q) ==> q)) by Weakening
      thenHave(∃(x :: A, P * x) |- ∀(q :: 𝔹, ∀(x :: A, (P * x) ==> q) ==> q)) by RightForall
      val folResult = lastStep

      // Lift: convert ∀(q :: 𝔹, ∀(x :: A, P*x ==> q) ==> q) to body (= hexists(A)*P via beta)
      // Key equivalences (all carry typing assumptions on the left):
      //   innerPred * x <=> (P * x ==> q)   [innerImpLift + innerBeta] — has x ∈ A, q ∈ 𝔹 on left
      //   innerFA <=> ∀(x :: A, innerPred * x)  [innerFALift]
      //   outerImp <=> (innerFA ==> q)       [outerImpLift] — has innerFA ∈ 𝔹, q ∈ 𝔹 on left
      //   outerPred * q === outerImp         [outerBeta]
      //   body <=> ∀(q :: 𝔹, outerPred * q) [outerFALift]

      // innerPredEquiv: innerPred * x <=> (P * x ==> q)
      val innerPredEquiv = have(innerPred * x <=> (P * x ==> q)) subproof:
        have(innerImp <=> (P * x ==> q)) by Restate.from(innerImpLift)
        thenHave(thesis) by Substitute(innerBeta)

      // Forward: ∀(x :: A, P * x ==> q) ⊢ innerFA  (with q ∈ 𝔹 on left)
      have(∀(x :: A, P * x ==> q) |- (x :: A) ==> (P * x ==> q)) by InstantiateForall
      // Combine with innerPredEquiv to get innerPred * x; need x ∈ A and q ∈ 𝔹 for innerPredEquiv
      have((∀(x :: A, P * x ==> q), x :: A, q :: 𝔹) |- innerPred * x) by Tautology.from(lastStep, innerPredEquiv)
      // Move x ∈ A to right so RightForall can generalize over x
      thenHave((∀(x :: A, P * x ==> q), q :: 𝔹) |- (x :: A) ==> innerPred * x) by Restate
      thenHave((∀(x :: A, P * x ==> q), q :: 𝔹) |- ∀(x :: A, innerPred * x)) by RightForall
      have((∀(x :: A, P * x ==> q), q :: 𝔹) |- innerFA) by Tautology.from(lastStep, innerFALift)
      val forallToInnerFA = lastStep

      // Reverse: innerFA ⊢ ∀(x :: A, P * x ==> q)  (with q ∈ 𝔹 on left)
      have(∀(x :: A, innerPred * x) |- (x :: A) ==> innerPred * x) by InstantiateForall
      have((∀(x :: A, innerPred * x), x :: A, q :: 𝔹) |- (P * x ==> q)) by Tautology.from(lastStep, innerPredEquiv)
      thenHave((∀(x :: A, innerPred * x), q :: 𝔹) |- (x :: A) ==> (P * x ==> q)) by Restate
      thenHave((∀(x :: A, innerPred * x), q :: 𝔹) |- ∀(x :: A, P * x ==> q)) by RightForall
      have((innerFA, q :: 𝔹) |- ∀(x :: A, P * x ==> q)) by Tautology.from(lastStep, innerFALift)
      val innerFAToForall = lastStep

      // outerImp <=> (∀(x :: A, P * x ==> q) ==> q)  — with q ∈ 𝔹 on left
      have((q :: 𝔹) |- outerImp <=> (∀(x :: A, P * x ==> q) ==> q)) by Tautology.from(
        outerImpLift,
        forallToInnerFA,
        innerFAToForall,
        HOLProofType(innerFA)
      )
      val outerImpFOL = lastStep

      // outerPred * q <=> outerImp
      val outerPredEquiv = have(outerPred * q <=> outerImp) subproof:
        have(outerImp <=> outerImp) by Restate
        thenHave(thesis) by Substitute(outerBeta)

      // outerPred * q <=> (∀(x :: A, P * x ==> q) ==> q) — with q ∈ 𝔹 on left
      have((q :: 𝔹) |- outerPred * q <=> (∀(x :: A, P * x ==> q) ==> q)) by Tautology.from(outerPredEquiv, outerImpFOL)
      val outerPredFOL = lastStep

      // Convert: ∀(q :: 𝔹, ∀(x :: A, P*x ==> q) ==> q) |- ∀(q :: 𝔹, outerPred * q)
      have(∀(q :: 𝔹, ∀(x :: A, P * x ==> q) ==> q) |- (q :: 𝔹) ==> (∀(x :: A, P * x ==> q) ==> q)) by InstantiateForall
      // Combine with outerPredFOL: carry q ∈ 𝔹 explicitly
      have((∀(q :: 𝔹, ∀(x :: A, P * x ==> q) ==> q), q :: 𝔹) |- outerPred * q) by Tautology.from(lastStep, outerPredFOL)
      // Move q ∈ 𝔹 to right for RightForall
      thenHave(∀(q :: 𝔹, ∀(x :: A, P * x ==> q) ==> q) |- (q :: 𝔹) ==> outerPred * q) by Restate
      thenHave(∀(q :: 𝔹, ∀(x :: A, P * x ==> q) ==> q) |- ∀(q :: 𝔹, outerPred * q)) by RightForall

      // body
      have(∀(q :: 𝔹, ∀(x :: A, P * x ==> q) ==> q) |- body) by Tautology.from(lastStep, outerFALift)
      thenHave(∀(q :: 𝔹, ∀(x :: A, P * x ==> q) ==> q) |- hexists(A) * P) by Substitute(beta)

      // Cut folResult and lastStep on ∀(q :: 𝔹, ∀(x :: A, P*x ==> q) ==> q)
      val cutResult = have(∃(x :: A, P * x) |- hexists(A) * P) by Cut(folResult, lastStep)
      have(thesis) by Restate.from(cutResult)

    have(thesis) by RightAnd(fwd, bwd)

}
