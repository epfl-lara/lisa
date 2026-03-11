package lisa.hol

import lisa.automation.Substitution.{Apply => Substitute}
import lisa.hol.HOLHelperTheorems._
import lisa.hol.HOLSteps._
import lisa.hol.VarsAndFunctions._
import lisa.hol.basics.Truth._
import lisa.hol.basics.Forall._
import lisa.hol.basics.False._
import lisa.hol.basics.Connectives._
import lisa.hol.basics.Exists._
import lisa.hol.basics.Select._
import lisa.hol.basics.Inductive._
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.maths.SetTheory.Types.TypingRules.BetaReduction
import lisa.maths.SetTheory.Types.TypingRules.TAbs
import lisa.utils.prooflib.BasicStepTactic._
import lisa.utils.prooflib.Library
import lisa.utils.prooflib.ProofTacticLib._
import lisa.utils.prooflib.SimpleDeducedSteps._

/**
 * HOL Light axioms: ETA_AX, INFINITY_AX, SELECT_AX.
 *
 * All operators (holT, holTruth, hforall, holF, hand, himp, hnot, hexists,
 * hselect, hOneOne, hOnto, ind, succ, etc.) are defined in lisa.hol.basics
 * and re-exported here.
 */
object HOLBasics extends lisa.HOL {

  val A = typevar
  val B = typevar

  val x = typedvar(A)
  val y = typedvar(A)
  val P = typedvar(A ->: 𝔹)

  val lib = summon[Library]

  // Re-export all definitions from basics sub-objects
  export lisa.hol.basics.Truth.{holT, holTruth, SYM, _SYM}
  export lisa.hol.basics.Forall.{hforall, hforallCorrect}
  export lisa.hol.basics.False.{holF, holFalseZero}
  export lisa.hol.basics.Connectives.{hand, handCorrect, himp, himpCorrect, hnot, hnotCorrect, p, q}
  export lisa.hol.basics.Exists.{hexists, hexistsCorrect}
  export lisa.hol.basics.Select.{hselect}
  export lisa.hol.basics.Inductive.{hOneOne, hOnto, ind, holeqBetaReduced}

  ////////////////////////////////////////////////////
  // HOL Light axioms
  // ETA_AX, INFINITY_AX, SELECT_AX

  val t = typedvar(A ->: B)

  /**
   * ETA_AX
   *
   * ```ocaml
   * let ETA_AX = new_axiom
   *   `!t:A->B. (\x. t x) = t`;;
   * ```
   */
  val etaAx = HOLTheorem(hforall(A ->: B) * fun(t, fun(x, t * x) =:= t)):
    assumeAll
    val pred = fun(t, fun(x, t * x) =:= t)

    val beta = have(pred * t === (fun(x, t * x) =:= t)) subproof:
      val bc = BETA_CONV(pred * t)
      have(thesis) by Tautology.from(
        bc,
        eqAlign of (A := 𝔹, x := pred * t, y := (fun(x, t * x) =:= t)),
        have(HOLProofType(pred * t)),
        have(HOLProofType(fun(x, t * x) =:= t))
      )

    have(pred * t) by Substitute(beta)(ETA(x, t))

    thenHave((t :: (A ->: B)) ==> (pred * t)) by Restate
    thenHave(∀(t :: (A ->: B), pred * t)) by RightForall

    have(thesis) by Tautology.from(
      lastStep,
      hforallCorrect of (A := (A ->: B), P := pred, x := t),
      have(HOLProofType(pred)),
      nonEmptyFuncSpace of (A := A, B := B)
    )

  val fi = typedvar(ind ->: ind)

  /**
   * INFINITY_AX
   *
   * ```ocaml
   * let INFINITY_AX = new_axiom
   *  `?f:ind->ind. ONE_ONE f /\ ~(ONTO f)`;;
   * ```
   */
  val infinityAx = HOLTheorem(
    hexists(ind ->: ind) * fun(
      fi,
      hand *
        (hOneOne(ind)(ind) * fi) *
        (hnot * (hOnto(ind)(ind) * fi))
    )
  ):
    val pred = fun(fi, hand * (hOneOne(ind)(ind) * fi) * (hnot * (hOnto(ind)(ind) * fi)))

    val beta = have(pred * succ === (hand * (hOneOne(ind)(ind) * succ) * (hnot * (hOnto(ind)(ind) * succ)))) subproof:
      val bc = BETA_CONV(pred * succ)
      have(thesis) by Tautology.from(
        bc,
        eqAlign of (A := 𝔹, x := pred * succ, y := hand * (hOneOne(ind)(ind) * succ) * (hnot * (hOnto(ind)(ind) * succ))),
        have(HOLProofType(pred * succ)),
        have(HOLProofType(hand * (hOneOne(ind)(ind) * succ) * (hnot * (hOnto(ind)(ind) * succ))))
      )

    // Combine succOneOne and succNotOnto
    val conjunct = have(hand * (hOneOne(ind)(ind) * succ) * (hnot * (hOnto(ind)(ind) * succ)) === One) by Tautology.from(
      handCorrect of (p := hOneOne(ind)(ind) * succ, q := hnot * (hOnto(ind)(ind) * succ)),
      have(HOLProofType(hOneOne(ind)(ind) * succ)),
      have(HOLProofType(hnot * (hOnto(ind)(ind) * succ))),
      succOneOne,
      succNotOnto
    )

    val predSucc = have(pred * succ) by Substitute(beta)(conjunct)

    have((succ :: (ind ->: ind)) /\ (pred * succ)) by Tautology.from(predSucc, succ.justif)
    thenHave(∃(fi :: (ind ->: ind), pred * fi)) by RightExists

    have(thesis) by Tautology.from(
      lastStep,
      hexistsCorrect of (A := (ind ->: ind), P := pred, x := fi),
      have(HOLProofType(pred)),
      nonEmptyFuncSpace of (A := ind, B := ind)
    )

  /**
   * SELECT_AX
   *
   * ```ocaml
   * let SELECT_AX = new_axiom
   *  `!P (x:A). P x ==> P((@) P)`;;
   * ```
   */
  val selectAx = HOLTheorem(
    hforall(A ->: 𝔹) * fun(P, hforall(A) * fun(x, himp * (P * x) * (P * (hselect(A) * P))))
  ):
    assumeAll
    val innerPred = fun(x, himp * (P * x) * (P * (hselect(A) * P)))
    val outerPred = fun(P, hforall(A) * fun(x, himp * (P * x) * (P * (hselect(A) * P))))

    // from selectWellDefined, get P * selectTerm === One when there's a witness
    // selectWellDefined: |- selectProp(selectTerm)
    //   = (selectTerm :: A) /\ (∃(y, (y :: A) /\ (P * y === One)) ==> (P * selectTerm === One))
    val selectFact = have(selectWellDefined)

    // assuming P * x, derive P * (hselect(A) * P)
    val core = have((P :: (A ->: 𝔹), x :: A, P * x === One) |- (P * (hselect(A) * P) === One)) subproof:
      have((x :: A) /\ (P * x === One) |- (x :: A) /\ (P * x === One)) by Hypothesis
      have((x :: A) /\ (P * x === One) |- ∃(x, (x :: A) /\ (P * x === One))) by RightExists.withParameters(x)(lastStep)
      val witness = have((P :: (A ->: 𝔹), (x :: A) /\ (P * x === One)) |- ∃(x, (x :: A) /\ (P * x === One))) by Weakening(lastStep)
      
      val T = variable[Ind]
      val e = variable[Ind >>: Ind]
      val e2 = variable[Ind]
      val selectBR = have(fun(P, selectTerm) * P === selectTerm) by Weakening(BetaReduction of (T := A ->: 𝔹, e2 := P, e := λ(P, selectTerm)))
      // prove P * selectTerm === One, then substitute to fold back
      have((P :: (A ->: 𝔹), x :: A, P * x === One) |- (P * selectTerm === One)) by Tautology.from(selectFact, witness)
      thenHave((P :: (A ->: 𝔹), x :: A, P * x === One) |- (P * (fun(P, selectTerm) * P) === One)) by Substitute(selectBR)

      thenHave(thesis) by Substitute(hselect.definition)

    val impStep = have((P :: (A ->: 𝔹), x :: A) |- himp * (P * x) * (P * (hselect(A) * P))) subproof:
      have(thesis) by Tautology.from(
        core,
        himpCorrect of (p := P * x, q := P * (hselect(A) * P)),
        have(HOLProofType(P * x)),
        have(HOLProofType(P * (hselect(A) * P)))
      )

    // Beta reduce innerPred * x
    val innerBeta = have(innerPred * x === (himp * (P * x) * (P * (hselect(A) * P)))) subproof:
      val bc = BETA_CONV(innerPred * x)
      have(thesis) by Tautology.from(
        bc,
        eqAlign of (A := 𝔹, x := innerPred * x, y := himp * (P * x) * (P * (hselect(A) * P))),
        have(HOLProofType(innerPred * x)),
        have(HOLProofType(himp * (P * x) * (P * (hselect(A) * P))))
      )

    // innerPred * x holds for all x :: A
    have((P :: (A ->: 𝔹), x :: A) |- innerPred * x) by Substitute(innerBeta)(impStep)
    thenHave((P :: (A ->: 𝔹)) |- (x :: A) ==> (innerPred * x)) by Restate
    thenHave((P :: (A ->: 𝔹)) |- ∀(x :: A, innerPred * x)) by RightForall

    val innerForall = have((P :: (A ->: 𝔹)) |- hforall(A) * innerPred) by Tautology.from(
      lastStep,
      hforallCorrect of (A := A, P := innerPred, x := x),
      have(HOLProofType(innerPred))
    )

    val outerBeta = have(outerPred * P === (hforall(A) * innerPred)) subproof:
      val bc = BETA_CONV(outerPred * P)
      have(thesis) by Tautology.from(
        bc,
        eqAlign of (A := 𝔹, x := outerPred * P, y := hforall(A) * innerPred),
        have(HOLProofType(outerPred * P)),
        have(HOLProofType(hforall(A) * innerPred))
      )

    have((P :: (A ->: 𝔹)) |- outerPred * P) by Substitute(outerBeta)(innerForall)
    thenHave((P :: (A ->: 𝔹)) ==> (outerPred * P)) by Restate
    thenHave(∀(P :: (A ->: 𝔹), outerPred * P)) by RightForall

    have(thesis) by Tautology.from(
      lastStep,
      hforallCorrect of (A := (A ->: 𝔹), P := outerPred, x := P),
      have(HOLProofType(outerPred)),
      nonEmptyFuncSpace of (A := A, B := 𝔹),
      𝔹.nonEmptyThm
    )

}
