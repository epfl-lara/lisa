package lisa.hol.basics

import lisa.automation.Substitution.{Apply => Substitute}
import lisa.hol.HOLHelperTheorems
import lisa.hol.HOLHelperTheorems._
import lisa.hol.HOLSteps._
import lisa.hol.basics.Truth.{holT, holTruth, SYM}
import lisa.hol.basics.Forall.{hforall, hforallCorrect}
import lisa.hol.basics.False.{holF, holFalseZero}
import lisa.hol.VarsAndFunctions._
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.utils.prooflib.BasicStepTactic.LeftSubstEq
import lisa.utils.prooflib.BasicStepTactic.RightSubstEq
import lisa.utils.prooflib.BasicStepTactic.RightAnd
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.BasicStepTactic.Weakening
import lisa.utils.prooflib.BasicStepTactic._
import lisa.utils.prooflib.Library
import lisa.utils.prooflib.ProofTacticLib._
import lisa.utils.prooflib.SimpleDeducedSteps.Discharge
import lisa.utils.prooflib.SimpleDeducedSteps._

/**
 * HOL Light logical connectives: conjunction, implication, negation.
 *
 * Defines:
 *  - hand / handCorrect (conjunction)
 *  - himp / himpCorrect (implication)
 *  - hnot / hnotCorrect (negation)
 */
object Connectives extends lisa.HOL {

  val A = typevar

  val x = typedvar(A)
  val p = typedvar(𝔹)
  val q = typedvar(𝔹)

  val lib = summon[Library]

  // ─── Conjunction ───

  /**
   * Higher-order embedded conjunction.
   *
   * Defined as in HOL Light:
   * `(/\) = \p q. (\f:bool->bool->bool. f p q) = (\f. f T T)`
   */
  val hand: HOLPolymorphicConstant[Ind] = {
    val f = typedvar(𝔹 ->: 𝔹 ->: 𝔹)

    val hand = DEF(fun(p, fun(q, fun(f, f * p * q) =:= fun(f, f * holT * holT))))

    val typing_of_and = Theorem(hand :: (𝔹 ->: 𝔹 ->: 𝔹)) {
      have(fun(p, fun(q, fun(f, f * p * q) =:= fun(f, f * holT * holT))) :: (𝔹 ->: 𝔹 ->: 𝔹)) by Typecheck.prove
      thenHave(thesis) by Substitute(hand.definition)
    }

    HOLPolymorphicConstant[Ind](hand.id, FunctionalClass(List(), List(), (𝔹 ->: 𝔹 ->: 𝔹)), typing_of_and)
  }

  val handCorrect = HOLTheorem(
    (hand * p * q === One) <=> ((p === One) /\ (q === One))
  ):
    assumeAll

    val f = typedvar(𝔹 ->: 𝔹 ->: 𝔹)
    val proj1 = fun(p, fun(q, p))
    val proj2 = fun(p, fun(q, q))

    val `beta f` = BETA(fun(f, f * p * q) * f)

    val leftProjection = // proj1 * p * q = p
      TRANS(
        MK_COMB(BETA(proj1 * p), REFL(q)),
        BETA(fun(q, p) * q)
      )
    val rightProjection = // proj2 * p * q = q
      TRANS(
        MK_COMB(BETA(proj2 * p), REFL(q)),
        BETA(fun(q, q) * q)
      )

    val `beta hand` = have(
      hand * p * q === (fun(f, f * p * q) =:= fun(f, f * holT * holT))
    ) subproof {
      val inner = fun(f, f * p * q) =:= fun(f, f * holT * holT)
      val lq = fun(q, inner)
      val lp = fun(p, lq)
      val betaLp = // lp * p * q =:= inner
        TRANS(
          MK_COMB(
            BETA_CONV(lp * p), // lp * p = lq
            REFL(q)
          ),
          BETA_CONV(lq * q) // lq * q = inner
        )
      have(lp * p * q === inner) by Tautology.from(
        betaLp,
        have(HOLProofType(lp * p * q)),
        have(HOLProofType(inner)),
        eqAlign of (A := 𝔹, x := lp * p * q, y := inner)
      )
      thenHave(hand === lp |- hand * p * q === inner) by RightSubstEq.withParameters(Seq((hand, lp)), (Seq(x), x * p * q === inner))
      have(hand * p * q === inner) by Cut(hand.definition, lastStep)
    }

    val fwd = lib.have((hand * p * q === One) ==> ((p === One) /\ (q === One))) subproof:
      val reducedProof = have(fun(f, f * p * q) =:= fun(f, f * holT * holT) |- (p === One) /\ (q === One)) subproof {
        assumeAll
        val andEq = have(fun(f, f * p * q) =:= fun(f, f * holT * holT)) by Restate

        // ((\p q. f p q) f) holT holT = ((\p q. f p q) f) p q
        val appliedEq =
          have(
            Clean.all(
              // f holT holT = f p q
              SYM(
                TRANS(
                  // (\p q. f p q) f holT holT = f p q
                  TRANS(
                    SYM(`beta f`),
                    MK_COMB(andEq, REFL(f))
                  ),
                  have(Discharge(holT.justif)(`beta f` of (p := holT, q := holT)))
                )
              )
            )
          )
        val `p is true` = have(p) subproof:
          // project appliedEq onto first argument
          val proj1Eq =
            have(Discharge(have(HOLProofType(proj1)))(appliedEq of (f := proj1)))
          // T =:= p
          val tEq = TRANS(
            SYM(
              have(Discharge(holT.justif)(leftProjection of (p := holT, q := holT)))
            ),
            TRANS(proj1Eq, leftProjection)
          )
          EQ_MP(tEq, holTruth)
          thenHave(thesis) by Weakening

        val `q is true` = have(q) subproof:
          // project appliedEq onto second argument
          val proj2Eq =
            have(Discharge(have(HOLProofType(proj2)))(appliedEq of (f := proj2)))
          // T =:= q
          val tEq = TRANS(
            SYM(
              have(Discharge(holT.justif)(rightProjection of (p := holT, q := holT)))
            ),
            TRANS(proj2Eq, rightProjection)
          )
          EQ_MP(tEq, holTruth)
          thenHave(thesis) by Weakening

        have(p /\ q) by RightAnd(`p is true`, `q is true`)
        have(Clean.all(lastStep))
      }

      have((hand * p * q === One) |- ((p === One) /\ (q === One))) by Substitute(`beta hand`)(reducedProof)

    val bwd = have(((p === One) /\ (q === One)) ==> (hand * p * q === One)) subproof:
      val rfl = have(fun(f, f * holT * holT) :: (𝔹 ->: 𝔹 ->: 𝔹) ->: 𝔹 |- fun(f, f * holT * holT) =:= fun(f, f * holT * holT)) by Tautology.from(
        HOLHelperTheorems.eqRefl of (A := (𝔹 ->: 𝔹 ->: 𝔹) ->: 𝔹, x := fun(f, f * holT * holT))
      )
      have(fun(f, f * holT * holT) =:= fun(f, f * holT * holT)) by Cut(have(HOLProofType(fun(f, f * holT * holT))), rfl)
      thenHave((p === holT, q === holT) |- fun(f, f * p * q) =:= fun(f, f * holT * holT)) by RightSubstEq.withParameters(
        Seq(p -> holT, q -> holT),
        (Seq(p, q), fun(f, f * p * q) =:= fun(f, f * holT * holT))
      )
      thenHave((holT === One, p === One, q === holT) |- fun(f, f * p * q) =:= fun(f, f * holT * holT)) by LeftSubstEq.withParameters(Seq(holT -> One), (Seq(x), p === x))
      thenHave((holT === One, p === One, q === One) |- fun(f, f * p * q) =:= fun(f, f * holT * holT)) by LeftSubstEq.withParameters(Seq(holT -> One), (Seq(x), q === x))
      lib.have((p === One, q === One) |- fun(f, f * p * q) =:= fun(f, f * holT * holT)) by Cut(holTruth, lastStep)
      thenHave((p === One, q === One) |- hand * p * q === One) by Substitute(`beta hand`)
      have(Clean.all(lastStep))

    have(thesis) by RightAnd(fwd, bwd)

  // ─── Implication ───

  /**
   * Higher-order embedded implication.
   *
   * Defined as in HOL Light:
   * `(==>) = \p q. p /\ q <=> p`
   */
  val himp: HOLPolymorphicConstant[Ind] = {

    val p = typedvar(𝔹)
    val q = typedvar(𝔹)

    val himp = DEF(fun(p, fun(q, (hand * p * q) =:= p)))

    val typing_of_imp = Theorem(himp :: (𝔹 ->: 𝔹 ->: 𝔹)) {
      have(fun(p, fun(q, (hand * p * q) =:= p)) :: (𝔹 ->: 𝔹 ->: 𝔹)) by Typecheck.prove
      thenHave(thesis) by Substitute(himp.definition)
    }

    HOLPolymorphicConstant[Ind](himp.id, FunctionalClass(List(), List(), (𝔹 ->: 𝔹 ->: 𝔹)), typing_of_imp)
  }

  val himpCorrect = HOLTheorem(
    (himp * p * q === One) <=> ((p === One) ==> (q === One))
  ):
    assumeAll

    val apq = hand * p * q
    val apqtyping = have(HOLProofType(apq))

    val beta = have(
      (himp * p * q) === ((hand * p * q) =:= p)
    ) subproof:
      val inner = (hand * p * q) =:= p
      val lq = fun(q, inner)
      val lp = fun(p, lq)
      val betaLp = // lp * p * q =:= inner
        TRANS(
          MK_COMB(
            BETA_CONV(lp * p), // lp * p = lq
            REFL(q)
          ),
          BETA_CONV(lq * q) // lq * q = inner
        )
      have(lp * p * q === inner) by Tautology.from(
        betaLp,
        have(HOLProofType(lp * p * q)),
        have(HOLProofType(inner)),
        eqAlign of (A := 𝔹, x := lp * p * q, y := inner)
      )
      thenHave(thesis) by Substitute(himp.definition)

    val restricted = have((hand * p * q === p) <=> (p ==> q)) subproof:
      // case split on hand p  q 0 or 1, in each case it follows by
      // propositional reasoning on handCorrect
      val cases = have((apq === One) \/ (apq === Zero)) by Tautology.from(apqtyping, boolBivalence of (x := apq))

      val `and true` = have(apq === One |- (apq === p) <=> (p ==> q)) subproof:
        have(apq === One |- (One === p) <=> (p ==> q)) by Tautology.from(handCorrect)
        thenHave(apq === One |- (apq === p) <=> (p ==> q)) by RightSubstEq.withParameters(Seq(apq -> One), (Seq(x), (x === p) <=> (p ==> q)))

      val `and false` = have(apq === Zero |- (apq === p) <=> (p ==> q)) subproof:
        have(apq === Zero |- (Zero === p) <=> (p ==> q)) by Tautology.from(
          handCorrect,
          boolBivalence of (x := p),
          boolBivalence of (x := q),
          boolBivalence of (x := apq),
          boolZeroXorOne of (x := p),
          boolZeroXorOne of (x := q),
          boolZeroXorOne of (x := apq)
        )
        thenHave(apq === Zero |- (apq === p) <=> (p ==> q)) by RightSubstEq.withParameters(Seq(apq -> Zero), (Seq(x), (x === p) <=> (p ==> q)))

      have(thesis) by Tautology.from(cases, `and true`, `and false`)

    have((apq :: 𝔹) |- (hand * p * q =:= p) <=> (p ==> q)) by Substitute(eqAlign)(restricted)
    thenHave(apq :: 𝔹 |- (himp * p * q) <=> (p ==> q)) by Substitute(beta)
    have(thesis) by Cut(apqtyping, lastStep)

  // ─── Negation ───

  /**
   * Higher-order embedded negation.
   *
   * Defined as in HOL Light:
   * `(~) = \p. p ==> F`
   * where F (HOL False) is Zero in the set-theoretic embedding.
   */
  val hnot: HOLPolymorphicConstant[Ind] = {
    val p = typedvar(𝔹)

    val hnot = DEF(fun(p, himp * p * holF))

    val typing_of_not = Theorem(hnot :: (𝔹 ->: 𝔹)) {
      have(fun(p, himp * p * holF) :: (𝔹 ->: 𝔹)) by Typecheck.prove
      thenHave(thesis) by Substitute(hnot.definition)
    }

    HOLPolymorphicConstant[Ind](hnot.id, FunctionalClass(List(), List(), (𝔹 ->: 𝔹)), typing_of_not)
  }

  val hnotCorrect = HOLTheorem(
    (hnot * p === One) <=> !(p === One)
  ):
    assumeAll

    val hnoteq =
      have(hnot === fun(p, himp * p * holF)) by Weakening(hnot.definition)
      have(hnot =:= fun(p, himp * p * holF)) by Tautology.from(
        lastStep,
        have(HOLProofType(hnot)),
        have(HOLProofType(fun(p, himp * p * holF))),
        eqAlign of (A := (𝔹 ->: 𝔹), x := hnot, y := fun(p, himp * p * holF))
      )

    val beta = // hnot * p = himp * p * holF
      val betaConv =
        TRANS(
          MK_COMB( // hnot * p = (\p. himp * p * holF) * p
            hnoteq,
            REFL(p)
          ),
          BETA_CONV(fun(p, himp * p * holF) * p)
        )
      have(hnot * p === himp * p * holF) by Tautology.from(
        betaConv,
        have(HOLProofType(hnot * p)),
        have(HOLProofType(himp * p * holF)),
        eqAlign of (A := 𝔹, x := hnot * p, y := himp * p * holF)
      )

    val impCorrect =
      have((p ==> Zero) <=> (p ==> Zero)) by Restate
      thenHave((Zero ∈ 𝔹) |- (himp * p * Zero) <=> (p ==> Zero)) by Substitute(himpCorrect)
      have((himp * p * Zero) <=> (p ==> Zero)) by Cut(Zero.justif, lastStep)
      thenHave((himp * p * holF) <=> (p ==> Zero)) by Substitute(holFalseZero)

    have((p ==> Zero) <=> !(p === One)) by Tautology.from(
      `0 != 1`,
      boolBivalence of (x := p),
      boolZeroXorOne of (x := p)
    )
    thenHave((himp * p * holF) <=> !(p === One)) by Substitute(impCorrect)
    thenHave((hnot * p) <=> !(p === One)) by Substitute(beta)

}
