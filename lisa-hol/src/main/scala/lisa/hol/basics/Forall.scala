package lisa.hol.basics

import lisa.automation.Substitution.{Apply => Substitute}
import lisa.hol.HOLHelperTheorems._
import lisa.hol.HOLSteps._
import lisa.hol.basics.Truth.{_SYM, SYM, holT, holTruth, oneTrue}
import lisa.hol.VarsAndFunctions._
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.utils.prooflib.BasicStepTactic._
import lisa.utils.prooflib.Library
import lisa.utils.prooflib.ProofTacticLib._
import lisa.utils.prooflib.SimpleDeducedSteps._

/**
 * HOL Light universal quantifier.
 *
 * Defines:
 *  - hforall (polymorphic constant)
 *  - hforallCorrect (correctness theorem)
 */
object Forall extends lisa.HOL {

  val A = typevar

  val x = typedvar(A)
  val P = typedvar(A ->: 𝔹)

  val lib = summon[Library]

  /**
   * Higher-order embedded universal quantifier.
   *
   * ```
   * let FORALL_DEF = new_basic_definition
   *   `(!) = \P:A->bool. P = \x. T`;;
   * ```
   */
  val hforall: HOLPolymorphicConstant[Ind >>: Ind] = {

    val f = typedvar(A ->: 𝔹)
    val a = typedvar(A)
    val x = typedvar(A)

    val hforall = DEF(λ(A, fun(f, f =:= fun(a, holT))))

    val typing_of_forall = Theorem(∀(A, nonEmpty(A) ==> hforall(A) :: ((A ->: 𝔹) ->: 𝔹))) {
      have(fun(f, f =:= fun(a, holT)) :: ((A ->: 𝔹) ->: 𝔹)) by Typecheck.prove
      thenHave(∃(x, x :: A) |- hforall(A) :: ((A ->: 𝔹) ->: 𝔹)) by Substitute(hforall.definition)
      thenHave(nonEmpty(A) ==> hforall(A) :: ((A ->: 𝔹) ->: 𝔹)) by Restate
      thenHave(thesis) by RightForall
    }

    HOLPolymorphicConstant[Ind >>: Ind](hforall.id, FunctionalClass(List(None), List(A), ((A ->: 𝔹) ->: 𝔹)), typing_of_forall)
  }

  val hforallCorrect = HOLTheorem(
    (hforall(A) * P) <=> ∀(x :: A, P * x)
  ):
    assumeAll
    val f = typedvar(A ->: 𝔹)

    val beta = have(hforall(A) * P === (P =:= fun(x, holT))) subproof:
      BETA(fun(P, P =:= fun(x, holT)) * P)
      val heq = thenHave((hforall(A) * P) =:= (P =:= fun(x, holT))) by Substitute(hforall.definition)
      have(thesis) by Tautology.from(
        heq,
        eqAlign of (A := 𝔹, x := hforall(A) * P, y := P =:= fun(x, holT)),
        have(HOLProofType(hforall(A) * P)),
        have(HOLProofType(P =:= fun(x, holT)))
      )

    val fwd = have((hforall(A) * P) ==> ∀(x :: A, P * x)) subproof: ip ?=>
      val `P x one` =
        TRANS( // P * x =:= holT
          MK_COMB( // P * x =:= fun(x, holT) * x
            ASSUME(P =:= fun(x, holT)),
            REFL(x)
          ),
          BETA_CONV(fun(x, holT) * x) // fun(x, holT) * x =:= holT
        )
      val `P x holds` = // |- P * x
        EQ_MP(SYM(`P x one`), holTruth)

      lib.have(P =:= fun(x, holT) |- (x :: A) ==> P * x) by Weakening(`P x holds`)
      thenHave(P =:= fun(x, holT) |- ∀(x :: A, P * x)) by RightForall
      thenHave(hforall(A) * P |- ∀(x :: A, P * x)) by Substitute(beta)
      thenHave(thesis) by Weakening

    val bwd = have(∀(x :: A, P * x) ==> (hforall(A) * P)) subproof:
      have(∀(x :: A, P * x) |- (x :: A) ==> P * x) by InstantiateForall
      val `P x holds` = have(∀(x :: A, P * x) |- P * x) by Weakening(lastStep)
      val `P x one` = have(∀(x :: A, P * x) |- P * x =:= One) by Tautology.from(`P x holds`, One.justif, have(HOLProofType(P * x)), eqAlign of (A := 𝔹, x := P * x, y := One))
      val `P x T` = have(∀(x :: A, P * x) |- P * x =:= holT) by Substitute(holTruth)(`P x one`)
      val Peq = have(
        Clean.all( // P =:= fun(x, holT)
          TRANS(
            SYM(ETA(x, P)),
            ABS(x)(`P x T`)
          )
        )
      )
      have(∀(x :: A, P * x) |- hforall(A) * P) by Substitute(beta)(Peq)
      thenHave(thesis) by Weakening

    have(thesis) by RightAnd(fwd, bwd)

}
