package lisa.hol.basics

import lisa.automation.Substitution.{Apply => Substitute}
import lisa.hol.HOLHelperTheorems._
import lisa.hol.HOLSteps._
import lisa.hol.basics.Truth.{holT, holTruth}
import lisa.hol.basics.Forall.{hforall, hforallCorrect}
import lisa.hol.VarsAndFunctions._
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.utils.prooflib.BasicStepTactic._
import lisa.utils.prooflib.Library
import lisa.utils.prooflib.ProofTacticLib._
import lisa.utils.prooflib.SimpleDeducedSteps._

/**
 * HOL Light false constant and related proofs.
 *
 * Defines:
 *  - holF (false constant)
 *  - holFalseZero (proof that F = Zero)
 */
object False extends lisa.HOL {

  val p = typedvar(𝔹)

  val lib = summon[Library]

  /**
   * False as defined in HOL Light
   *
   * ```
   * let F_DEF = new_basic_definition
   *  `F = (!p:bool. p)`;;
   * ```
   */
  val holF: HOLConstant = {
    val holF = DEF(hforall(𝔹) * fun(p, p))

    val typing_of_F = Theorem(holF :: 𝔹) {
      have(∃(p, p :: 𝔹) |- hforall(𝔹) * fun(p, p) :: 𝔹) by Typecheck.prove
      have(hforall(𝔹) * fun(p, p) :: 𝔹) by Cut(𝔹.nonEmptyThm, lastStep)
      thenHave(thesis) by Substitute(holF.definition)
    }

    HOLConstant(holF.id, 𝔹, typing_of_F)
  }

  val holFalseZero = HOLTheorem(holF === Zero):
    lib.have(∀(p :: 𝔹, fun(p, p) * p) |- ()) subproof:
      val beta = have((Zero :: 𝔹) |- (fun(p, p) * Zero === Zero)) subproof:
        BETA_CONV(fun(p, p) * Zero)
        val conditional = thenHave(((fun(p, p) * Zero) :: 𝔹, Zero :: 𝔹) |- fun(p, p) * Zero === Zero) by Substitute(eqAlign)
        have(Discharge(have(HOLProofType(fun(p, p) * Zero)))(conditional))
      have(!(Zero === One)) by Weakening(`0 != 1`)
      thenHave((Zero :: 𝔹) |- !(fun(p, p) * Zero === One)) by Substitute(beta)
      lib.have((Zero :: 𝔹) /\ !(fun(p, p) * Zero === One)) by Tautology.from(Zero.justif, lastStep)
      thenHave(∃(p :: 𝔹, !(fun(p, p) * p))) by RightExists

    val conditional = thenHave((∃(p, p :: 𝔹), fun(p, p) :: (𝔹 ->: 𝔹), hforall(𝔹) * fun(p, p)) |- ()) by Substitute(hforallCorrect)
    have(Discharge(𝔹.nonEmptyThm, have(HOLProofType(fun(p, p))))(conditional))
    thenHave(holF |- ()) by Substitute(holF.definition)
    have(thesis) by Tautology.from(boolZeroXorOne of (x := holF), holF.justif, lastStep)

}
