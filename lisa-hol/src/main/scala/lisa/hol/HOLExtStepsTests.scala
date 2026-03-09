package lisa.hol

import lisa.automation.Substitution.{Apply => Substitute}
import lisa.hol.HOLHelperTheorems._
import lisa.hol.HOLSteps._
import lisa.hol.VarsAndFunctions._
import lisa.maths.SetTheory.Base.Pair.given
import lisa.maths.SetTheory.Base.Replacement.|
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.maths.SetTheory.Types.TypingRules.BetaReduction
import lisa.maths.SetTheory.Types.TypingRules.TAbs
import lisa.utils.prooflib.BasicStepTactic._
import lisa.utils.prooflib.Library
import lisa.utils.prooflib.ProofTacticLib._
import lisa.utils.prooflib.SimpleDeducedSteps._
import lisa.utils.unification.UnificationUtils.Substitution
import lisa.utils.prooflib.BasicStepTactic.RightSubstEq
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.BasicStepTactic.RightAnd
import lisa.utils.prooflib.BasicStepTactic.Weakening
import lisa.utils.prooflib.BasicStepTactic.RightSubstEq
import lisa.utils.prooflib.BasicStepTactic.Weakening
import lisa.utils.unification.UnificationUtils.Substitution
import lisa.utils.prooflib.BasicStepTactic.RightSubstEq
import lisa.utils.prooflib.SimpleDeducedSteps.Discharge
import lisa.utils.unification.UnificationUtils.Substitution
import lisa.utils.prooflib.BasicStepTactic.LeftSubstEq

import lisa.hol.ExtendedHOLSteps._INST_TYPE_RENAME
import lisa.hol.Import.mkTypedVar

import lisa.hol.HOLBasics.{SYM}

object HOLExtStepsTests extends lisa.HOL {
  draft()

  val A = typevar
  val B = typevar
  val T = typevar

  val x = typedvar(A)
  val y = typedvar(A)
  val z = typedvar(A)
  val P = typedvar(A ->: 𝔹)

  val f = typedvar(A ->: B)
  val g = typedvar(A ->: B)

  val p = typedvar(𝔹)
  val q = typedvar(𝔹)

  val φ = variable[Prop]

  val lib = summon[Library]


  val holeqBetaReduced = HOLTheorem(
    holeq(A) =:= fun(x, fun(y, x =:= y))
  ):
    SYM(TRANS(
      ABS(x)( // fun(x, fun(y, x =:= y)) =:= fun(x, holeq(A) * x)
        ETA(y, holeq(A) * x) // fun(y, holeq(A) * x * y) =:= holeq(A) * x
      ),
      ETA(x, holeq(A)) // fun(x, holeq(A) * x) =:= holeq(A)
    ))

  val holeqBetaReducedFull = HOLTheorem(
    holeq(A)*z*z =:= fun(x, fun(y, x =:= y))*z*z
  ):
    sorry




  val xb = mkTypedVar("x", B)
  val yb = mkTypedVar("y", B)
  val instTypeTest1 = HOLTheorem(
    holeq(B) =:= fun(xb, fun(yb, xb =:= yb))
  ):
    have(_INST_TYPE_RENAME(Seq((A, B)), holeqBetaReduced))



  val xba = mkTypedVar("x", A ->: B)
  val yba = mkTypedVar("y", A ->: B)
  val instTypeTest2 = HOLTheorem(
    holeq(A ->: B) =:= fun(xba, fun(yba, xba =:= yba))
  ):
    have(_INST_TYPE_RENAME(Seq((A, A ->: B)), holeqBetaReduced))



  val fba = mkTypedVar("f", A ->: B)
  val zba = mkTypedVar("z", A ->: B)
  val instTypeTest3 = HOLTheorem(
    (holeq(A ->: B)*zba*zba) =:= (fun(xba, fun(yba, xba =:= yba))*zba*zba)
  ):
    val s1 = have(_INST_TYPE_RENAME(Seq((A, A ->: B)), holeqBetaReducedFull))




  val instTypeTest4 = HOLTheorem(
    (holeq(A ->: B)*fba*fba) =:= (fun(xba, fun(yba, xba =:= yba))*fba*fba)
  ):
    val s1 = have(_INST_TYPE_RENAME(Seq((A, A ->: B)), holeqBetaReducedFull))
    have(_INST(Seq((zba, fba)), s1))

}