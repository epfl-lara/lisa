package lisa.hol.basics

import lisa.automation.Substitution.{Apply => Substitute}
import lisa.hol.HOLHelperTheorems._
import lisa.hol.HOLSteps._
import lisa.hol.VarsAndFunctions._
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.utils.prooflib.BasicStepTactic._
import lisa.utils.prooflib.Library
import lisa.utils.prooflib.ProofTacticLib._
import lisa.utils.prooflib.SimpleDeducedSteps._

/**
 * HOL Light truth constant and related proofs.
 *
 * Defines:
 *  - _SYM / SYM (symmetry tactic)
 *  - holT (truth constant)
 *  - holTruth (proof that T holds)
 *  - oneTrue (proof that One holds)
 */
object Truth extends lisa.HOL {

  val A = typevar
  val B = typevar

  val x = typedvar(A)
  val y = typedvar(A)

  val p = typedvar(𝔹)
  val q = typedvar(𝔹)

  val lib = summon[Library]

  /**
   *     |- t = u
   *  ------------------
   *     |- u = t
   */
  object _SYM extends ProofTactic {
    def apply(using proof: Proof)(prem: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      prem.statement match {
        case HOLSequent(_, _, *(*(=:= #@ (typ), t), u)) =>
          prem.statement.left.foreach(ip.addAssumption(_))
          val s1 = have((t :: typ, u :: typ, t =:= u) |- u =:= t) by Weakening(eqSym of (A := typ, x := t, y := u))
          val s2 = have(Discharge(prem)(s1))
          val s3 = have(Discharge(have(HOLProofType(t)))(s2))
          val s4 = have(Discharge(have(HOLProofType(u)))(s3))
          have(Clean.all(s4))

        case _ =>
          return proof.InvalidProofTactic(s"The premise is not parseable as an HOL sequent")
      }
    }
  }

  /**
   * SYM: t = u |- u = t
   */
  def SYM(using line: sourcecode.Line, file: sourcecode.File)(using proof: library.Proof)(prem: proof.Fact) =
    have(_SYM(prem))

  /**
   * Truth as defined in HOL Light
   *
   * ```
   *  let T_DEF = new_basic_definition
   *   `T = ((\p:bool. p) = (\p:bool. p))`;;
   * ```
   */
  val holT: HOLConstant = {
    val holT = DEF(fun(p, p) =:= fun(p, p))

    val typing_of_T = Theorem(holT :: 𝔹) {
      have((fun(p, p) =:= fun(p, p)) :: 𝔹) by Typecheck.prove
      thenHave(thesis) by Substitute(holT.definition)
    }
    HOLConstant(holT.id, 𝔹, typing_of_T)
  }

  val holTruth = HOLTheorem(holT):
    REFL(fun(p, p))
    thenHave(thesis) by Substitute(holT.definition)

  val oneTrue = HOLTheorem(One):
    have(thesis) by RightRefl

}
