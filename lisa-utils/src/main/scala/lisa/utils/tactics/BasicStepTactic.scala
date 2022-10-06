package lisa.utils.tactics

import lisa.kernel.proof.SequentCalculus.{SCProofStep, Sequent}
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.{SCProof, SequentCalculus as SC}
import lisa.utils.Library
import lisa.utils.tactics.ProofStepLib.{*, given}

object BasicStepTactic {

  case object Hypothesis extends ProofStepWithoutBotNorPrem(0) {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.Hypothesis(bot, bot.left.intersect(bot.right).head)
  }

  case object Rewrite extends ProofStepWithoutBotNorPrem(1) {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.Rewrite(bot, premises(0))
  }

  /**
   * <pre>
   *  Γ |- Δ, φ    φ, Σ |- Π
   * ------------------------
   *       Γ, Σ |-Δ, Π
   * </pre>
   */
  case class Cut(phi: Formula) extends ProofStepWithoutBotNorPrem(2) {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.Cut(bot, premises(0), premises(1), phi)
  }

  // Left rules
  /**
   * <pre>
   *   Γ, φ |- Δ                Γ, φ, ψ |- Δ
   * --------------     or     --------------
   *  Γ, φ∧ψ |- Δ               Γ, φ∧ψ |- Δ
   * </pre>
   */
  case class LeftAnd(phi: Formula, psi: Formula) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.LeftAnd(bot, premises(0), phi, psi)
  }

  /**
   * <pre>
   *  Γ, φ |- Δ    Σ, ψ |- Π    ...
   * --------------------------------
   *    Γ, Σ, φ∨ψ∨... |- Δ, Π
   * </pre>
   */
  case class LeftOr(t: Seq[Int], disjuncts: Seq[Formula]) extends ProofStepWithoutBotNorPrem(-1) {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      SC.LeftOr(bot, t, disjuncts)
    }
  }

  /**
   * <pre>
   *  Γ |- φ, Δ    Σ, ψ |- Π
   * ------------------------
   *    Γ, Σ, φ→ψ |- Δ, Π
   * </pre>
   */
  case class LeftImplies(phi: Formula, psi: Formula) extends ProofStepWithoutBotNorPrem(2){
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.LeftImplies(bot, premises(0), premises(1), phi, psi)
  }

  /**
   * <pre>
   *  Γ, φ→ψ |- Δ               Γ, φ→ψ, ψ→φ |- Δ
   * --------------    or     --------------------
   *  Γ, φ↔ψ |- Δ                 Γ, φ↔ψ |- Δ
   * </pre>
   */
  case class LeftIff(phi: Formula, psi: Formula) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.LeftIff(bot, premises(0), phi, psi)
  }

  /**
   * <pre>
   *   Γ |- φ, Δ
   * --------------
   *   Γ, ¬φ |- Δ
   * </pre>
   */
  case class LeftNot(phi: Formula) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.LeftNot(bot, premises(0), phi)
  }

  /**
   * <pre>
   *   Γ, φ[t/x] |- Δ
   * -------------------
   *  Γ, ∀ φ |- Δ
   *
   * </pre>
   */
  case class LeftForall(phi: Formula, x: VariableLabel, t: Term) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.LeftForall(bot, premises(0), phi, x, t)
  }

  /**
   * <pre>
   *    Γ, φ |- Δ
   * ------------------- if x is not free in the resulting sequent
   *  Γ, ∃x φ|- Δ
   *
   * </pre>
   */
  case class LeftExists(phi: Formula, x: VariableLabel) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.LeftExists(bot, premises(0), phi, x)
  }

  /**
   * <pre>
   *  Γ, ∃y.∀x. (x=y) ↔ φ |-  Δ
   * ---------------------------- if y is not free in φ
   *      Γ, ∃!x. φ |- Δ
   * </pre>
   */
  case class LeftExistsOne( t1: Int, phi: Formula, x: VariableLabel) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.LeftExistsOne(bot, premises(0), phi, x)
  }


  // Right rules
  /**
   * <pre>
   *  Γ |- φ, Δ    Σ |- ψ, Π     ...
   * ------------------------------------
   *    Γ, Σ |- φ∧ψ∧..., Π, Δ
   * </pre>
   */
  case class RightAnd(t: Seq[Int], cunjuncts: Seq[Formula]) extends ProofStepWithoutBotNorPrem(-1) {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.RightAnd(bot, t, cunjuncts)
  }

  /**
   * <pre>
   *   Γ |- φ, Δ                Γ |- φ, ψ, Δ
   * --------------    or    ---------------
   *  Γ |- φ∨ψ, Δ              Γ |- φ∨ψ, Δ
   * </pre>
   */
  case class RightOr(phi: Formula, psi: Formula) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.RightOr(bot, premises(0), phi, psi)
  }

  /**
   * <pre>
   *  Γ, φ |- ψ, Δ
   * --------------
   *  Γ |- φ→ψ, Δ
   * </pre>
   */
  case class RightImplies(phi: Formula, psi: Formula) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.RightImplies(bot, premises(0), phi, psi)
  }

  /**
   * <pre>
   *  Γ |- a→ψ, Δ    Σ |- ψ→φ, Π
   * ----------------------------
   *      Γ, Σ |- φ↔ψ, Π, Δ
   * </pre>
   */
  case class RightIff(phi: Formula, psi: Formula) extends ProofStepWithoutBotNorPrem(2) {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.RightIff(bot, premises(0), premises(1), phi, psi)
  }

  /**
   * <pre>
   *  Γ, φ |- Δ
   * --------------
   *   Γ |- ¬φ, Δ
   * </pre>
   */
  case class RightNot(phi: Formula) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.RightNot(bot, premises(0), phi)
  }

  /**
   * <pre>
   *    Γ |- φ, Δ
   * ------------------- if x is not free in the resulting sequent
   *  Γ |- ∀x. φ, Δ
   * </pre>
   */
  case class RightForall(phi: Formula, x: VariableLabel) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.RightForall(bot, premises(0), phi, x)
  }

  /**
   * <pre>
   *   Γ |- φ[t/x], Δ
   * -------------------
   *  Γ |- ∃x. φ, Δ
   *
   * (ln-x stands for locally nameless x)
   * </pre>
   */
  case class RightExists(phi: Formula, x: VariableLabel, t: Term) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.RightExists(bot, premises(0), phi, x, t)
  }

  /**
   * <pre>
   *  Γ |- ∃y.∀x. (x=y) ↔ φ, Δ
   * ---------------------------- if y is not free in φ
   *      Γ|- ∃!x. φ,  Δ
   * </pre>
   */
  case class RightExistsOne(phi: Formula, x: VariableLabel) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.RightExistsOne(bot, premises(0), phi, x)
  }

  // Structural rules
  /**
   * <pre>
   *     Γ |- Δ
   * --------------
   *   Γ, Σ |- Δ, Π
   * </pre>
   */
  case class Weakening(t1: Int) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.Weakening(bot, t1)
  }

  // Equality Rules
  /**
   * <pre>
   *  Γ, s=s |- Δ
   * --------------
   *     Γ |- Δ
   * </pre>
   */
  case class LeftRefl(fa: Formula) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.LeftRefl(bot, premises(0), fa)
  }

  /**
   * <pre>
   *
   * --------------
   *     |- s=s
   * </pre>
   */
  case class RightRefl(fa: Formula) extends ProofStepWithoutBotNorPrem(0) {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.RightRefl(bot, fa)
  }

  /**
   * <pre>
   *    Γ, φ(s1,...,sn) |- Δ
   * ---------------------
   *  Γ, s1=premises(0), ..., sn=tn, φ(premises(0),...tn) |- Δ
   * </pre>
   */
  case class LeftSubstEq(equals: List[(Term, Term)], lambdaPhi: LambdaTermFormula) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.LeftSubstEq(bot, premises(0), equals, lambdaPhi)
  }

  /**
   * <pre>
   *    Γ |- φ(s1,...,sn), Δ
   * ---------------------
   *  Γ, s1=premises(0), ..., sn=tn |- φ(premises(0),...tn), Δ
   * </pre>
   */
  case class RightSubstEq(equals: List[(Term, Term)], lambdaPhi: LambdaTermFormula) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.RightSubstEq(bot, premises(0), equals, lambdaPhi)
  }

  /**
   * <pre>
   *    Γ, φ(a1,...an) |- Δ
   * ---------------------
   *  Γ, a1↔b1, ..., an↔bn, φ(b1,...bn) |- Δ
   * </pre>
   */
  case class LeftSubstIff(equals: List[(Formula, Formula)], lambdaPhi: LambdaFormulaFormula) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.LeftSubstIff(bot, premises(0), equals, lambdaPhi)
  }

  /**
   * <pre>
   *    Γ |- φ(a1,...an), Δ
   * ---------------------
   *  Γ, a1↔b1, ..., an↔bn |- φ(b1,...bn), Δ
   * </pre>
   */
  case class RightSubstIff(equals: List[(Formula, Formula)], lambdaPhi: LambdaFormulaFormula) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.RightSubstIff(bot, premises(0), equals, lambdaPhi)
  }

  /**
   * <pre>
   *           Γ |- Δ
   * --------------------------
   *  Γ[r(a)/?f] |- Δ[r(a)/?f]
   * </pre>
   */
  case class InstFunSchema(insts: Map[SchematicTermLabel, LambdaTermTerm]) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.InstFunSchema(bot, premises(0), insts)
  }

  /**
   * <pre>
   *           Γ |- Δ
   * --------------------------
   *  Γ[ψ(a)/?p] |- Δ[ψ(a)/?p]
   * </pre>
   */
  case class InstPredSchema(insts: Map[SchematicVarOrPredLabel, LambdaTermFormula]) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProofStep(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.InstPredSchema(bot, premises(0), insts)
  }

  // Proof Organisation rules
  case class SCSubproof(sp: WithProofs#Proof|SCProof,
                        premises: Seq[Int] = Seq.empty,
                        display: Boolean = true
                       )(using l:Library)(using String => Unit)(using finishOutput: Throwable => Nothing) extends ProofStep{
    this.validate(l)
    def asSCProofStep(currentProof: Library#Proof): ProofStepJudgement =
      sp match {
        case sp:WithProofs#Proof => SC.SCSubproof(sp.toSCProof, premises, display)
        case sp:SCProof => SC.SCSubproof(sp, premises, display)
      }
  }

}
