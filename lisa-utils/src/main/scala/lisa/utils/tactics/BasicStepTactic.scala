package lisa.utils.tactics

import lisa.kernel.proof.SequentCalculus.{SCProofStep, Sequent}
import lisa.kernel.proof.SequentCalculus as SC

object BasicStepTactic {

  case class Hypothesis() extends ProofStepWithoutBot {
    override val premises: Seq[Int] = Seq()
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
      SC.Hypothesis(bot, bot.left.intersect(bot.right).head)
  }

  case class Rewrite(t1: Int) extends ProofStepWithoutBot {
    override val premises: Seq[Int] = Seq(t1)
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
      SC.Rewrite(bot, t1)
  }

  case class Cut(t1: Int, t2: Int, phi: Formula) extends ProofStepWithoutBot {
    override val premises: Seq[Int] = Seq(t1)
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
      SC.Cut(bot, t1, t2, phi)
  }

  // Left rules
  /**
   * <pre>
   *   Γ, φ |- Δ                Γ, φ, ψ |- Δ
   * --------------     or     --------------
   *  Γ, φ∧ψ |- Δ               Γ, φ∧ψ |- Δ
   * </pre>
   */
  case class LeftAnd(t1: Int, phi: Formula, psi: Formula) extends ProofStepWithoutBot {
    override val premises: Seq[Int] = Seq(t1)
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
      SC.LeftAnd(bot, t1, phi, psi)
  }

  /**
   * <pre>
   *  Γ, φ |- Δ    Σ, ψ |- Π    ...
   * --------------------------------
   *    Γ, Σ, φ∨ψ∨... |- Δ, Π
   * </pre>
   */
  case class LeftOr(t: Seq[Int], disjuncts: Seq[Formula]) extends ProofStepWithoutBot {
    override val premises: Seq[Int] = Seq(t1)
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
      SC.LeftOr(bot, t, disjuncts)
  }

  /**
   * <pre>
   *  Γ |- φ, Δ    Σ, ψ |- Π
   * ------------------------
   *    Γ, Σ, φ→ψ |- Δ, Π
   * </pre>
   */
  case class LeftImplies(bot: Sequent, t1: Int, t2: Int, phi: Formula, psi: Formula) extends SCProofStep { val premises = Seq(t1, t2) }

  /**
   * <pre>
   *  Γ, φ→ψ |- Δ               Γ, φ→ψ, ψ→φ |- Δ
   * --------------    or     --------------------
   *  Γ, φ↔ψ |- Δ                 Γ, φ↔ψ |- Δ
   * </pre>
   */
  case class LeftIff(bot: Sequent, t1: Int, phi: Formula, psi: Formula) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *   Γ |- φ, Δ
   * --------------
   *   Γ, ¬φ |- Δ
   * </pre>
   */
  case class LeftNot(bot: Sequent, t1: Int, phi: Formula) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *   Γ, φ[t/x] |- Δ
   * -------------------
   *  Γ, ∀ φ |- Δ
   *
   * </pre>
   */
  case class LeftForall(bot: Sequent, t1: Int, phi: Formula, x: VariableLabel, t: Term) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *    Γ, φ |- Δ
   * ------------------- if x is not free in the resulting sequent
   *  Γ, ∃x φ|- Δ
   *
   * </pre>
   */
  case class LeftExists(bot: Sequent, t1: Int, phi: Formula, x: VariableLabel) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *  Γ, ∃y.∀x. (x=y) ↔ φ |-  Δ
   * ---------------------------- if y is not free in φ
   *      Γ, ∃!x. φ |- Δ
   * </pre>
   */
  case class LeftExistsOne(bot: Sequent, t1: Int, phi: Formula, x: VariableLabel) extends SCProofStep { val premises = Seq(t1) }

  // Right rules
  /**
   * <pre>
   *  Γ |- φ, Δ    Σ |- ψ, Π     ...
   * ------------------------------------
   *    Γ, Σ |- φ∧ψ∧..., Π, Δ
   * </pre>
   */
  case class RightAnd(bot: Sequent, t: Seq[Int], cunjuncts: Seq[Formula]) extends SCProofStep { val premises = t }

  /**
   * <pre>
   *   Γ |- φ, Δ                Γ |- φ, ψ, Δ
   * --------------    or    ---------------
   *  Γ |- φ∨ψ, Δ              Γ |- φ∨ψ, Δ
   * </pre>
   */
  case class RightOr(bot: Sequent, t1: Int, phi: Formula, psi: Formula) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *  Γ, φ |- ψ, Δ
   * --------------
   *  Γ |- φ→ψ, Δ
   * </pre>
   */
  case class RightImplies(bot: Sequent, t1: Int, phi: Formula, psi: Formula) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *  Γ |- a→ψ, Δ    Σ |- ψ→φ, Π
   * ----------------------------
   *      Γ, Σ |- φ↔ψ, Π, Δ
   * </pre>
   */
  case class RightIff(bot: Sequent, t1: Int, t2: Int, phi: Formula, psi: Formula) extends SCProofStep { val premises = Seq(t1, t2) }

  /**
   * <pre>
   *  Γ, φ |- Δ
   * --------------
   *   Γ |- ¬φ, Δ
   * </pre>
   */
  case class RightNot(bot: Sequent, t1: Int, phi: Formula) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *    Γ |- φ, Δ
   * ------------------- if x is not free in the resulting sequent
   *  Γ |- ∀x. φ, Δ
   * </pre>
   */
  case class RightForall(bot: Sequent, t1: Int, phi: Formula, x: VariableLabel) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *   Γ |- φ[t/x], Δ
   * -------------------
   *  Γ |- ∃x. φ, Δ
   *
   * (ln-x stands for locally nameless x)
   * </pre>
   */
  case class RightExists(bot: Sequent, t1: Int, phi: Formula, x: VariableLabel, t: Term) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *  Γ |- ∃y.∀x. (x=y) ↔ φ, Δ
   * ---------------------------- if y is not free in φ
   *      Γ|- ∃!x. φ,  Δ
   * </pre>
   */
  case class RightExistsOne(bot: Sequent, t1: Int, phi: Formula, x: VariableLabel) extends SCProofStep { val premises = Seq(t1) }

  // Structural rules
  /**
   * <pre>
   *     Γ |- Δ
   * --------------
   *   Γ, Σ |- Δ, Π
   * </pre>
   */
  case class Weakening(bot: Sequent, t1: Int) extends SCProofStep { val premises = Seq(t1) }

  // Equality Rules
  /**
   * <pre>
   *  Γ, s=s |- Δ
   * --------------
   *     Γ |- Δ
   * </pre>
   */
  case class LeftRefl(bot: Sequent, t1: Int, fa: Formula) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *
   * --------------
   *     |- s=s
   * </pre>
   */
  case class RightRefl(bot: Sequent, fa: Formula) extends SCProofStep { val premises = Seq() }

  /**
   * <pre>
   *    Γ, φ(s1,...,sn) |- Δ
   * ---------------------
   *  Γ, s1=t1, ..., sn=tn, φ(t1,...tn) |- Δ
   * </pre>
   */
  case class LeftSubstEq(bot: Sequent, t1: Int, equals: List[(Term, Term)], lambdaPhi: LambdaTermFormula) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *    Γ |- φ(s1,...,sn), Δ
   * ---------------------
   *  Γ, s1=t1, ..., sn=tn |- φ(t1,...tn), Δ
   * </pre>
   */
  case class RightSubstEq(bot: Sequent, t1: Int, equals: List[(Term, Term)], lambdaPhi: LambdaTermFormula) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *    Γ, φ(a1,...an) |- Δ
   * ---------------------
   *  Γ, a1↔b1, ..., an↔bn, φ(b1,...bn) |- Δ
   * </pre>
   */
  case class LeftSubstIff(bot: Sequent, t1: Int, equals: List[(Formula, Formula)], lambdaPhi: LambdaFormulaFormula) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *    Γ |- φ(a1,...an), Δ
   * ---------------------
   *  Γ, a1↔b1, ..., an↔bn |- φ(b1,...bn), Δ
   * </pre>
   */
  case class RightSubstIff(bot: Sequent, t1: Int, equals: List[(Formula, Formula)], lambdaPhi: LambdaFormulaFormula) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *           Γ |- Δ
   * --------------------------
   *  Γ[r(a)/?f] |- Δ[r(a)/?f]
   * </pre>
   */
  case class InstFunSchema(bot: Sequent, t1: Int, insts: Map[SchematicTermLabel, LambdaTermTerm]) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *           Γ |- Δ
   * --------------------------
   *  Γ[ψ(a)/?p] |- Δ[ψ(a)/?p]
   * </pre>
   */
  case class InstPredSchema(bot: Sequent, t1: Int, insts: Map[SchematicPredicateLabel, LambdaTermFormula]) extends SCProofStep { val premises = Seq(t1) }

  // Proof Organisation rules
  case class SCSubproof(sp: SCProof, premises: Seq[Int] = Seq.empty, display: Boolean = true) extends SCProofStep {
    // premises is a list of ints similar to t1, t2... that verifies that imports of the subproof sp are justified by previous steps.
    val bot: Sequent = sp.conclusion
  }

}
