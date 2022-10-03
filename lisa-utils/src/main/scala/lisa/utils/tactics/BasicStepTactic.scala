package lisa.utils.tactics

import lisa.kernel.proof.SequentCalculus.{SCProofStep, Sequent}
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.{SCProof, SequentCalculus as SC}

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
    override val premises: Seq[Int] = t
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
  case class LeftImplies(t1: Int, t2: Int, phi: Formula, psi: Formula) extends ProofStepWithoutBot {
    override val premises: Seq[Int] = Seq(t1, t2)
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
      SC.LeftImplies(bot, t1, t2, phi, psi)
  }

  /**
   * <pre>
   *  Γ, φ→ψ |- Δ               Γ, φ→ψ, ψ→φ |- Δ
   * --------------    or     --------------------
   *  Γ, φ↔ψ |- Δ                 Γ, φ↔ψ |- Δ
   * </pre>
   */
  case class LeftIff(t1: Int, phi: Formula, psi: Formula) extends ProofStepWithoutBot {
    override val premises: Seq[Int] = Seq(t1)
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
      SC.LeftIff(bot, t1, phi, psi)
  }

  /**
   * <pre>
   *   Γ |- φ, Δ
   * --------------
   *   Γ, ¬φ |- Δ
   * </pre>
   */
  case class LeftNot(t1: Int, phi: Formula) extends ProofStepWithoutBot {
    override val premises: Seq[Int] = Seq(t1)
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
      SC.LeftNot(bot, t1, phi)
  }

  /**
   * <pre>
   *   Γ, φ[t/x] |- Δ
   * -------------------
   *  Γ, ∀ φ |- Δ
   *
   * </pre>
   */
  case class LeftForall(t1: Int, phi: Formula, x: VariableLabel, t: Term) extends ProofStepWithoutBot {
    override val premises: Seq[Int] = Seq(t1)
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
      SC.LeftForall(bot, t1, phi, x, t)
  }

  /**
   * <pre>
   *    Γ, φ |- Δ
   * ------------------- if x is not free in the resulting sequent
   *  Γ, ∃x φ|- Δ
   *
   * </pre>
   */
  case class LeftExists(t1: Int, phi: Formula, x: VariableLabel) extends ProofStepWithoutBot {
    override val premises: Seq[Int] = Seq(t1)
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
      SC.LeftExists(bot, t1, phi, x)
  }

  /**
   * <pre>
   *  Γ, ∃y.∀x. (x=y) ↔ φ |-  Δ
   * ---------------------------- if y is not free in φ
   *      Γ, ∃!x. φ |- Δ
   * </pre>
   */
  case class LeftExistsOne( t1: Int, phi: Formula, x: VariableLabel) extends ProofStepWithoutBot {
    override val premises: Seq[Int] = Seq(t1)
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
      SC.LeftExistsOne(bot, t1, phi, x)
  }


  // Right rules
  /**
   * <pre>
   *  Γ |- φ, Δ    Σ |- ψ, Π     ...
   * ------------------------------------
   *    Γ, Σ |- φ∧ψ∧..., Π, Δ
   * </pre>
   */
  case class RightAnd(t: Seq[Int], cunjuncts: Seq[Formula]) extends ProofStepWithoutBot {
    override val premises: Seq[Int] = t
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
      SC.RightAnd(bot, t, cunjuncts)
  }

  /**
   * <pre>
   *   Γ |- φ, Δ                Γ |- φ, ψ, Δ
   * --------------    or    ---------------
   *  Γ |- φ∨ψ, Δ              Γ |- φ∨ψ, Δ
   * </pre>
   */
  case class RightOr(t1: Int, phi: Formula, psi: Formula) extends ProofStepWithoutBot {
    override val premises: Seq[Int] = Seq(t1)
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
      SC.RightOr(bot, t1, phi, psi)
  }

  /**
   * <pre>
   *  Γ, φ |- ψ, Δ
   * --------------
   *  Γ |- φ→ψ, Δ
   * </pre>
   */
  case class RightImplies(t1: Int, phi: Formula, psi: Formula) extends ProofStepWithoutBot {
    override val premises: Seq[Int] = Seq(t1)
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
      SC.RightImplies(bot, t1, phi, psi)
  }

  /**
   * <pre>
   *  Γ |- a→ψ, Δ    Σ |- ψ→φ, Π
   * ----------------------------
   *      Γ, Σ |- φ↔ψ, Π, Δ
   * </pre>
   */
  case class RightIff(t1: Int, t2: Int, phi: Formula, psi: Formula) extends ProofStepWithoutBot {
    override val premises: Seq[Int] = Seq(t1, t2)
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
      SC.RightIff(bot, t1, t2, phi, psi)
  }

  /**
   * <pre>
   *  Γ, φ |- Δ
   * --------------
   *   Γ |- ¬φ, Δ
   * </pre>
   */
  case class RightNot(t1: Int, phi: Formula) extends ProofStepWithoutBot {
    override val premises: Seq[Int] = Seq(t1)
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
      SC.RightNot(bot, t1, phi)
  }

  /**
   * <pre>
   *    Γ |- φ, Δ
   * ------------------- if x is not free in the resulting sequent
   *  Γ |- ∀x. φ, Δ
   * </pre>
   */
  case class RightForall(t1: Int, phi: Formula, x: VariableLabel) extends ProofStepWithoutBot {
    override val premises: Seq[Int] = Seq(t1)
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
      SC.RightForall(bot, t1, phi, x)
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
  case class RightExists(t1: Int, phi: Formula, x: VariableLabel, t: Term) extends ProofStepWithoutBot {
    override val premises: Seq[Int] = Seq(t1)
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
      SC.RightExists(bot, t1, phi, x, t)
  }

  /**
   * <pre>
   *  Γ |- ∃y.∀x. (x=y) ↔ φ, Δ
   * ---------------------------- if y is not free in φ
   *      Γ|- ∃!x. φ,  Δ
   * </pre>
   */
  case class RightExistsOne(t1: Int, phi: Formula, x: VariableLabel) extends ProofStepWithoutBot {
    override val premises: Seq[Int] = Seq(t1)
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
      SC.RightExistsOne(bot, t1, phi, x)
  }

  // Structural rules
  /**
   * <pre>
   *     Γ |- Δ
   * --------------
   *   Γ, Σ |- Δ, Π
   * </pre>
   */
  case class Weakening(t1: Int) extends ProofStepWithoutBot {
    override val premises: Seq[Int] = Seq(t1)
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
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
  case class LeftRefl(t1: Int, fa: Formula) extends ProofStepWithoutBot {
    override val premises: Seq[Int] = Seq(t1)
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
      SC.LeftRefl(bot, t1, fa)
  }

  /**
   * <pre>
   *
   * --------------
   *     |- s=s
   * </pre>
   */
  case class RightRefl(fa: Formula) extends ProofStepWithoutBot {
    override val premises: Seq[Int] = Seq()
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
      SC.RightRefl(bot, fa)
  }

  /**
   * <pre>
   *    Γ, φ(s1,...,sn) |- Δ
   * ---------------------
   *  Γ, s1=t1, ..., sn=tn, φ(t1,...tn) |- Δ
   * </pre>
   */
  case class LeftSubstEq(t1: Int, equals: List[(Term, Term)], lambdaPhi: LambdaTermFormula) extends ProofStepWithoutBot {
    override val premises: Seq[Int] = Seq(t1)
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
      SC.LeftSubstEq(bot, t1, equals, lambdaPhi)
  }

  /**
   * <pre>
   *    Γ |- φ(s1,...,sn), Δ
   * ---------------------
   *  Γ, s1=t1, ..., sn=tn |- φ(t1,...tn), Δ
   * </pre>
   */
  case class RightSubstEq(t1: Int, equals: List[(Term, Term)], lambdaPhi: LambdaTermFormula) extends ProofStepWithoutBot {
    override val premises: Seq[Int] = Seq(t1)
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
      SC.RightSubstEq(bot, t1, equals, lambdaPhi)
  }

  /**
   * <pre>
   *    Γ, φ(a1,...an) |- Δ
   * ---------------------
   *  Γ, a1↔b1, ..., an↔bn, φ(b1,...bn) |- Δ
   * </pre>
   */
  case class LeftSubstIff(t1: Int, equals: List[(Formula, Formula)], lambdaPhi: LambdaFormulaFormula) extends ProofStepWithoutBot {
    override val premises: Seq[Int] = Seq(t1)
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
      SC.LeftSubstIff(bot, t1, equals, lambdaPhi)
  }

  /**
   * <pre>
   *    Γ |- φ(a1,...an), Δ
   * ---------------------
   *  Γ, a1↔b1, ..., an↔bn |- φ(b1,...bn), Δ
   * </pre>
   */
  case class RightSubstIff(t1: Int, equals: List[(Formula, Formula)], lambdaPhi: LambdaFormulaFormula) extends ProofStepWithoutBot {
    override val premises: Seq[Int] = Seq(t1)
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
      SC.RightSubstIff(bot, t1, equals, lambdaPhi)
  }

  /**
   * <pre>
   *           Γ |- Δ
   * --------------------------
   *  Γ[r(a)/?f] |- Δ[r(a)/?f]
   * </pre>
   */
  case class InstFunSchema(t1: Int, insts: Map[SchematicTermLabel, LambdaTermTerm]) extends ProofStepWithoutBot {
    override val premises: Seq[Int] = Seq(t1)
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
      SC.InstFunSchema(bot, t1, insts)
  }

  /**
   * <pre>
   *           Γ |- Δ
   * --------------------------
   *  Γ[ψ(a)/?p] |- Δ[ψ(a)/?p]
   * </pre>
   */
  case class InstPredSchema(bot: Sequent, t1: Int, insts: Map[SchematicPredicateLabel, LambdaTermFormula]) extends ProofStepWithoutBot {
    override val premises: Seq[Int] = Seq(t1)
    def asSCProofStep(bot: Sequent, references:Int => Sequent): SCProofStep =
      SC.InstPredSchema(bot, t1, insts)
  }

  // Proof Organisation rules
  case class SCSubproof(sp: Proof|SCProof, premises: Seq[Int] = Seq.empty, display: Boolean = true) extends ProofStep {
    // premises is a list of ints similar to t1, t2... that verifies that imports of the subproof sp are justified by previous steps.
    def asSCProofStep(references:Int => Sequent): SCProofStep =
      sp match {
        case sp:Proof => SC.SCSubproof(sp.toSCProof, premises, display)
        case sp:SCProof => SC.SCSubproof(sp, premises, display)
      }
  }

}
