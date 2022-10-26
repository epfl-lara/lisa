package lisa.utils.tactics

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.SCProofStep
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.kernel.proof.{SequentCalculus => SC}
import lisa.utils.Library
import lisa.utils.Helpers.*
import lisa.utils.tactics.ProofStepLib.{_, given}

object BasicStepTactic {

  case object Hypothesis extends ProofStepWithoutBotNorPrem(0) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.Hypothesis(bot, bot.left.intersect(bot.right).head)
  }

  case object Rewrite extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
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
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.Cut(bot, premises(0), premises(1), phi)
  }

  case object CutWithoutFormula extends ProofStepWithoutBotNorPrem(2) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      val leftSequent = currentProof.getSequent(premises(0))
      val rightSequent = currentProof.getSequent(premises(1))
      val cutSet = rightSequent.left.diff(bot.left) ++ leftSequent.right.diff(bot.right)
      lazy val intersectedCutSet = rightSequent.left & leftSequent.right

      if (!cutSet.isEmpty)
        if (cutSet.tail.isEmpty) {
          SC.Cut(bot, premises(0), premises(1), cutSet.head)
        } else
          ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Inferred cut pivot is not a singleton set.")
      else if (!intersectedCutSet.isEmpty && intersectedCutSet.tail.isEmpty)
        // can still find a pivot
        SC.Cut(bot, premises(0), premises(1), intersectedCutSet.head)
      else
        ProofStepJudgement.InvalidProofStep(
          this.asProofStepWithoutBot(premises).asProofStep(bot),
          "A consistent cut pivot cannot be inferred from the premises. Possibly a missing or extraneous clause."
        )
    }
  }

  case object Cut extends ProofStepWithoutBotNorPrem(2) {
    // default construction:
    // def apply(phi: Formula) = new Cut(phi)
    def apply() = CutWithoutFormula

    // usage without an argument list
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      this().asSCProof(bot, premises, currentProof)

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
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.LeftAnd(bot, premises(0), phi, psi)
  }

  case object LeftAndWithoutFormula extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      val premiseSequent = currentProof.getSequent(premises(0))
      val pivot = bot.left.diff(premiseSequent.left)

      if (!pivot.isEmpty && pivot.tail.isEmpty)
        pivot.head match {
          case ConnectorFormula(And, Seq(phi, psi)) =>
            if (premiseSequent.left.contains(phi))
              SC.LeftAnd(bot, premises(0), phi, psi)
            else
              SC.LeftAnd(bot, premises(0), psi, phi)
          case _ => ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Could not infer a conjunction as pivot from premise and conclusion.")
        }
      else
      // try a rewrite, if it works, go ahead with it, otherwise malformed
      if (SC.isSameSequent(premiseSequent, bot))
        SC.Rewrite(bot, premises(0))
      else
        ProofStepJudgement.InvalidProofStep(
          this.asProofStepWithoutBot(premises).asProofStep(bot),
          "Left-hand side of conclusion + φ∧ψ must be same as left-hand side of premise + either φ, ψ or both."
        )
    }
  }

  case object LeftAnd extends ProofStepWithoutBotNorPrem(1) {
    // default construction:
    // def apply(phi: Formula, psi: Formula) = new LeftAnd(phi, psi)
    def apply() = LeftAndWithoutFormula

    // usage without an argument list
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      this().asSCProof(bot, premises, currentProof)
  }

  /**
   * <pre>
   *  Γ, φ |- Δ    Σ, ψ |- Π    ...
   * --------------------------------
   *    Γ, Σ, φ∨ψ∨... |- Δ, Π
   * </pre>
   */
  case class LeftOr(disjuncts: Seq[Formula]) extends ProofStepWithoutBotNorPrem(-1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      SC.LeftOr(bot, premises, disjuncts)
    }
  }
  case class LeftOrWithoutFormula() extends ProofStepWithoutBotNorPrem(-1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      val premiseSequents = premises.map(currentProof.getSequent(_))
      val pivots = premiseSequents.map(_.left.diff(bot.left))

      if (pivots.exists(_.isEmpty))
        SC.Weakening(bot, premises(pivots.indexWhere(_.isEmpty)))
      else if (pivots.forall(_.tail.isEmpty))
        SC.LeftOr(bot, premises, pivots.map(_.head))
      else
        // some extraneous formulae
        ProofStepJudgement.InvalidProofStep(
          this.asProofStepWithoutBot(premises).asProofStep(bot),
          "Left-hand side of conclusion + disjuncts is not the same as the union of the left-hand sides of the premises + φ∨ψ."
        )
    }
  }

  case object LeftOr extends ProofStepWithoutBotNorPrem(-1) {
    // default construction:
    // def apply(disjuncts: Seq[Formula]) = new LeftOr(disjuncts)
    def apply() = new LeftOrWithoutFormula()

    // usage without an argument list
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      this().asSCProof(bot, premises, currentProof)
  }

  /**
   * <pre>
   *  Γ |- φ, Δ    Σ, ψ |- Π
   * ------------------------
   *    Γ, Σ, φ→ψ |- Δ, Π
   * </pre>
   */
  case class LeftImplies(phi: Formula, psi: Formula) extends ProofStepWithoutBotNorPrem(2) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.LeftImplies(bot, premises(0), premises(1), phi, psi)
  }

  case object LeftImpliesWithoutFormula extends ProofStepWithoutBotNorPrem(2) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      val leftSequent = currentProof.getSequent(premises(0))
      val rightSequent = currentProof.getSequent(premises(1))
      val pivotLeft = leftSequent.right.diff(bot.right)
      lazy val pivotRight = rightSequent.left.diff(bot.left)

      if (pivotLeft.isEmpty)
        SC.Weakening(bot, premises(0))
      else if (pivotRight.isEmpty)
        SC.Weakening(bot, premises(1))
      else if (pivotLeft.tail.isEmpty && pivotRight.tail.isEmpty)
        SC.LeftImplies(bot, premises(0), premises(1), pivotLeft.head, pivotRight.head)
      else
        ProofStepJudgement.InvalidProofStep(
          this.asProofStepWithoutBot(premises).asProofStep(bot),
          "Could not infer an implication as a pivot from the premises and conclusion, possible extraneous formulae in premises."
        )
    }
  }

  case object LeftImplies extends ProofStepWithoutBotNorPrem(2) {
    // default construction:
    // def apply(phi: Formula, psi: Formula) = new LeftImplies(phi, psi)
    def apply() = LeftImpliesWithoutFormula

    // usage without an argument list
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      this().asSCProof(bot, premises, currentProof)
  }

  /**
   * <pre>
   *  Γ, φ→ψ |- Δ               Γ, φ→ψ, ψ→φ |- Δ
   * --------------    or     --------------------
   *  Γ, φ↔ψ |- Δ                 Γ, φ↔ψ |- Δ
   * </pre>
   */
  case class LeftIff(phi: Formula, psi: Formula) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.LeftIff(bot, premises(0), phi, psi)
  }

  case class LeftIffWithoutFormula() extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      val premiseSequent = currentProof.getSequent(premises(0))
      val pivot = premiseSequent.left.diff(bot.left)

      if (pivot.isEmpty)
        SC.Weakening(bot, premises(0))
      else
        pivot.head match {
          case ConnectorFormula(Implies, Seq(phi, psi)) => SC.LeftIff(bot, premises(0), phi, psi)
          case _ => ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Could not infer a pivot implication from premise.")
        }
    }
  }

  case object LeftIff extends ProofStepWithoutBotNorPrem(1) {
    // default construction:
    // def apply(phi: Formula, psi: Formula) = new LeftIff(phi, psi)
    def apply() = new LeftIffWithoutFormula()

    // usage without an argument list
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      this().asSCProof(bot, premises, currentProof)
  }

  /**
   * <pre>
   *   Γ |- φ, Δ
   * --------------
   *   Γ, ¬φ |- Δ
   * </pre>
   */
  case class LeftNot(phi: Formula) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.LeftNot(bot, premises(0), phi)
  }

  case class LeftNotWithoutFormula() extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      val premiseSequent = currentProof.getSequent(premises(0))
      val pivot = premiseSequent.right.diff(bot.right)

      if (pivot.isEmpty)
        SC.Weakening(bot, premises(0))
      else if (pivot.tail.isEmpty)
        SC.LeftNot(bot, premises(0), pivot.head)
      else
        ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Right-hand side of conclusion + φ must be the same as right-hand side of premise.")

    }
  }

  case object LeftNot extends ProofStepWithoutBotNorPrem(1) {
    // default construction:
    // def apply(phi: Formula) = new LeftNot(phi)
    def apply() = new LeftNotWithoutFormula()

    // usage without an argument list
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      this().asSCProof(bot, premises, currentProof)
  }

  /**
   * <pre>
   *   Γ, φ[t/x] |- Δ
   * -------------------
   *   Γ, ∀x. φ |- Δ
   *
   * </pre>
   */
  case class LeftForall(phi: Formula, x: VariableLabel, t: Term) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.LeftForall(bot, premises(0), phi, x, t)
  }

  case class LeftForallWithoutFormula(t: Term) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      val premiseSequent = currentProof.getSequent(premises(0))
      val pivot = bot.left.diff(premiseSequent.left)
      lazy val instantiatedPivot = premiseSequent.left.diff(bot.left)

      if (!pivot.isEmpty)
        if (pivot.tail.isEmpty)
          pivot.head match {
            case BinderFormula(Forall, x, phi) => SC.LeftForall(bot, premises(0), phi, x, t)
            case _ => ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Could not infer a universally quantified pivot from premise and conclusion.")
          }
        else
          ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Left-hand side of conclusion + φ[t/x] must be the same as left-hand side of premise + ∀x. φ.")
      else if (instantiatedPivot.isEmpty) SC.Weakening(bot, premises(0))
      else if (instantiatedPivot.tail.isEmpty) {
        // go through conclusion to find a matching quantified formula

        val in: Formula = instantiatedPivot.head
        val quantifiedPhi: Option[Formula] = bot.left.find(f =>
          f match {
            case g @ BinderFormula(Forall, _, _) => isSame(instantiateBinder(g, t), in)
            case _ => false
          }
        )

        quantifiedPhi match {
          case Some(BinderFormula(Forall, x, phi)) => SC.LeftForall(bot, premises(0), phi, x, t)
          case _ => ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Could not infer a universally quantified pivot from premise and conclusion.")
        }
      } else ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Left-hand side of conclusion + φ[t/x] must be the same as left-hand side of premise + ∀x. φ.")
    }
  }

  case object LeftForall {
    // default construction:
    // def apply(phi: Formula, x: VariableLabel, t: Term) = new LeftForall(phi, x, t)
    def apply(t: Term) = new LeftForallWithoutFormula(t)

    // TODO: will require unification to infer input Term:
    // def apply() = new LeftForallWithoutFormulaOrTerm()

    // usage without an argument list
    // TODO: add `extends ProofStepWithoutBotNorPrem(1)` to object when uncommenting
    // def asSCProof(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
    //   this().asSCProof(bot, premises, currentProof)
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
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.LeftExists(bot, premises(0), phi, x)
  }

  case class LeftExistsWithoutFormula() extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      val premiseSequent = currentProof.getSequent(premises(0))
      val pivot = bot.left.diff(premiseSequent.left)
      lazy val instantiatedPivot = premiseSequent.left.diff(bot.left)

      if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty) SC.Rewrite(bot, premises(0))
        else if (instantiatedPivot.tail.isEmpty) {
          val in: Formula = instantiatedPivot.head
          val quantifiedPhi: Option[Formula] = bot.left.find(f =>
            f match {
              case BinderFormula(Exists, _, g) => isSame(g, in)
              case _ => false
            }
          )

          quantifiedPhi match {
            case Some(BinderFormula(Exists, x, phi)) => SC.LeftExists(bot, premises(0), phi, x)
            case _ => ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Could not infer an existensially quantified pivot from premise and conclusion.")
          }
        } else ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Left-hand side of conclusion + φ must be the same as left-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case BinderFormula(Exists, x, phi) => SC.LeftExists(bot, premises(0), phi, x)
          case _ => ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Could not infer an existentially quantified pivot from premise and conclusion.")
        }
      else
        ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Left-hand side of conclusion + φ must be the same as left-hand side of premise + ∃x. φ.")
    }
  }

  case object LeftExists extends ProofStepWithoutBotNorPrem(1) {
    // default construction:
    // def apply(phi: Formula, x: VariableLabel) = new LeftExists(phi, x)
    def apply() = new LeftExistsWithoutFormula()

    // usage without an argument list
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      this().asSCProof(bot, premises, currentProof)
  }

  /**
   * <pre>
   *  Γ, ∃y.∀x. (x=y) ↔ φ |-  Δ
   * ---------------------------- if y is not free in φ
   *      Γ, ∃!x. φ |- Δ
   * </pre>
   */
  case class LeftExistsOne(phi: Formula, x: VariableLabel) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.LeftExistsOne(bot, premises(0), phi, x)
  }

  case class LeftExistsOneWithoutFormula() extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      val premiseSequent = currentProof.getSequent(premises(0))
      val pivot = bot.left.diff(premiseSequent.left)
      lazy val instantiatedPivot = premiseSequent.left.diff(bot.left)

      if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty)
          SC.Rewrite(bot, premises(0))
        else if (instantiatedPivot.tail.isEmpty) {
          instantiatedPivot.head match {
            // ∃_. ∀x. _ ↔ φ == extract ==> x, phi
            case BinderFormula(Exists, _, BinderFormula(Forall, x, ConnectorFormula(Iff, Seq(_, phi)))) => SC.LeftExistsOne(bot, premises(0), phi, x)
            case _ => ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Could not infer an existentially quantified pivot from premise and conclusion.")
          }
        } else
          ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Left-hand side of conclusion + φ must be the same as left-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case BinderFormula(ExistsOne, x, phi) => SC.LeftExistsOne(bot, premises(0), phi, x)
          case _ => ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Could not infer an existentially quantified pivot from premise and conclusion.")
        }
      else
        ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Left-hand side of conclusion + φ must be the same as left-hand side of premise + ∃x. φ.")
    }
  }

  case object LeftExistsOne extends ProofStepWithoutBotNorPrem(1) {
    // default construction:
    // def apply(phi: Formula, x: VariableLabel) = new LeftExistsOne(phi, x)
    def apply() = new LeftExistsOneWithoutFormula()

    // usage without an argument list
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      this().asSCProof(bot, premises, currentProof)
  }

  // Right rules
  /**
   * <pre>
   *  Γ |- φ, Δ    Σ |- ψ, Π     ...
   * ------------------------------------
   *    Γ, Σ |- φ∧ψ∧..., Π, Δ
   * </pre>
   */
  case class RightAnd(cunjuncts: Seq[Formula]) extends ProofStepWithoutBotNorPrem(-1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.RightAnd(bot, premises, cunjuncts)
  }
  case object RightAndWithoutFormula extends ProofStepWithoutBotNorPrem(-1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      val premiseSequents = premises.map(currentProof.getSequent(_))
      val pivots = premiseSequents.map(_.right.diff(bot.right))

      if (pivots.exists(_.isEmpty))
        SC.Weakening(bot, premises(pivots.indexWhere(_.isEmpty)))
      else if (pivots.forall(_.tail.isEmpty))
        SC.RightAnd(bot, premises, pivots.map(_.head))
      else
        // some extraneous formulae
        ProofStepJudgement.InvalidProofStep(
          this.asProofStepWithoutBot(premises).asProofStep(bot),
          "Right-hand side of conclusion + φ + ψ is not the same as the union of the right-hand sides of the premises +φ∧ψ."
        )
    }
  }

  case object RightAnd extends ProofStepWithoutBotNorPrem(-1) {
    // default construction:
    // def apply(conjuncts: Seq[Formula]) = new RightAnd(conjuncts)
    def apply() = RightAndWithoutFormula

    // usage without an argument list
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      this().asSCProof(bot, premises, currentProof)
  }

  /**
   * <pre>
   *   Γ |- φ, Δ               Γ |- φ, ψ, Δ
   * --------------    or    ---------------
   *  Γ |- φ∨ψ, Δ              Γ |- φ∨ψ, Δ
   * </pre>
   */
  case class RightOr(phi: Formula, psi: Formula) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.RightOr(bot, premises(0), phi, psi)
  }

  case class RightOrWithoutFormula() extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      val premiseSequent = currentProof.getSequent(premises(0))
      val pivot = bot.right.diff(premiseSequent.right)

      if (!pivot.isEmpty && pivot.tail.isEmpty)
        pivot.head match {
          case ConnectorFormula(Or, Seq(phi, psi)) =>
            if (premiseSequent.left.contains(phi))
              SC.RightOr(bot, premises(0), phi, psi)
            else
              SC.RightOr(bot, premises(0), psi, phi)
          case _ => ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Could not infer a disjunction as pivot from premise and conclusion.")
        }
      else
      // try a rewrite, if it works, go ahead with it, otherwise malformed
      if (SC.isSameSequent(premiseSequent, bot))
        SC.Rewrite(bot, premises(0))
      else
        ProofStepJudgement.InvalidProofStep(
          this.asProofStepWithoutBot(premises).asProofStep(bot),
          "Right-hand side of conclusion + φ∧ψ must be same as right-hand side of premise + either φ, ψ or both."
        )
    }
  }

  case object RightOr extends ProofStepWithoutBotNorPrem(1) {
    // default construction:
    // def apply(phi: Formula, psi: Formula) = new RightOr(phi, psi)
    def apply() = new RightOrWithoutFormula()

    // usage without an argument list
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      this().asSCProof(bot, premises, currentProof)
  }

  /**
   * <pre>
   *  Γ, φ |- ψ, Δ
   * --------------
   *  Γ |- φ→ψ, Δ
   * </pre>
   */
  case class RightImplies(phi: Formula, psi: Formula) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.RightImplies(bot, premises(0), phi, psi)
  }

  case class RightImpliesWithoutFormula() extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      val premiseSequent = currentProof.getSequent(premises(0))
      val leftPivot = premiseSequent.left.diff(bot.left)
      val rightPivot = premiseSequent.right.diff(bot.right)

      if (
        !leftPivot.isEmpty && leftPivot.tail.isEmpty &&
        !rightPivot.isEmpty && rightPivot.tail.isEmpty
      )
        SC.RightImplies(bot, premises(0), leftPivot.head, rightPivot.head)
      else
        ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Right-hand side of conclusion + ψ must be same as right-hand side of premise + φ→ψ.")
    }
  }

  case object RightImplies extends ProofStepWithoutBotNorPrem(1) {
    // default construction:
    // def apply(phi: Formula, psi: Formula) = new RightImplies(phi, psi)
    def apply() = new RightImpliesWithoutFormula()

    // usage without an argument list
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      this().asSCProof(bot, premises, currentProof)
  }

  /**
   * <pre>
   *  Γ |- φ→ψ, Δ    Σ |- ψ→φ, Π
   * ----------------------------
   *      Γ, Σ |- φ↔ψ, Π, Δ
   * </pre>
   */
  case class RightIff(phi: Formula, psi: Formula) extends ProofStepWithoutBotNorPrem(2) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.RightIff(bot, premises(0), premises(1), phi, psi)
  }

  case class RightIffWithoutFormula() extends ProofStepWithoutBotNorPrem(2) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      val premiseSequent = currentProof.getSequent(premises(0))
      val pivot = premiseSequent.right.diff(bot.right)

      if (pivot.isEmpty)
        SC.Weakening(bot, premises(0))
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case ConnectorFormula(Implies, Seq(phi, psi)) => SC.RightIff(bot, premises(0), premises(1), phi, psi)
          case _ => ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Could not infer an implication as pivot from premise and conclusion.")
        }
      else
        ProofStepJudgement.InvalidProofStep(
          this.asProofStepWithoutBot(premises).asProofStep(bot),
          "Right-hand side of conclusion + φ→ψ + ψ→φ is not the same as the union of the right-hand sides of the premises φ↔ψ."
        )
    }
  }

  case object RightIff extends ProofStepWithoutBotNorPrem(2) {
    // default construction:
    // def apply(phi: Formula, psi: Formula) = new RightIff(phi, psi)
    def apply() = new RightIffWithoutFormula()

    // usage without an argument list
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      this().asSCProof(bot, premises, currentProof)
  }

  /**
   * <pre>
   *  Γ, φ |- Δ
   * --------------
   *   Γ |- ¬φ, Δ
   * </pre>
   */
  case class RightNot(phi: Formula) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.RightNot(bot, premises(0), phi)
  }

  case class RightNotWithoutFormula() extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      val premiseSequent = currentProof.getSequent(premises(0))
      val pivot = premiseSequent.left.diff(bot.left)

      if (pivot.isEmpty)
        SC.Weakening(bot, premises(0))
      else if (pivot.tail.isEmpty)
        SC.RightNot(bot, premises(0), pivot.head)
      else
        ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Left-hand side of conclusion + φ must be the same as left-hand side of premise.")

    }
  }

  case object RightNot extends ProofStepWithoutBotNorPrem(1) {
    // default construction:
    // def apply(phi: Formula) = new RightNot(phi)
    def apply() = new RightNotWithoutFormula()

    // usage without an argument list
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      this().asSCProof(bot, premises, currentProof)
  }

  /**
   * <pre>
   *    Γ |- φ, Δ
   * ------------------- if x is not free in the resulting sequent
   *  Γ |- ∀x. φ, Δ
   * </pre>
   */
  case class RightForall(phi: Formula, x: VariableLabel) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.RightForall(bot, premises(0), phi, x)
  }

  case class RightForallWithoutFormula() extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      val premiseSequent = currentProof.getSequent(premises(0))
      val pivot = bot.right.diff(premiseSequent.right)
      lazy val instantiatedPivot = premiseSequent.right.diff(bot.right)

      if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty) SC.Rewrite(bot, premises(0))
        else if (instantiatedPivot.tail.isEmpty) {
          val in: Formula = instantiatedPivot.head
          val quantifiedPhi: Option[Formula] = bot.right.find(f =>
            f match {
              case BinderFormula(Forall, _, g) => isSame(g, in)
              case _ => false
            }
          )

          quantifiedPhi match {
            case Some(BinderFormula(Forall, x, phi)) => SC.RightForall(bot, premises(0), phi, x)
            case _ => ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Could not infer a universally quantified pivot from premise and conclusion.")
          }
        } else ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Right-hand side of conclusion + φ must be the same as right-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case BinderFormula(Forall, x, phi) => SC.RightForall(bot, premises(0), phi, x)
          case _ => ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Could not infer a universally quantified pivot from premise and conclusion.")
        }
      else
        ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Right-hand side of conclusion + φ must be the same as right-hand side of premise + ∃x. φ.")
    }
  }

  case object RightForall extends ProofStepWithoutBotNorPrem(1) {
    // default construction:
    // def apply(phi: Formula, x: VariableLabel) = new RightForall(phi, x)
    def apply() = new RightForallWithoutFormula()

    // usage without an argument list
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      this().asSCProof(bot, premises, currentProof)
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
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.RightExists(bot, premises(0), phi, x, t)
  }

  case class RightExistsWithoutFormula(t: Term) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      val premiseSequent = currentProof.getSequent(premises(0))
      val pivot = bot.right.diff(premiseSequent.right)
      lazy val instantiatedPivot = premiseSequent.right.diff(bot.right)

      if (!pivot.isEmpty)
        if (pivot.tail.isEmpty)
          pivot.head match {
            case BinderFormula(Exists, x, phi) => SC.RightExists(bot, premises(0), phi, x, t)
            case _ => ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Could not infer an existentially quantified pivot from premise and conclusion.")
          }
        else
          ProofStepJudgement.InvalidProofStep(
            this.asProofStepWithoutBot(premises).asProofStep(bot),
            "Right-hand side of conclusion + φ[t/x] must be the same as right-hand side of premise + ∀x. φ."
          )
      else if (instantiatedPivot.isEmpty) SC.Weakening(bot, premises(0))
      else if (instantiatedPivot.tail.isEmpty) {
        // go through conclusion to find a matching quantified formula

        val in: Formula = instantiatedPivot.head
        val quantifiedPhi: Option[Formula] = bot.right.find(f =>
          f match {
            case g @ BinderFormula(Exists, _, _) => isSame(instantiateBinder(g, t), in)
            case _ => false
          }
        )

        quantifiedPhi match {
          case Some(BinderFormula(Exists, x, phi)) => SC.RightExists(bot, premises(0), phi, x, t)
          case _ => ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Could not infer an existentially quantified pivot from premise and conclusion.")
        }
      } else
        ProofStepJudgement.InvalidProofStep(
          this.asProofStepWithoutBot(premises).asProofStep(bot),
          "Right-hand side of conclusion + φ[t/x] must be the same as right-hand side of premise + ∀x. φ."
        )
    }
  }

  case object RightExists {
    // default construction:
    // def apply(phi: Formula, x: VariableLabel, t: Term) = new RightExists(phi, x, t)
    def apply(t: Term) = new RightExistsWithoutFormula(t)

    // TODO: will require unification to infer input Term:
    // def apply() = new RightExistsWithoutFormulaOrTerm()

    // usage without an argument list
    // TODO: add `extends ProofStepWithoutBotNorPrem(1)` to object when uncommenting
    // def asSCProof(bot: Sequent, premises:Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
    //   this().asSCProof(bot, premises, currentProof)
  }

  /**
   * <pre>
   *  Γ |- ∃y.∀x. (x=y) ↔ φ, Δ
   * ---------------------------- if y is not free in φ
   *      Γ|- ∃!x. φ,  Δ
   * </pre>
   */
  case class RightExistsOne(phi: Formula, x: VariableLabel) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.RightExistsOne(bot, premises(0), phi, x)
  }

  case class RightExistsOneWithoutFormula() extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      val premiseSequent = currentProof.getSequent(premises(0))
      val pivot = bot.right.diff(premiseSequent.right)
      lazy val instantiatedPivot = premiseSequent.right.diff(bot.right)

      if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty)
          SC.Rewrite(bot, premises(0))
        else if (instantiatedPivot.tail.isEmpty) {
          instantiatedPivot.head match {
            // ∃_. ∀x. _ ↔ φ == extract ==> x, phi
            case BinderFormula(Exists, _, BinderFormula(Forall, x, ConnectorFormula(Iff, Seq(_, phi)))) => SC.RightExistsOne(bot, premises(0), phi, x)
            case _ => ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Could not infer an existentially quantified pivot from premise and conclusion.")
          }
        } else
          ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Right-hand side of conclusion + φ must be the same as right-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case BinderFormula(ExistsOne, x, phi) => SC.RightExistsOne(bot, premises(0), phi, x)
          case _ => ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Could not infer an existentially quantified pivot from premise and conclusion.")
        }
      else
        ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Right-hand side of conclusion + φ must be the same as right-hand side of premise + ∃x. φ.")
    }
  }

  case object RightExistsOne extends ProofStepWithoutBotNorPrem(1) {
    // default construction:
    // def apply(phi: Formula, x: VariableLabel) = new RightExistsOne(phi, x)
    def apply() = new RightExistsOneWithoutFormula()

    // usage without an argument list
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      this().asSCProof(bot, premises, currentProof)
  }

  // Structural rules
  /**
   * <pre>
   *     Γ |- Δ
   * --------------
   *   Γ, Σ |- Δ, Π
   * </pre>
   */
  case object Weakening extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.Weakening(bot, premises(0))
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
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.LeftRefl(bot, premises(0), fa)
  }

  case class LeftReflWithoutFormula() extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.Rewrite(bot, premises(0))
  }

  case object LeftRefl extends ProofStepWithoutBotNorPrem(1) {
    // default construction:
    // def apply(fa: Formula) = new LeftRefl(fa)
    def apply() = new LeftReflWithoutFormula()

    // usage without an argument list
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      this().asSCProof(bot, premises, currentProof)
  }

  /**
   * <pre>
   *
   * --------------
   *     |- s=s
   * </pre>
   */
  case class RightRefl(fa: Formula) extends ProofStepWithoutBotNorPrem(0) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.RightRefl(bot, fa)
  }

  case class RightReflWithoutFormula() extends ProofStepWithoutBotNorPrem(0) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.RewriteTrue(bot)
  }

  case object RightRefl extends ProofStepWithoutBotNorPrem(0) {
    // default construction:
    // def apply(fa: Formula) = new RightRefl(fa)
    def apply() = new RightReflWithoutFormula()

    // usage without an argument list
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      this().asSCProof(bot, premises, currentProof)
  }

  /**
   * <pre>
   *    Γ, φ(s1,...,sn) |- Δ
   * ---------------------
   *  Γ, s1=premises(0), ..., sn=tn, φ(premises(0),...tn) |- Δ
   * </pre>
   */
  case class LeftSubstEq(equals: List[(Term, Term)], lambdaPhi: LambdaTermFormula) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
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
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
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
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
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
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
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
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
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
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.InstPredSchema(bot, premises(0), insts)
  }

  // Proof Organisation rules
  case class SCSubproof(sp: SCProof, premises: Seq[Int] = Seq.empty, display: Boolean = true) extends ProofStep {
    def asSCProof(currentProof: Library#Proof): ProofStepJudgement =
      sp match {
        case sp: SCProof => SC.SCSubproof(sp, premises, display)
      }
  }

}
