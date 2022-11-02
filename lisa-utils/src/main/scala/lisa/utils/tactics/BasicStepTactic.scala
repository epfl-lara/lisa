package lisa.utils.tactics

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.SCProofStep
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.kernel.proof.{SequentCalculus => SC}
import lisa.utils.Helpers.*
import lisa.utils.Library
import lisa.utils.tactics.ProofStepLib.{_, given}

object BasicStepTactic {

  case object Hypothesis extends ProofStepWithoutBotNorPrem(0) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val intersectedPivot = bot.left.intersect(bot.right)

      if (premises.length != 0)
        invalid(s"No premises expected, ${premises.length} received.")
      else if (intersectedPivot.isEmpty)
        invalid("A formula for input to hypothesis could not be inferred from left and right side of sequent.")
      else
        SC.Hypothesis(bot, intersectedPivot.head)
    }
  }

  case object Rewrite extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (!SC.isSameSequent(bot, currentProof.getSequent(premises(0))))
        invalid("The premise and the conclusion are not trivially equivalent.")
      else
        SC.Rewrite(bot, premises(0))
    }
  }

  /**
   * <pre>
   *  Γ |- Δ, φ    φ, Σ |- Π
   * ------------------------
   *       Γ, Σ |-Δ, Π
   * </pre>
   */
  case class Cut(phi: Formula) extends ProofStepWithoutBotNorPrem(2) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val leftSequent = currentProof.getSequent(premises(0))
      lazy val rightSequent = currentProof.getSequent(premises(1))

      if (premises.length != 2)
        invalid(s"Two premises expected, ${premises.length} received.")
      else if (!contains(leftSequent.right, phi))
        invalid("Right-hand side of first premise does not contain φ as claimed.")
      else if (!contains(rightSequent.left, phi))
        invalid("Left-hand side of second premise does not contain φ as claimed.")
      else if (!isSameSet(bot.left, leftSequent.left ++ rightSequent.left.filterNot(isSame(_, phi))))
        invalid("Left-hand side of conclusion + φ is not the union of the left-hand sides of the premises.")
      else if (!isSameSet(bot.right, leftSequent.right.filterNot(isSame(_, phi)) ++ rightSequent.right))
        invalid("Right-hand side of conclusion + φ is not the union of the right-hand sides of the premises.")
      else
        SC.Cut(bot, premises(0), premises(1), phi)
    }
  }

  case object CutWithoutFormula extends ProofStepWithoutBotNorPrem(2) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val leftSequent = currentProof.getSequent(premises(0))
      lazy val rightSequent = currentProof.getSequent(premises(1))
      lazy val cutSet = rightSequent.left.diff(bot.left) ++ leftSequent.right.diff(bot.right)
      lazy val intersectedCutSet = rightSequent.left & leftSequent.right

      if (premises.length != 2)
        invalid(s"Two premises expected, ${premises.length} received.")
      else if (!cutSet.isEmpty)
        if (cutSet.tail.isEmpty)
          Cut(cutSet.head).asSCProof(bot, premises, currentProof)
        else
          invalid("Inferred cut pivot is not a singleton set.")
      else if (!intersectedCutSet.isEmpty && intersectedCutSet.tail.isEmpty)
        // can still find a pivot
        Cut(intersectedCutSet.head).asSCProof(bot, premises, currentProof)
      else
        invalid("A consistent cut pivot cannot be inferred from the premises. Possibly a missing or extraneous clause.")
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
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val phiAndPsi = ConnectorFormula(And, Seq(phi, psi))

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (!isSameSet(bot.right, premiseSequent.right))
        invalid("Right-hand side of the conclusion is not the same as the right-hand side of the premise.")
      else if (
        !isSameSet(bot.left + phi, premiseSequent.left + phiAndPsi) &&
        !isSameSet(bot.left + psi, premiseSequent.left + phiAndPsi) &&
        !isSameSet(bot.left + phi + psi, premiseSequent.left + phiAndPsi)
      )
        invalid("Left-hand side of premise + φ∧ψ is not the same as left-hand side of conclusion + either φ, ψ or both.")
      else
        SC.LeftAnd(bot, premises(0), phi, psi)
    }
  }

  case object LeftAndWithoutFormula extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val pivot = bot.left.diff(premiseSequent.left)

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (!pivot.isEmpty && pivot.tail.isEmpty)
        pivot.head match {
          case ConnectorFormula(And, Seq(phi, psi)) =>
            if (premiseSequent.left.contains(phi))
              LeftAnd(phi, psi).asSCProof(bot, premises, currentProof)
            else
              LeftAnd(psi, phi).asSCProof(bot, premises, currentProof)
          case _ => invalid("Could not infer a conjunction as pivot from premise and conclusion.")
        }
      else
      // try a rewrite, if it works, go ahead with it, otherwise malformed
      if (SC.isSameSequent(premiseSequent, bot))
        Rewrite.asSCProof(bot, premises, currentProof)
      else
        invalid("Left-hand side of premise + φ∧ψ is not the same as left-hand side of conclusion + either φ, ψ or both.")
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
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequents = premises.map(currentProof.getSequent(_))
      lazy val disjunction = ConnectorFormula(Or, disjuncts)

      if (premises.length == 0)
        invalid(s"Premises expected, ${premises.length} received.")
      else if (!isSameSet(bot.right, premiseSequents.map(_.right).reduce(_ union _)))
        invalid("Right-hand side of conclusion is not the union of the right-hand sides of the premises.")
      else if (!isSameSet(disjuncts.foldLeft(bot.left)(_ + _), premiseSequents.map(_.left).reduce(_ union _) + disjunction))
        invalid("Left-hand side of conclusion + disjuncts is not the same as the union of the left-hand sides of the premises + φ∨ψ.")
      else
        SC.LeftOr(bot, premises, disjuncts)
    }
  }
  case object LeftOrWithoutFormula extends ProofStepWithoutBotNorPrem(-1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequents = premises.map(currentProof.getSequent(_))
      lazy val pivots = premiseSequents.map(_.left.diff(bot.left))

      if (premises.length == 0)
        invalid(s"Premises expected, ${premises.length} received.")
      else if (pivots.exists(_.isEmpty))
        Weakening.asSCProof(bot, Seq(premises(pivots.indexWhere(_.isEmpty))), currentProof)
      else if (pivots.forall(_.tail.isEmpty))
        LeftOr(pivots.map(_.head)).asSCProof(bot, premises, currentProof)
      else
        // some extraneous formulae
        invalid("Left-hand side of conclusion + disjuncts is not the same as the union of the left-hand sides of the premises + φ∨ψ.")
    }
  }

  case object LeftOr extends ProofStepWithoutBotNorPrem(-1) {
    // default construction:
    // def apply(disjuncts: Seq[Formula]) = new LeftOr(disjuncts)
    def apply() = LeftOrWithoutFormula

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
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val leftSequent = currentProof.getSequent(premises(0))
      lazy val rightSequent = currentProof.getSequent(premises(1))
      lazy val implication = ConnectorFormula(Implies, Seq(phi, psi))

      if (premises.length != 2)
        invalid(s"Two premises expected, ${premises.length} received.")
      else if (!isSameSet(bot.right + phi, leftSequent.right union rightSequent.right))
        invalid("Right-hand side of conclusion + φ is not the union of right-hand sides of premises.")
      else if (!isSameSet(bot.left + psi, leftSequent.left union rightSequent.left + implication))
        invalid("Left-hand side of conclusion + ψ is not the union of left-hand sides of premises + φ→ψ.")
      else
        SC.LeftImplies(bot, premises(0), premises(1), phi, psi)
    }
  }

  case object LeftImpliesWithoutFormula extends ProofStepWithoutBotNorPrem(2) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val leftSequent = currentProof.getSequent(premises(0))
      lazy val rightSequent = currentProof.getSequent(premises(1))
      lazy val pivotLeft = leftSequent.right.diff(bot.right)
      lazy val pivotRight = rightSequent.left.diff(bot.left)

      if (premises.length != 2)
        invalid(s"Two premises expected, ${premises.length} received.")
      else if (pivotLeft.isEmpty)
        Weakening.asSCProof(bot, premises, currentProof)
      else if (pivotRight.isEmpty)
        Weakening.asSCProof(bot, premises, currentProof)
      else if (pivotLeft.tail.isEmpty && pivotRight.tail.isEmpty)
        LeftImplies(pivotLeft.head, pivotRight.head).asSCProof(bot, premises, currentProof)
      else
        invalid("Could not infer an implication as a pivot from the premises and conclusion, possible extraneous formulae in premises.")
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
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val implication = ConnectorFormula(Iff, Seq(phi, psi))
      lazy val impLeft = ConnectorFormula(Implies, Seq(phi, psi))
      lazy val impRight = ConnectorFormula(Implies, Seq(psi, phi))

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (!isSameSet(bot.right, premiseSequent.right))
        invalid("Right-hand side of premise is not the same as right-hand side of conclusion.")
      else if (
        !isSameSet(bot.left + impLeft, premiseSequent.left + implication) &&
        !isSameSet(bot.left + impRight, premiseSequent.left + implication) &&
        !isSameSet(bot.left + impLeft + impRight, premiseSequent.left + implication)
      )
        invalid("Left-hand side of premise + φ↔ψ is not the same as left-hand side of conclusion + either φ→ψ, ψ→φ or both.")
      else
        SC.LeftIff(bot, premises(0), phi, psi)
    }
  }

  case object LeftIffWithoutFormula extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val pivot = premiseSequent.left.diff(bot.left)

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (pivot.isEmpty)
        Weakening.asSCProof(bot, premises, currentProof)
      else
        pivot.head match {
          case ConnectorFormula(Implies, Seq(phi, psi)) => LeftIff(phi, psi).asSCProof(bot, premises, currentProof)
          case _ => invalid("Could not infer a pivot implication from premise.")
        }
    }
  }

  case object LeftIff extends ProofStepWithoutBotNorPrem(1) {
    // default construction:
    // def apply(phi: Formula, psi: Formula) = new LeftIff(phi, psi)
    def apply() = LeftIffWithoutFormula

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
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val negation = ConnectorFormula(Neg, Seq(phi))

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (!isSameSet(bot.right + phi, premiseSequent.right))
        invalid("Right-hand side of conclusion + φ is not the same as right-hand side of premise.")
      else if (!isSameSet(bot.left, premiseSequent.left + negation))
        invalid("Left-hand side of conclusion is not the same as left-hand side of premise + ¬φ.")
      else
        SC.LeftNot(bot, premises(0), phi)
    }
  }

  case object LeftNotWithoutFormula extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val pivot = premiseSequent.right.diff(bot.right)

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (pivot.isEmpty)
        Weakening.asSCProof(bot, premises, currentProof)
      else if (pivot.tail.isEmpty)
        LeftNot(pivot.head).asSCProof(bot, premises, currentProof)
      else
        invalid("Right-hand side of conclusion + φ is not the same as right-hand side of premise.")

    }
  }

  case object LeftNot extends ProofStepWithoutBotNorPrem(1) {
    // default construction:
    // def apply(phi: Formula) = new LeftNot(phi)
    def apply() = LeftNotWithoutFormula

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
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val quantified = BinderFormula(Forall, x, phi)
      lazy val instantiated = substituteVariables(phi, Map(x -> t))

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (!isSameSet(bot.right, premiseSequent.right))
        invalid("Right-hand side of conclusion is not the same as right-hand side of premise")
      else if (!isSameSet(bot.left + instantiated, premiseSequent.left + quantified))
        invalid("Left-hand side of conclusion + φ[t/x] is not the same as left-hand side of premise + ∀x. φ")
      else
        SC.LeftForall(bot, premises(0), phi, x, t)
    }
  }

  case class LeftForallWithoutFormula(t: Term) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val pivot = bot.left.diff(premiseSequent.left)
      lazy val instantiatedPivot = premiseSequent.left.diff(bot.left)

      if (premises.length != 1) invalid(s"One premise expected, ${premises.length} received.")
      else if (!pivot.isEmpty)
        if (pivot.tail.isEmpty)
          pivot.head match {
            case BinderFormula(Forall, x, phi) => LeftForall(phi, x, t).asSCProof(bot, premises, currentProof)
            case _ => invalid("Could not infer a universally quantified pivot from premise and conclusion.")
          }
        else
          invalid("Left-hand side of conclusion + φ[t/x] is not the same as left-hand side of premise + ∀x. φ.")
      else if (instantiatedPivot.isEmpty) Weakening.asSCProof(bot, premises, currentProof)
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
          case Some(BinderFormula(Forall, x, phi)) => LeftForall(phi, x, t).asSCProof(bot, premises, currentProof)
          case _ => invalid("Could not infer a universally quantified pivot from premise and conclusion.")
        }
      } else invalid("Left-hand side of conclusion + φ[t/x] is not the same as left-hand side of premise + ∀x. φ.")
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
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val quantified = BinderFormula(Exists, x, phi)

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if ((bot.left union bot.right).exists(_.freeVariables.contains(x)))
        invalid("The variable x must not be free in the resulting sequent.")
      else if (!isSameSet(bot.right, premiseSequent.right))
        invalid("Right-hand side of conclusion is not the same as right-hand side of premise")
      else if (!isSameSet(bot.left + phi, premiseSequent.left + quantified))
        invalid("Left-hand side of conclusion + φ is not the same as left-hand side of premise + ∃x. φ")
      else
        SC.LeftExists(bot, premises(0), phi, x)
    }
  }

  case object LeftExistsWithoutFormula extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val pivot = bot.left.diff(premiseSequent.left)
      lazy val instantiatedPivot = premiseSequent.left.diff(bot.left)

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty) Rewrite.asSCProof(bot, premises, currentProof)
        else if (instantiatedPivot.tail.isEmpty) {
          val in: Formula = instantiatedPivot.head
          val quantifiedPhi: Option[Formula] = bot.left.find(f =>
            f match {
              case BinderFormula(Exists, _, g) => isSame(g, in)
              case _ => false
            }
          )

          quantifiedPhi match {
            case Some(BinderFormula(Exists, x, phi)) => LeftExists(phi, x).asSCProof(bot, premises, currentProof)
            case _ => invalid("Could not infer an existensially quantified pivot from premise and conclusion.")
          }
        } else invalid("Left-hand side of conclusion + φ is not the same as left-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case BinderFormula(Exists, x, phi) => LeftExists(phi, x).asSCProof(bot, premises, currentProof)
          case _ => invalid("Could not infer an existentially quantified pivot from premise and conclusion.")
        }
      else
        invalid("Left-hand side of conclusion + φ is not the same as left-hand side of premise + ∃x. φ.")
    }
  }

  case object LeftExists extends ProofStepWithoutBotNorPrem(1) {
    // default construction:
    // def apply(phi: Formula, x: VariableLabel) = new LeftExists(phi, x)
    def apply() = LeftExistsWithoutFormula

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
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val y = VariableLabel(freshId(phi.freeVariables.map(_.id) + x.id, "y"))
      lazy val instantiated = BinderFormula(Exists, y, BinderFormula(Forall, x, ConnectorFormula(Iff, List(PredicateFormula(equality, List(VariableTerm(x), VariableTerm(y))), phi))))
      lazy val quantified = BinderFormula(ExistsOne, x, phi)

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (!isSameSet(bot.right, premiseSequent.right))
        invalid("Right-hand side of conclusion is not the same as right-hand side of premise.")
      else if (!isSameSet(bot.left + instantiated, premiseSequent.left + quantified))
        invalid("Left-hand side of conclusion + ∃y.∀x. (x=y) ↔ φ is not the same as left-hand side of premise + ∃!x. φ.")
      else
        SC.LeftExistsOne(bot, premises(0), phi, x)
    }
  }

  case object LeftExistsOneWithoutFormula extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val pivot = bot.left.diff(premiseSequent.left)
      lazy val instantiatedPivot = premiseSequent.left.diff(bot.left)

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty)
          Rewrite.asSCProof(bot, premises, currentProof)
        else if (instantiatedPivot.tail.isEmpty) {
          instantiatedPivot.head match {
            // ∃_. ∀x. _ ↔ φ == extract ==> x, phi
            case BinderFormula(Exists, _, BinderFormula(Forall, x, ConnectorFormula(Iff, Seq(_, phi)))) => LeftExistsOne(phi, x).asSCProof(bot, premises, currentProof)
            case _ => ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Could not infer an existentially quantified pivot from premise and conclusion.")
          }
        } else
          invalid("Left-hand side of conclusion + φ is not the same as left-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case BinderFormula(ExistsOne, x, phi) => SC.LeftExistsOne(bot, premises(0), phi, x)
          case _ => invalid("Could not infer an existentially quantified pivot from premise and conclusion.")
        }
      else
        invalid("Left-hand side of conclusion + φ is not the same as left-hand side of premise + ∃x. φ.")
    }
  }

  case object LeftExistsOne extends ProofStepWithoutBotNorPrem(1) {
    // default construction:
    // def apply(phi: Formula, x: VariableLabel) = new LeftExistsOne(phi, x)
    def apply() = LeftExistsOneWithoutFormula

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
  case class RightAnd(conjuncts: Seq[Formula]) extends ProofStepWithoutBotNorPrem(-1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequents = premises.map(currentProof.getSequent(_))
      lazy val conjunction = ConnectorFormula(And, conjuncts)

      if (premises.length == 0)
        invalid(s"Premises expected, ${premises.length} received.")
      else if (!isSameSet(bot.left, premiseSequents.map(_.left).reduce(_ union _)))
        invalid("Left-hand side of conclusion is not the union of the left-hand sides of the premises.")
      else if (!isSameSet(conjuncts.foldLeft(bot.right)(_ + _), premiseSequents.map(_.right).reduce(_ union _) + conjunction))
        invalid("Right-hand side of conclusion + conjuncts is not the same as the union of the right-hand sides of the premises + φ∧ψ....")
      else
        SC.RightAnd(bot, premises, conjuncts)
    }
  }
  case object RightAndWithoutFormula extends ProofStepWithoutBotNorPrem(-1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequents = premises.map(currentProof.getSequent(_))
      lazy val pivots = premiseSequents.map(_.right.diff(bot.right))

      if (premises.length == 0)
        invalid(s"Premises expected, ${premises.length} received.")
      else if (pivots.exists(_.isEmpty))
        Weakening.asSCProof(bot, Seq(premises(pivots.indexWhere(_.isEmpty))), currentProof)
      else if (pivots.forall(_.tail.isEmpty))
        RightAnd(pivots.map(_.head)).asSCProof(bot, premises, currentProof)
      else
        // some extraneous formulae
        invalid("Right-hand side of conclusion + φ + ψ is not the same as the union of the right-hand sides of the premises +φ∧ψ.")
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
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val phiAndPsi = ConnectorFormula(Or, Seq(phi, psi))

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (!isSameSet(bot.left, premiseSequent.left))
        invalid("Left-hand side of the premise is not the same as the left-hand side of the conclusion.")
      else if (
        !isSameSet(bot.right + phi, premiseSequent.right + phiAndPsi) &&
        !isSameSet(bot.right + psi, premiseSequent.right + phiAndPsi) &&
        !isSameSet(bot.right + phi + psi, premiseSequent.right + phiAndPsi)
      )
        invalid("Right-hand side of premise + φ∧ψ is not the same as right-hand side of conclusion + either φ, ψ or both.")
      else
        SC.RightOr(bot, premises(0), phi, psi)
    }
  }

  case object RightOrWithoutFormula extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val pivot = bot.right.diff(premiseSequent.right)

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (!pivot.isEmpty && pivot.tail.isEmpty)
        pivot.head match {
          case ConnectorFormula(Or, Seq(phi, psi)) =>
            if (premiseSequent.left.contains(phi))
              RightOr(phi, psi).asSCProof(bot, premises, currentProof)
            else
              RightOr(psi, phi).asSCProof(bot, premises, currentProof)
          case _ => invalid("Could not infer a disjunction as pivot from premise and conclusion.")
        }
      else
      // try a rewrite, if it works, go ahead with it, otherwise malformed
      if (SC.isSameSequent(premiseSequent, bot))
        Rewrite.asSCProof(bot, premises, currentProof)
      else
        invalid("Right-hand side of conclusion + φ∧ψ is not the same as right-hand side of premise + either φ, ψ or both.")
    }
  }

  case object RightOr extends ProofStepWithoutBotNorPrem(1) {
    // default construction:
    // def apply(phi: Formula, psi: Formula) = new RightOr(phi, psi)
    def apply() = RightOrWithoutFormula

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
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val implication = ConnectorFormula(Implies, Seq(phi, psi))

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (!isSameSet(bot.left + phi, premiseSequent.left))
        invalid("Left-hand side of conclusion + φ is not the same as left-hand side of premise.")
      else if (!isSameSet(bot.right + psi, premiseSequent.right + implication))
        invalid("Right-hand side of conclusion + ψ is not the same as right-hand side of premise + φ→ψ.")
      else
        SC.RightImplies(bot, premises(0), phi, psi)
    }
  }

  case object RightImpliesWithoutFormula extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val leftPivot = premiseSequent.left.diff(bot.left)
      lazy val rightPivot = premiseSequent.right.diff(bot.right)

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (
        !leftPivot.isEmpty && leftPivot.tail.isEmpty &&
        !rightPivot.isEmpty && rightPivot.tail.isEmpty
      )
        RightImplies(leftPivot.head, rightPivot.head).asSCProof(bot, premises, currentProof)
      else
        invalid("Right-hand side of conclusion + ψ is not the same as right-hand side of premise + φ→ψ.")
    }
  }

  case object RightImplies extends ProofStepWithoutBotNorPrem(1) {
    // default construction:
    // def apply(phi: Formula, psi: Formula) = new RightImplies(phi, psi)
    def apply() = RightImpliesWithoutFormula

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
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val leftSequent = currentProof.getSequent(premises(0))
      lazy val rightSequent = currentProof.getSequent(premises(1))
      lazy val implication = ConnectorFormula(Iff, Seq(phi, psi))
      lazy val impLeft = ConnectorFormula(Implies, Seq(phi, psi))
      lazy val impRight = ConnectorFormula(Implies, Seq(psi, phi))

      if (premises.length != 2)
        invalid(s"Two premises expected, ${premises.length} received.")
      else if (!isSameSet(bot.left, leftSequent.left union rightSequent.left))
        invalid("Left-hand side of conclusion is not the union of the left-hand sides of the premises.")
      else if (!isSameSet(bot.right + impLeft + impRight, leftSequent.right union rightSequent.right + implication))
        invalid("Right-hand side of conclusion + φ→ψ + ψ→φ is not the same as the union of the right-hand sides of the premises + φ↔ψ.")
      else
        SC.RightIff(bot, premises(0), premises(1), phi, psi)
    }
  }

  case object RightIffWithoutFormula extends ProofStepWithoutBotNorPrem(2) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val pivot = premiseSequent.right.diff(bot.right)

      if (premises.length != 2)
        invalid(s"Two premises expected, ${premises.length} received.")
      else if (pivot.isEmpty)
        Weakening.asSCProof(bot, Seq(premises(0)), currentProof)
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case ConnectorFormula(Implies, Seq(phi, psi)) => RightIff(phi, psi).asSCProof(bot, premises, currentProof)
          case _ => invalid("Could not infer an implication as pivot from premise and conclusion.")
        }
      else
        invalid("Right-hand side of conclusion + φ→ψ + ψ→φ is not the same as the union of the right-hand sides of the premises φ↔ψ.")
    }
  }

  case object RightIff extends ProofStepWithoutBotNorPrem(2) {
    // default construction:
    // def apply(phi: Formula, psi: Formula) = new RightIff(phi, psi)
    def apply() = RightIffWithoutFormula

    // usage without an argument list
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      this().asSCProof(bot, premises, currentProof)
  }

  /**
   * <pre>
   *   Γ, φ |- Δ
   * --------------
   *   Γ |- ¬φ, Δ
   * </pre>
   */
  case class RightNot(phi: Formula) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val negation = ConnectorFormula(Neg, Seq(phi))

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (!isSameSet(bot.left + phi, premiseSequent.left))
        invalid("Left-hand side of conclusion + φ is not the same as left-hand side of premise.")
      else if (!isSameSet(bot.right, premiseSequent.right + negation))
        invalid("Right-hand side of conclusion is not the same as right-hand side of premise + ¬φ.")
      else
        SC.RightNot(bot, premises(0), phi)
    }
  }

  case object RightNotWithoutFormula extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val pivot = premiseSequent.left.diff(bot.left)

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (pivot.isEmpty)
        Weakening.asSCProof(bot, Seq(premises(0)), currentProof)
      else if (pivot.tail.isEmpty)
        RightNot(pivot.head).asSCProof(bot, premises, currentProof)
      else
        invalid("Left-hand side of conclusion + φ is not the same as left-hand side of premise.")

    }
  }

  case object RightNot extends ProofStepWithoutBotNorPrem(1) {
    // default construction:
    // def apply(phi: Formula) = new RightNot(phi)
    def apply() = RightNotWithoutFormula

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
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val quantified = BinderFormula(Forall, x, phi)

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if ((bot.left union bot.right).exists(_.freeVariables.contains(x)))
        invalid("The variable x is free in the resulting sequent.")
      else if (!isSameSet(bot.left, premiseSequent.left))
        invalid("Left-hand side of conclusion is not the same as left-hand side of premise.")
      else if (!isSameSet(bot.right + phi, premiseSequent.right + quantified))
        invalid("Right-hand side of conclusion + φ is not the same as right-hand side of premise + ∀x. φ.")
      else
        SC.RightForall(bot, premises(0), phi, x)
    }
  }

  case object RightForallWithoutFormula extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val pivot = bot.right.diff(premiseSequent.right)
      lazy val instantiatedPivot = premiseSequent.right.diff(bot.right)

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty) Rewrite.asSCProof(bot, Seq(premises(0)), currentProof)
        else if (instantiatedPivot.tail.isEmpty) {
          val in: Formula = instantiatedPivot.head
          val quantifiedPhi: Option[Formula] = bot.right.find(f =>
            f match {
              case BinderFormula(Forall, _, g) => isSame(g, in)
              case _ => false
            }
          )

          quantifiedPhi match {
            case Some(BinderFormula(Forall, x, phi)) => RightForall(phi, x).asSCProof(bot, premises, currentProof)
            case _ => invalid("Could not infer a universally quantified pivot from premise and conclusion.")
          }
        } else invalid("Right-hand side of conclusion + φ is not the same as right-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case BinderFormula(Forall, x, phi) => RightForall(phi, x).asSCProof(bot, premises, currentProof)
          case _ => invalid("Could not infer a universally quantified pivot from premise and conclusion.")
        }
      else
        invalid("Right-hand side of conclusion + φ is not the same as right-hand side of premise + ∃x. φ.")
    }
  }

  case object RightForall extends ProofStepWithoutBotNorPrem(1) {
    // default construction:
    // def apply(phi: Formula, x: VariableLabel) = new RightForall(phi, x)
    def apply() = RightForallWithoutFormula

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
   * </pre>
   */
  case class RightExists(phi: Formula, x: VariableLabel, t: Term) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val quantified = BinderFormula(Exists, x, phi)
      lazy val instantiated = substituteVariables(phi, Map(x -> t))

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (!isSameSet(bot.left, premiseSequent.left))
        invalid("Left-hand side of conclusion is not the same as left-hand side of premise")
      else if (!isSameSet(bot.right + instantiated, premiseSequent.right + quantified))
        invalid("Right-hand side of conclusion + φ[t/x] is not the same as right-hand side of premise + ∃x. φ")
      else
        SC.RightExists(bot, premises(0), phi, x, t)
    }
  }

  case class RightExistsWithoutFormula(t: Term) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val pivot = bot.right.diff(premiseSequent.right)
      lazy val instantiatedPivot = premiseSequent.right.diff(bot.right)

      if (premises.length != 1) invalid(s"One premise expected, ${premises.length} received.")
      else if (!pivot.isEmpty)
        if (pivot.tail.isEmpty)
          pivot.head match {
            case BinderFormula(Exists, x, phi) => RightExists(phi, x, t).asSCProof(bot, premises, currentProof)
            case _ => invalid("Could not infer an existentially quantified pivot from premise and conclusion.")
          }
        else
          invalid("Right-hand side of conclusion + φ[t/x] is not the same as right-hand side of premise + ∀x. φ.")
      else if (instantiatedPivot.isEmpty) Weakening.asSCProof(bot, premises, currentProof)
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
          case Some(BinderFormula(Exists, x, phi)) => RightExists(phi, x, t).asSCProof(bot, premises, currentProof)
          case _ => invalid("Could not infer an existentially quantified pivot from premise and conclusion.")
        }
      } else invalid("Right-hand side of conclusion + φ[t/x] is not the same as right-hand side of premise + ∀x. φ.")
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
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val y = VariableLabel(freshId(phi.freeVariables.map(_.id) + x.id, "y"))
      lazy val instantiated = BinderFormula(Exists, y, BinderFormula(Forall, x, ConnectorFormula(Iff, List(PredicateFormula(equality, List(VariableTerm(x), VariableTerm(y))), phi))))
      lazy val quantified = BinderFormula(ExistsOne, x, phi)

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (!isSameSet(bot.left, premiseSequent.left))
        invalid("Left-hand side of conclusion is not the same as left-hand side of premise.")
      else if (!isSameSet(bot.right + instantiated, premiseSequent.right + quantified))
        invalid("Right-hand side of conclusion + ∃y.∀x. (x=y) ↔ φ is not the same as right-hand side of premise + ∃!x. φ.")
      else
        SC.RightExistsOne(bot, premises(0), phi, x)
    }
  }

  case object RightExistsOneWithoutFormula extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val pivot = bot.right.diff(premiseSequent.right)
      lazy val instantiatedPivot = premiseSequent.right.diff(bot.right)

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty)
          Rewrite.asSCProof(bot, premises, currentProof)
        else if (instantiatedPivot.tail.isEmpty) {
          instantiatedPivot.head match {
            // ∃_. ∀x. _ ↔ φ == extract ==> x, phi
            case BinderFormula(Exists, _, BinderFormula(Forall, x, ConnectorFormula(Iff, Seq(_, phi)))) => RightExistsOne(phi, x).asSCProof(bot, premises, currentProof)
            case _ => invalid("Could not infer an existentially quantified pivot from premise and conclusion.")
          }
        } else
          invalid("Right-hand side of conclusion + φ is not the same as right-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case BinderFormula(ExistsOne, x, phi) => RightExistsOne(phi, x).asSCProof(bot, premises, currentProof)
          case _ => invalid("Could not infer an existentially quantified pivot from premise and conclusion.")
        }
      else
        invalid("Right-hand side of conclusion + φ is not the same as right-hand side of premise + ∃x. φ.")
    }
  }

  case object RightExistsOne extends ProofStepWithoutBotNorPrem(1) {
    // default construction:
    // def apply(phi: Formula, x: VariableLabel) = new RightExistsOne(phi, x)
    def apply() = RightExistsOneWithoutFormula

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
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (!isSubset(premiseSequent.left, bot.left))
        invalid("Left-hand side of conclusion is not the same as left-hand side of premise.")
      else if (!isSubset(premiseSequent.right, bot.right))
        invalid("Left-hand side of premise is not a subset of left-hand side of conclusion.")
      else
        SC.Weakening(bot, premises(0))
    }
  }

  // Equality Rules
  /**
   * <pre>
   *  Γ, s=s |- Δ
   * --------------
   *     Γ |- Δ
   * </pre>
   */
  case class LeftRefl(phi: Formula) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (!isSameSet(bot.left + phi, premiseSequent.left))
        invalid("Left-hand sides of the conclusion + φ is not the same as left-hand side of the premise.")
      else if (!isSameSet(bot.right, premiseSequent.right))
        invalid("Right-hand side of the premise is not the same as the right-hand side of the conclusion.")
      else
        phi match {
          case PredicateFormula(`equality`, Seq(left, right)) =>
            if (isSame(left, right))
              SC.LeftRefl(bot, premises(0), phi)
            else
              invalid("φ is not an instance of reflexivity.")
          case _ => invalid("φ is not an equality.")
        }
    }
  }

  case object LeftReflWithoutFormula extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val pivot = premiseSequent.left.diff(bot.left)

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (!pivot.isEmpty && pivot.tail.isEmpty)
        LeftRefl(pivot.head).asSCProof(bot, premises, currentProof)
      else
        invalid("Could not infer an equality as pivot from premise and conclusion.")
    }
  }

  case object LeftRefl extends ProofStepWithoutBotNorPrem(1) {
    // default construction:
    // def apply(fa: Formula) = new LeftRefl(fa)
    def apply() = LeftReflWithoutFormula

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
  case class RightRefl(phi: Formula) extends ProofStepWithoutBotNorPrem(0) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      if (premises.length != 0)
        invalid(s"No premises expected, ${premises.length} received.")
      else if (!contains(bot.right, phi))
        invalid("Right-hand side of conclusion does not contain φ.")
      else
        phi match {
          case PredicateFormula(`equality`, Seq(left, right)) =>
            if (isSame(left, right))
              SC.RightRefl(bot, phi)
            else
              invalid("φ is not an instance of reflexivity.")
          case _ => invalid("φ is not an equality.")
        }
    }
  }

  case object RightReflWithoutFormula extends ProofStepWithoutBotNorPrem(0) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      if (premises.length != 0) invalid(s"No premises expected, ${premises.length} received.")
      else if (bot.right.isEmpty) invalid("Right-hand side of conclusion does not contain an instance of reflexivity.")
      else {
        // go through conclusion to see if you can find an reflexive formula
        val pivot: Option[Formula] = bot.right.find(f =>
          f match {
            case PredicateFormula(`equality`, Seq(l, r)) => isSame(l, r)
            case _ => false
          }
        )

        pivot match {
          case Some(phi) => RightRefl(phi).asSCProof(bot, premises, currentProof)
          case _ => invalid("Could not infer an equality as pivot from conclusion.")
        }

      }

    }
  }

  case object RightRefl extends ProofStepWithoutBotNorPrem(0) {
    // default construction:
    // def apply(fa: Formula) = new RightRefl(fa)
    def apply() = RightReflWithoutFormula

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
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val (s_es, t_es) = equals.unzip
      lazy val phi_s = lambdaPhi(s_es)
      lazy val phi_t = lambdaPhi(t_es)
      lazy val equalities = equals map { case (s, t) => PredicateFormula(equality, Seq(s, t)) }

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (!isSameSet(bot.right, premiseSequent.right))
        invalid("Right-hand side of the premise is not the same as the right-hand side of the conclusion.")
      else if (
        !isSameSet(bot.left + phi_s, premiseSequent.left ++ equalities + phi_t) &&
        !isSameSet(bot.left + phi_t, premiseSequent.left ++ equalities + phi_s)
      )
        invalid("Left-hand side of the conclusion + φ(s_) is not the same as left-hand side of the premise + (s=t)_ + φ(t_) (or with s_ and t_ swapped).")
      else
        SC.LeftSubstEq(bot, premises(0), equals, lambdaPhi)
    }
  }

  /**
   * <pre>
   *    Γ |- φ(s1,...,sn), Δ
   * ---------------------
   *  Γ, s1=premises(0), ..., sn=tn |- φ(premises(0),...tn), Δ
   * </pre>
   */
  case class RightSubstEq(equals: List[(Term, Term)], lambdaPhi: LambdaTermFormula) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val (s_es, t_es) = equals.unzip
      lazy val phi_s = lambdaPhi(s_es)
      lazy val phi_t = lambdaPhi(t_es)
      lazy val equalities = equals map { case (s, t) => PredicateFormula(equality, Seq(s, t)) }

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (!isSameSet(bot.left, premiseSequent.left ++ equalities))
        invalid("Left-hand side of the conclusion is not the same as the left-hand side of the premise + (s=t)_.")
      else if (
        !isSameSet(bot.left + phi_s, premiseSequent.left + phi_t) &&
        !isSameSet(bot.left + phi_t, premiseSequent.left + phi_s)
      )
        invalid("Right-hand side of the conclusion + φ(s_) is not the same as right-hand side of the premise + φ(t_) (or with s_ and t_ swapped).")
      else
        SC.RightSubstEq(bot, premises(0), equals, lambdaPhi)
    }
  }

  /**
   * <pre>
   *    Γ, φ(a1,...an) |- Δ
   * ---------------------
   *  Γ, a1↔b1, ..., an↔bn, φ(b1,...bn) |- Δ
   * </pre>
   */
  case class LeftSubstIff(equals: List[(Formula, Formula)], lambdaPhi: LambdaFormulaFormula) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val (psi_es, tau_es) = equals.unzip
      lazy val phi_psi = lambdaPhi(psi_es)
      lazy val phi_tau = lambdaPhi(tau_es)
      lazy val implications = equals map { case (s, t) => ConnectorFormula(Iff, Seq(s, t)) }

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (!isSameSet(bot.right, premiseSequent.right))
        invalid("Right-hand side of the premise is not the same as the right-hand side of the conclusion.")
      else if (
        !isSameSet(bot.left + phi_psi, premiseSequent.left ++ implications + phi_tau) &&
        !isSameSet(bot.left + phi_tau, premiseSequent.left ++ implications + phi_psi)
      )
        invalid("Left-hand side of the conclusion + φ(ψ_) is not the same as left-hand side of the premise + (ψ ↔ τ)_ + φ(τ_) (or with ψ_ and τ_ swapped).")
      else
        SC.LeftSubstIff(bot, premises(0), equals, lambdaPhi)
    }
  }

  /**
   * <pre>
   *    Γ |- φ(a1,...an), Δ
   * ---------------------
   *  Γ, a1↔b1, ..., an↔bn |- φ(b1,...bn), Δ
   * </pre>
   */
  case class RightSubstIff(equals: List[(Formula, Formula)], lambdaPhi: LambdaFormulaFormula) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))
      lazy val (psi_es, tau_es) = equals.unzip
      lazy val phi_psi = lambdaPhi(psi_es)
      lazy val phi_tau = lambdaPhi(tau_es)
      lazy val implications = equals map { case (s, t) => ConnectorFormula(Iff, Seq(s, t)) }

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (!isSameSet(bot.left, premiseSequent.left ++ implications))
        invalid("Left-hand side of the conclusion is not the same as the left-hand side of the premise + (ψ ↔ τ)_.")
      else if (
        !isSameSet(bot.left + phi_psi, premiseSequent.left + phi_tau) &&
        !isSameSet(bot.left + phi_tau, premiseSequent.left + phi_psi)
      )
        invalid("Right-hand side of the conclusion + φ(ψ_) is not the same as right-hand side of the premise + φ(τ_) (or with ψ_ and τ_ swapped).")
      else
        SC.RightSubstIff(bot, premises(0), equals, lambdaPhi)
    }
  }

  /**
   * <pre>
   *           Γ |- Δ
   * --------------------------
   *  Γ[r(a)/?f] |- Δ[r(a)/?f]
   * </pre>
   */
  case class InstFunSchema(insts: Map[SchematicTermLabel, LambdaTermTerm]) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (!isSameSet(bot.left, premiseSequent.left.map(instantiateTermSchemas(_, insts))))
        invalid("Left-hand side of premise instantiated with the map 'insts' is not the same as left-hand side of conclusion.")
      else if (!isSameSet(bot.right, premiseSequent.right.map(instantiateTermSchemas(_, insts))))
        invalid("Right-hand side of premise instantiated with the map 'insts' is not the same as right-hand side of conclusion.")
      else
        SC.InstFunSchema(bot, premises(0), insts)
    }
  }

  /**
   * <pre>
   *           Γ |- Δ
   * --------------------------
   *  Γ[ψ(a)/?p] |- Δ[ψ(a)/?p]
   * </pre>
   */
  case class InstPredSchema(insts: Map[SchematicVarOrPredLabel, LambdaTermFormula]) extends ProofStepWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this.asProofStepWithoutBot(premises).asProofStep(bot),
        msg
      )

      lazy val premiseSequent = currentProof.getSequent(premises(0))

      if (premises.length != 1)
        invalid(s"One premise expected, ${premises.length} received.")
      else if (!isSameSet(bot.left, premiseSequent.left.map(instantiatePredicateSchemas(_, insts))))
        invalid("Left-hand side of premise instantiated with the map 'insts' is not the same as left-hand side of conclusion.")
      else if (!isSameSet(bot.right, premiseSequent.right.map(instantiatePredicateSchemas(_, insts))))
        invalid("Right-hand side of premise instantiated with the map 'insts' is not the same as right-hand side of conclusion.")
      else
        SC.InstPredSchema(bot, premises(0), insts)
    }
  }

  // Proof Organisation rules
  case class SCSubproof(sp: SCProof, premises: Seq[Int] = Seq.empty, display: Boolean = true) extends ProofStep {
    def asSCProof(currentProof: Library#Proof): ProofStepJudgement = {
      def invalid(msg: String) = ProofStepJudgement.InvalidProofStep(
        this,
        msg
      )

      lazy val premiseSequents = premises.map(currentProof.getSequent(_))
      lazy val invalidPremise = premises.zipWithIndex.find((no, p) => !SC.isSameSequent(premiseSequents(no), sp.imports(p)))

      if (premises.length != sp.imports.length)
        invalid(s"Subproof expected ${sp.imports.length} premises, ${premises.length} received.")
      else if (!invalidPremise.isEmpty)
        invalid(s"Premise number ${invalidPremise.get._1} (refering to step ${invalidPremise.get}) is not the same as import number ${invalidPremise.get._1} of the subproof.")
      else
        SC.SCSubproof(sp, premises)
    }
  }

}
