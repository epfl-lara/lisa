package lisa.utils.tactics

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.SCProofStep
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.kernel.proof.SequentCalculus as SC
import lisa.utils.Helpers.*
import lisa.utils.{Library, LisaException, OutputManager}
import lisa.utils.tactics.BasicStepTactic.LeftForallWithoutFormula
import lisa.utils.tactics.ProofTacticLib.{*, given}

object BasicStepTactic {

  final class Hypothesis(using val proof: Library#Proof) extends ProofTacticWithoutBot {
    val premises: Seq[proof.Fact] = Seq()
    def asSCProof(premMap: proof.Fact => Int, bot: Sequent): ProofTacticJudgement =
      SC.Hypothesis(bot, bot.left.intersect(bot.right).head)
  }

  
  final class Rewrite(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
      SC.Rewrite(bot, premises(0))
  }
  

  /**
   * <pre>
   *  Γ |- Δ, φ    φ, Σ |- Π
   * ------------------------
   *       Γ, Σ |-Δ, Π
   * </pre>
   */
  final class Cut(phi: Formula)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(2) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
      SC.Cut(bot, premises(0), premises(1), phi)
  }

  final class CutWithoutFormula(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(2) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement = {
      val leftSequent = proof.getSequent(premises(0))
      val rightSequent = proof.getSequent(premises(1))
      val cutSet = rightSequent.left.diff(bot.left) ++ leftSequent.right.diff(bot.right)
      lazy val intersectedCutSet = rightSequent.left & leftSequent.right

      if (!cutSet.isEmpty)
        if (cutSet.tail.isEmpty) {
          SC.Cut(bot, premises(0), premises(1), cutSet.head)
        } else
          ProofTacticJudgement.InvalidProofTactic("Inferred cut pivot is not a singleton set.")
      else if (!intersectedCutSet.isEmpty && intersectedCutSet.tail.isEmpty)
      // can still find a pivot
        SC.Cut(bot, premises(0), premises(1), intersectedCutSet.head)
      else
        ProofTacticJudgement.InvalidProofTactic("A consistent cut pivot cannot be inferred from the premises. Possibly a missing or extraneous clause.")
    }
  }



  
  // Left rules
  /**
   * <pre>
   *   Γ, φ |- Δ                Γ, φ, ψ |- Δ
   * --------------     or     --------------
   *  Γ, φ∧ψ |- Δ               Γ, φ∧ψ |- Δ
   * </pre>
   */
  final class LeftAnd(phi: Formula, psi: Formula)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
      SC.LeftAnd(bot, premises(0), phi, psi)
  }

  final class LeftAndWithoutFormula(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premises(0))
      val pivot = bot.left.diff(premiseSequent.left)

      if (!pivot.isEmpty && pivot.tail.isEmpty)
        pivot.head match {
          case ConnectorFormula(And, Seq(phi, psi)) =>
            if (premiseSequent.left.contains(phi))
              SC.LeftAnd(bot, premises(0), phi, psi)
            else
              SC.LeftAnd(bot, premises(0), psi, phi)
          case _ => ProofTacticJudgement.InvalidProofTactic("Could not infer a conjunction as pivot from premise and conclusion.")
        }
      else
      // try a rewrite, if it works, go ahead with it, otherwise malformed
        if (SC.isSameSequent(premiseSequent, bot))
          SC.Rewrite(bot, premises(0))
        else
          ProofTacticJudgement.InvalidProofTactic("Left-hand side of conclusion + φ∧ψ must be same as left-hand side of premise + either φ, ψ or both.")
    }
  }


  /**
   * <pre>
   *  Γ, φ |- Δ    Σ, ψ |- Π    ...
   * --------------------------------
   *    Γ, Σ, φ∨ψ∨... |- Δ, Π
   * </pre>
   */
  final class LeftOr(disjuncts: Seq[Formula])(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(-1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement = {
      SC.LeftOr(bot, premises, disjuncts)
    }
  }
  final class LeftOrWithoutFormula(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(-1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement = {
      val premiseSequents = premises.map(proof.getSequent(_))
      val pivots = premiseSequents.map(_.left.diff(bot.left))

      if (pivots.exists(_.isEmpty))
        SC.Weakening(bot, premises(pivots.indexWhere(_.isEmpty)))
      else if (pivots.forall(_.tail.isEmpty))
        SC.LeftOr(bot, premises, pivots.map(_.head))
      else
      // some extraneous formulae
        ProofTacticJudgement.InvalidProofTactic("Left-hand side of conclusion + disjuncts is not the same as the union of the left-hand sides of the premises + φ∨ψ.")
    }
  }


  /**
   * <pre>
   *  Γ |- φ, Δ    Σ, ψ |- Π
   * ------------------------
   *    Γ, Σ, φ→ψ |- Δ, Π
   * </pre>
   */
  final class LeftImplies(phi: Formula, psi: Formula)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(2) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
      SC.LeftImplies(bot, premises(0), premises(1), phi, psi)
  }

  final class LeftImpliesWithoutFormula(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(2) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement = {
      val leftSequent = proof.getSequent(premises(0))
      val rightSequent = proof.getSequent(premises(1))
      val pivotLeft = leftSequent.right.diff(bot.right)
      lazy val pivotRight = rightSequent.left.diff(bot.left)

      if (pivotLeft.isEmpty)
        SC.Weakening(bot, premises(0))
      else if (pivotRight.isEmpty)
        SC.Weakening(bot, premises(1))
      else if (pivotLeft.tail.isEmpty && pivotRight.tail.isEmpty)
        SC.LeftImplies(bot, premises(0), premises(1), pivotLeft.head, pivotRight.head)
      else
        ProofTacticJudgement.InvalidProofTactic("Could not infer an implication as a pivot from the premises and conclusion, possible extraneous formulae in premises.")
    }
  }


  /**
   * <pre>
   *  Γ, φ→ψ |- Δ               Γ, φ→ψ, ψ→φ |- Δ
   * --------------    or     --------------------
   *  Γ, φ↔ψ |- Δ                 Γ, φ↔ψ |- Δ
   * </pre>
   */
  final class LeftIff(phi: Formula, psi: Formula)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
      SC.LeftIff(bot, premises(0), phi, psi)
  }

  final class LeftIffWithoutFormula()(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premises(0))
      val pivot = premiseSequent.left.diff(bot.left)

      if (pivot.isEmpty)
        SC.Weakening(bot, premises(0))
      else
        pivot.head match {
          case ConnectorFormula(Implies, Seq(phi, psi)) => SC.LeftIff(bot, premises(0), phi, psi)
          case _ => ProofTacticJudgement.InvalidProofTactic("Could not infer a pivot implication from premise.")
        }
    }
  }


  /**
   * <pre>
   *   Γ |- φ, Δ
   * --------------
   *   Γ, ¬φ |- Δ
   * </pre>
   */
  final class LeftNot(phi: Formula)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
      SC.LeftNot(bot, premises(0), phi)
  }

  final class LeftNotWithoutFormula(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premises(0))
      val pivot = premiseSequent.right.diff(bot.right)

      if (pivot.isEmpty)
        SC.Weakening(bot, premises(0))
      else if (pivot.tail.isEmpty)
        SC.LeftNot(bot, premises(0), pivot.head)
      else
        ProofTacticJudgement.InvalidProofTactic("Right-hand side of conclusion + φ must be the same as right-hand side of premise.")

    }
  }



  /**
   * <pre>
   *   Γ, φ[t/x] |- Δ
   * -------------------
   *   Γ, ∀x. φ |- Δ
   *
   * </pre>
   */
  final class LeftForall(phi: Formula, x: VariableLabel, t: Term)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
      SC.LeftForall(bot, premises(0), phi, x, t)
  }

  final class LeftForallWithoutFormula(t: Term)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premises(0))
      val pivot = bot.left.diff(premiseSequent.left)
      lazy val instantiatedPivot = premiseSequent.left.diff(bot.left)

      if (pivot.nonEmpty)
        if (pivot.tail.isEmpty)
          pivot.head match {
            case BinderFormula(Forall, x, phi) => SC.LeftForall(bot, premises(0), phi, x, t)
            case _ => ProofTacticJudgement.InvalidProofTactic("Could not infer a universally quantified pivot from premise and conclusion.")
          }
        else
          ProofTacticJudgement.InvalidProofTactic("Left-hand side of conclusion + φ[t/x] must be the same as left-hand side of premise + ∀x. φ.")
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
          case _ => ProofTacticJudgement.InvalidProofTactic("Could not infer a universally quantified pivot from premise and conclusion.")
        }
      } else ProofTacticJudgement.InvalidProofTactic("Left-hand side of conclusion + φ[t/x] must be the same as left-hand side of premise + ∀x. φ.")
    }
  }

  // def apply() = new LeftForallWithoutFormulaOrTerm()


  /**
   * <pre>
   *    Γ, φ |- Δ
   * ------------------- if x is not free in the resulting sequent
   *  Γ, ∃x φ|- Δ
   *
   * </pre>
   */
  final class LeftExists(phi: Formula, x: VariableLabel)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
      SC.LeftExists(bot, premises(0), phi, x)
  }

  final class LeftExistsWithoutFormula()(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premises(0))
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
            case _ => ProofTacticJudgement.InvalidProofTactic("Could not infer an existensially quantified pivot from premise and conclusion.")
          }
        } else ProofTacticJudgement.InvalidProofTactic("Left-hand side of conclusion + φ must be the same as left-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case BinderFormula(Exists, x, phi) => SC.LeftExists(bot, premises(0), phi, x)
          case _ => ProofTacticJudgement.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
        }
      else
        ProofTacticJudgement.InvalidProofTactic("Left-hand side of conclusion + φ must be the same as left-hand side of premise + ∃x. φ.")
    }
  }


  /**
   * <pre>
   *  Γ, ∃y.∀x. (x=y) ↔ φ |-  Δ
   * ---------------------------- if y is not free in φ
   *      Γ, ∃!x. φ |- Δ
   * </pre>
   */
  final class LeftExistsOne(phi: Formula, x: VariableLabel)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
      SC.LeftExistsOne(bot, premises(0), phi, x)
  }

  final class LeftExistsOneWithoutFormula()(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premises(0))
      val pivot = bot.left.diff(premiseSequent.left)
      lazy val instantiatedPivot = premiseSequent.left.diff(bot.left)

      if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty)
          SC.Rewrite(bot, premises(0))
        else if (instantiatedPivot.tail.isEmpty) {
          instantiatedPivot.head match {
            // ∃_. ∀x. _ ↔ φ == extract ==> x, phi
            case BinderFormula(Exists, _, BinderFormula(Forall, x, ConnectorFormula(Iff, Seq(_, phi)))) => SC.LeftExistsOne(bot, premises(0), phi, x)
            case _ => ProofTacticJudgement.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
          }
        } else
          ProofTacticJudgement.InvalidProofTactic("Left-hand side of conclusion + φ must be the same as left-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case BinderFormula(ExistsOne, x, phi) => SC.LeftExistsOne(bot, premises(0), phi, x)
          case _ => ProofTacticJudgement.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
        }
      else
        ProofTacticJudgement.InvalidProofTactic("Left-hand side of conclusion + φ must be the same as left-hand side of premise + ∃x. φ.")
    }
  }



  // Right rules
  /**
   * <pre>
   *  Γ |- φ, Δ    Σ |- ψ, Π     ...
   * ------------------------------------
   *    Γ, Σ |- φ∧ψ∧..., Π, Δ
   * </pre>
   */
  final class RightAnd(cunjuncts: Seq[Formula])(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(-1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
      SC.RightAnd(bot, premises, cunjuncts)
  }
  final class RightAndWithoutFormula(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(-1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement = {
      val premiseSequents = premises.map(proof.getSequent(_))
      val pivots = premiseSequents.map(_.right.diff(bot.right))

      if (pivots.exists(_.isEmpty))
        SC.Weakening(bot, premises(pivots.indexWhere(_.isEmpty)))
      else if (pivots.forall(_.tail.isEmpty))
        SC.RightAnd(bot, premises, pivots.map(_.head))
      else
      // some extraneous formulae
        ProofTacticJudgement.InvalidProofTactic("Right-hand side of conclusion + φ + ψ is not the same as the union of the right-hand sides of the premises +φ∧ψ.")
    }
  }


  /**
   * <pre>
   *   Γ |- φ, Δ               Γ |- φ, ψ, Δ
   * --------------    or    ---------------
   *  Γ |- φ∨ψ, Δ              Γ |- φ∨ψ, Δ
   * </pre>
   */
  final class RightOr(phi: Formula, psi: Formula)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
      SC.RightOr(bot, premises(0), phi, psi)
  }

  final class RightOrWithoutFormula()(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premises(0))
      val pivot = bot.right.diff(premiseSequent.right)

      if (!pivot.isEmpty && pivot.tail.isEmpty)
        pivot.head match {
          case ConnectorFormula(Or, Seq(phi, psi)) =>
            if (premiseSequent.left.contains(phi))
              SC.RightOr(bot, premises(0), phi, psi)
            else
              SC.RightOr(bot, premises(0), psi, phi)
          case _ => ProofTacticJudgement.InvalidProofTactic("Could not infer a disjunction as pivot from premise and conclusion.")
        }
      else
      // try a rewrite, if it works, go ahead with it, otherwise malformed
        if (SC.isSameSequent(premiseSequent, bot))
          SC.Rewrite(bot, premises(0))
        else
          ProofTacticJudgement.InvalidProofTactic("Right-hand side of conclusion + φ∧ψ must be same as right-hand side of premise + either φ, ψ or both.")
    }
  }


  /**
   * <pre>
   *  Γ, φ |- ψ, Δ
   * --------------
   *  Γ |- φ→ψ, Δ
   * </pre>
   */
  final class RightImplies(phi: Formula, psi: Formula)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
      SC.RightImplies(bot, premises(0), phi, psi)
  }

  final class RightImpliesWithoutFormula()(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premises(0))
      val leftPivot = premiseSequent.left.diff(bot.left)
      val rightPivot = premiseSequent.right.diff(bot.right)

      if (
        !leftPivot.isEmpty && leftPivot.tail.isEmpty &&
            !rightPivot.isEmpty && rightPivot.tail.isEmpty
      )
        SC.RightImplies(bot, premises(0), leftPivot.head, rightPivot.head)
      else
        ProofTacticJudgement.InvalidProofTactic("Right-hand side of conclusion + ψ must be same as right-hand side of premise + φ→ψ.")
    }
  }


  /**
   * <pre>
   *  Γ |- φ→ψ, Δ    Σ |- ψ→φ, Π
   * ----------------------------
   *      Γ, Σ |- φ↔ψ, Π, Δ
   * </pre>
   */
  final class RightIff(phi: Formula, psi: Formula)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(2) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
      SC.RightIff(bot, premises(0), premises(1), phi, psi)
  }

  final class RightIffWithoutFormula()(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(2) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premises(0))
      val pivot = premiseSequent.right.diff(bot.right)

      if (pivot.isEmpty)
        SC.Weakening(bot, premises(0))
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case ConnectorFormula(Implies, Seq(phi, psi)) => SC.RightIff(bot, premises(0), premises(1), phi, psi)
          case _ => ProofTacticJudgement.InvalidProofTactic("Could not infer an implication as pivot from premise and conclusion.")
        }
      else
        ProofTacticJudgement.InvalidProofTactic("Right-hand side of conclusion + φ→ψ + ψ→φ is not the same as the union of the right-hand sides of the premises φ↔ψ.")
    }
  }


  /**
   * <pre>
   *  Γ, φ |- Δ
   * --------------
   *   Γ |- ¬φ, Δ
   * </pre>
   */
  final class RightNot(phi: Formula)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
      SC.RightNot(bot, premises(0), phi)
  }

  final class RightNotWithoutFormula()(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premises(0))
      val pivot = premiseSequent.left.diff(bot.left)

      if (pivot.isEmpty)
        SC.Weakening(bot, premises(0))
      else if (pivot.tail.isEmpty)
        SC.RightNot(bot, premises(0), pivot.head)
      else
        ProofTacticJudgement.InvalidProofTactic("Left-hand side of conclusion + φ must be the same as left-hand side of premise.")

    }
  }


  /**
   * <pre>
   *    Γ |- φ, Δ
   * ------------------- if x is not free in the resulting sequent
   *  Γ |- ∀x. φ, Δ
   * </pre>
   */
  final class RightForall(phi: Formula, x: VariableLabel)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
      SC.RightForall(bot, premises(0), phi, x)
  }

  final class RightForallWithoutFormula()(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premises(0))
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
            case _ => ProofTacticJudgement.InvalidProofTactic("Could not infer a universally quantified pivot from premise and conclusion.")
          }
        } else ProofTacticJudgement.InvalidProofTactic("Right-hand side of conclusion + φ must be the same as right-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case BinderFormula(Forall, x, phi) => SC.RightForall(bot, premises(0), phi, x)
          case _ => ProofTacticJudgement.InvalidProofTactic("Could not infer a universally quantified pivot from premise and conclusion.")
        }
      else
        ProofTacticJudgement.InvalidProofTactic("Right-hand side of conclusion + φ must be the same as right-hand side of premise + ∃x. φ.")
    }
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
  final class RightExists(phi: Formula, x: VariableLabel, t: Term)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
      SC.RightExists(bot, premises(0), phi, x, t)
  }

  final class RightExistsWithoutFormula(t: Term)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premises(0))
      val pivot = bot.right.diff(premiseSequent.right)
      lazy val instantiatedPivot = premiseSequent.right.diff(bot.right)

      if (!pivot.isEmpty)
        if (pivot.tail.isEmpty)
          pivot.head match {
            case BinderFormula(Exists, x, phi) => SC.RightExists(bot, premises(0), phi, x, t)
            case _ => ProofTacticJudgement.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
          }
        else
          ProofTacticJudgement.InvalidProofTactic("Right-hand side of conclusion + φ[t/x] must be the same as right-hand side of premise + ∀x. φ.")
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
          case _ => ProofTacticJudgement.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
        }
      } else
        ProofTacticJudgement.InvalidProofTactic("Right-hand side of conclusion + φ[t/x] must be the same as right-hand side of premise + ∀x. φ.")
    }
  }
  // def RightExists() = new RightExistsWithoutFormulaOrTerm


  /**
   * <pre>
   *  Γ |- ∃y.∀x. (x=y) ↔ φ, Δ
   * ---------------------------- if y is not free in φ
   *      Γ|- ∃!x. φ,  Δ
   * </pre>
   */
  final class RightExistsOne(phi: Formula, x: VariableLabel)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
      SC.RightExistsOne(bot, premises(0), phi, x)
  }

  final class RightExistsOneWithoutFormula(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premises(0))
      val pivot = bot.right.diff(premiseSequent.right)
      lazy val instantiatedPivot = premiseSequent.right.diff(bot.right)

      if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty)
          SC.Rewrite(bot, premises(0))
        else if (instantiatedPivot.tail.isEmpty) {
          instantiatedPivot.head match {
            // ∃_. ∀x. _ ↔ φ == extract ==> x, phi
            case BinderFormula(Exists, _, BinderFormula(Forall, x, ConnectorFormula(Iff, Seq(_, phi)))) => SC.RightExistsOne(bot, premises(0), phi, x)
            case _ => ProofTacticJudgement.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
          }
        } else
          ProofTacticJudgement.InvalidProofTactic("Right-hand side of conclusion + φ must be the same as right-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case BinderFormula(ExistsOne, x, phi) => SC.RightExistsOne(bot, premises(0), phi, x)
          case _ => ProofTacticJudgement.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
        }
      else
        ProofTacticJudgement.InvalidProofTactic("Right-hand side of conclusion + φ must be the same as right-hand side of premise + ∃x. φ.")
    }
  }


  // Structural rules
  /**
   * <pre>
   *     Γ |- Δ
   * --------------
   *   Γ, Σ |- Δ, Π
   * </pre>
   */
  final class Weakening(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
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
  final class LeftRefl(fa: Formula)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
      SC.LeftRefl(bot, premises(0), fa)
  }

  final class LeftReflWithoutFormula(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
      SC.Rewrite(bot, premises(0))
  }


  /**
   * <pre>
   *
   * --------------
   *     |- s=s
   * </pre>
   */
  final class RightRefl(using val proof: Library#Proof)(fa: Formula) extends ProofTacticWithoutBotNorPrem(0) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
      SC.RightRefl(bot, fa)
  }

  final class RightReflWithoutFormula(using val proof: Library#Proof)() extends ProofTacticWithoutBotNorPrem(0) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
      SC.RewriteTrue(bot)
  }


  /**
   * <pre>
   *    Γ, φ(s1,...,sn) |- Δ
   * ---------------------
   *  Γ, s1=premises(0), ..., sn=tn, φ(premises(0),...tn) |- Δ
   * </pre>
   */
  final class LeftSubstEq(equals: List[(Term, Term)], lambdaPhi: LambdaTermFormula)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
      SC.LeftSubstEq(bot, premises(0), equals, lambdaPhi)
  }

  /**
   * <pre>
   *    Γ |- φ(s1,...,sn), Δ
   * ---------------------
   *  Γ, s1=premises(0), ..., sn=tn |- φ(premises(0),...tn), Δ
   * </pre>
   */
  final class RightSubstEq(equals: List[(Term, Term)], lambdaPhi: LambdaTermFormula)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
      SC.RightSubstEq(bot, premises(0), equals, lambdaPhi)
  }

  /**
   * <pre>
   *    Γ, φ(a1,...an) |- Δ
   * ---------------------
   *  Γ, a1↔b1, ..., an↔bn, φ(b1,...bn) |- Δ
   * </pre>
   */
  final class LeftSubstIff(equals: List[(Formula, Formula)], lambdaPhi: LambdaFormulaFormula)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
      SC.LeftSubstIff(bot, premises(0), equals, lambdaPhi)
  }

  /**
   * <pre>
   *    Γ |- φ(a1,...an), Δ
   * ---------------------
   *  Γ, a1↔b1, ..., an↔bn |- φ(b1,...bn), Δ
   * </pre>
   */
  final class RightSubstIff(equals: List[(Formula, Formula)], lambdaPhi: LambdaFormulaFormula)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
      SC.RightSubstIff(bot, premises(0), equals, lambdaPhi)
  }

  /**
   * <pre>
   *           Γ |- Δ
   * --------------------------
   *  Γ[r(a)/?f] |- Δ[r(a)/?f]
   * </pre>
   */
  final class InstFunSchema(insts: Map[SchematicTermLabel, LambdaTermTerm])(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
      SC.InstFunSchema(bot, premises(0), insts)
  }

  /**
   * <pre>
   *           Γ |- Δ
   * --------------------------
   *  Γ[ψ(a)/?p] |- Δ[ψ(a)/?p]
   * </pre>
   */
  final class InstPredSchema(insts: Map[SchematicVarOrPredLabel, LambdaTermFormula])(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
      SC.InstPredSchema(bot, premises(0), insts)
  }

  class SUBPROOF (using val proof: Library#Proof, om:OutputManager)
                 (statement: Sequent | String, val line:Int, val file:String)
                 (computeProof: proof.InnerProof ?=> Unit) extends ProofTactic {
    val bot:Sequent = statement match {
      case s: Sequent => s
      case s: String => lisa.utils.Parser.parseSequent(s)
    }

    val iProof:proof.InnerProof = new proof.InnerProof(bot)
    val scproof: SCProof = {
      try {
        computeProof(using iProof)
      } catch {
        case e: NotImplementedError => om.lisaThrow(new LisaException.EmptyProofException("Closed empty subproof."))
        case e: LisaException => om.lisaThrow(e)
      }
      if (proof.length == 0)
        om.lisaThrow(new LisaException.EmptyProofException("Closed empty subproof."))
      iProof.toSCProof
    }
    val premises = iProof.getImports.map(of => of._1)

    override def asSCProof(premMap: proof.Fact => Int): ProofTacticJudgement = {
      ProofTacticJudgement.ValidProofTactic(SC.SCSubproof(scproof, premises map premMap))
    }
  }



}