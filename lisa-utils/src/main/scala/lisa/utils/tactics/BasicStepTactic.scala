package lisa.utils.tactics

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.SCProofStep
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.kernel.proof.SequentCalculus as SC
import lisa.utils.Helpers.*
import lisa.utils.Library
import lisa.utils.LisaException
import lisa.utils.OutputManager
import lisa.utils.UserLisaException
import lisa.utils.tactics.ProofTacticLib.{_, given}

object BasicStepTactic {

  object Hypothesis extends ProofTactic with ParameterlessHave {
    def apply(using proof: Library#Proof)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.Hypothesis(bot, bot.left.intersect(bot.right).head)), Seq())
  }

  object Rewrite extends ProofTactic with ParameterlessAndThen {
    def apply(using proof: Library#Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.Rewrite(bot, -1)), Seq(premise))
  }

  /**
   * <pre>
   *  Γ |- Δ, φ    φ, Σ |- Π
   * ------------------------
   *       Γ, Σ |-Δ, Π
   * </pre>
   */
  object Cut extends ProofTactic {
    def apply(using proof: Library#Proof)(phi: Formula)(prem1: proof.Fact, prem2: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.Cut(bot, -1, -2, phi)), Seq(prem1, prem2))

    def apply(using proof: Library#Proof)(prem1: proof.Fact, prem2: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      val leftSequent = proof.getSequent(prem1)
      val rightSequent = proof.getSequent(prem2)
      val cutSet = rightSequent.left.diff(bot.left) ++ leftSequent.right.diff(bot.right)
      lazy val intersectedCutSet = rightSequent.left & leftSequent.right

      if (cutSet.nonEmpty)
        if (cutSet.tail.isEmpty) {
          proof.ValidProofTactic(Seq(SC.Cut(bot, -1, -2, cutSet.head)), Seq(prem1, prem2))
        } else
          proof.InvalidProofTactic("Inferred cut pivot is not a singleton set.")
      else if (intersectedCutSet.nonEmpty && intersectedCutSet.tail.isEmpty)
        // can still find a pivot
        proof.ValidProofTactic(Seq(SC.Cut(bot, -1, -2, intersectedCutSet.head)), Seq(prem1, prem2))
      else
        proof.InvalidProofTactic("A consistent cut pivot cannot be inferred from the premises. Possibly a missing or extraneous clause.")
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
  object LeftAnd extends ProofTactic with ParameterlessAndThen {
    def apply(using proof: Library#Proof)(phi: Formula, psi: Formula)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.LeftAnd(bot, -1, phi, psi)), Seq(premise))
    def apply(using proof: Library#Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premise)
      val pivot = bot.left.diff(premiseSequent.left)

      if (pivot.nonEmpty && pivot.tail.isEmpty)
        pivot.head match {
          case ConnectorFormula(And, Seq(phi, psi)) =>
            if (premiseSequent.left.contains(phi))
              proof.ValidProofTactic(Seq(SC.LeftAnd(bot, -1, phi, psi)), Seq(premise))
            else
              proof.ValidProofTactic(Seq(SC.LeftAnd(bot, -1, psi, phi)), Seq(premise))
          case _ => proof.InvalidProofTactic("Could not infer a conjunction as pivot from premise and conclusion.")
        }
      else
      // try a rewrite, if it works, go ahead with it, otherwise malformed
      if (SC.isSameSequent(premiseSequent, bot))
        proof.ValidProofTactic(Seq(SC.Rewrite(bot, -1)), Seq(premise))
      else
        proof.InvalidProofTactic("Left-hand side of conclusion + φ∧ψ must be same as left-hand side of premise + either φ, ψ or both.")
    }
  }

  /**
   * <pre>
   *  Γ, φ |- Δ    Σ, ψ |- Π    ...
   * --------------------------------
   *    Γ, Σ, φ∨ψ∨... |- Δ, Π
   * </pre>
   */
  object LeftOr extends ProofTactic {
    def apply(using proof: Library#Proof)(phis: Formula*)(premises: proof.Fact*)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.LeftOr(bot, Range(-1, -premises.length - 1, -1), phis)), premises.toSeq)
    def apply(using proof: Library#Proof)(premises: proof.Fact*)(bot: Sequent): proof.ProofTacticJudgement = {
      val premiseSequents = premises.map(proof.getSequent)
      val pivots = premiseSequents.map(_.left.diff(bot.left))

      if (pivots.exists(_.isEmpty))
        proof.ValidProofTactic(Seq(SC.Weakening(bot, pivots.indexWhere(_.isEmpty))), premises.toSeq)
      else if (pivots.forall(_.tail.isEmpty))
        proof.ValidProofTactic(Seq(SC.LeftOr(bot, Range(-1, -premises.length - 1, -1), pivots.map(_.head))), premises.toSeq)
      else
        // some extraneous formulae
        proof.InvalidProofTactic("Left-hand side of conclusion + disjuncts is not the same as the union of the left-hand sides of the premises + φ∨ψ.")
    }
  }

  /**
   * <pre>
   *  Γ |- φ, Δ    Σ, ψ |- Π
   * ------------------------
   *    Γ, Σ, φ→ψ |- Δ, Π
   * </pre>
   */
  object LeftImplies extends ProofTactic {
    def apply(using proof: Library#Proof)(phi: Formula, psi: Formula)(prem1: proof.Fact, prem2: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.LeftImplies(bot, -1, -2, phi, psi)), Seq(prem1, prem2))
    def apply(using proof: Library#Proof)(prem1: proof.Fact, prem2: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      val leftSequent = proof.getSequent(prem1)
      val rightSequent = proof.getSequent(prem2)
      val pivotLeft = leftSequent.right.diff(bot.right)
      lazy val pivotRight = rightSequent.left.diff(bot.left)

      if (pivotLeft.isEmpty)
        proof.ValidProofTactic(Seq(SC.Weakening(bot, -1)), Seq(prem1, prem2))
      else if (pivotRight.isEmpty)
        proof.ValidProofTactic(Seq(SC.Weakening(bot, -2)), Seq(prem1, prem2))
      else if (pivotLeft.tail.isEmpty && pivotRight.tail.isEmpty)
        proof.ValidProofTactic(Seq(SC.LeftImplies(bot, -1, -2, pivotLeft.head, pivotRight.head)), Seq(prem1, prem2))
      else
        proof.InvalidProofTactic("Could not infer an implication as a pivot from the premises and conclusion, possible extraneous formulae in premises.")
    }
  }

  /**
   * <pre>
   *  Γ, φ→ψ |- Δ               Γ, φ→ψ, ψ→φ |- Δ
   * --------------    or     --------------------
   *  Γ, φ↔ψ |- Δ                 Γ, φ↔ψ |- Δ
   * </pre>
   */
  object LeftIff extends ProofTactic with ParameterlessAndThen {
    def apply(using proof: Library#Proof)(phi: Formula, psi: Formula)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.LeftIff(bot, -1, phi, psi)), Seq(premise))

    def apply(using proof: Library#Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premise)
      val pivot = premiseSequent.left.diff(bot.left)

      if (pivot.isEmpty)
        proof.ValidProofTactic(Seq(SC.Weakening(bot, -1)), Seq(premise))
      else
        pivot.head match {
          case ConnectorFormula(Implies, Seq(phi, psi)) => proof.ValidProofTactic(Seq(SC.LeftIff(bot, -1, phi, psi)), Seq(premise))
          case _ => proof.InvalidProofTactic("Could not infer a pivot implication from premise.")
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
  object LeftNot extends ProofTactic with ParameterlessAndThen {
    def apply(using proof: Library#Proof)(phi: Formula)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.LeftNot(bot, -1, phi)), Seq(premise))
    def apply(using proof: Library#Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premise)
      val pivot = premiseSequent.right.diff(bot.right)

      if (pivot.isEmpty)
        proof.ValidProofTactic(Seq(SC.Weakening(bot, -1)), Seq(premise))
      else if (pivot.tail.isEmpty)
        proof.ValidProofTactic(Seq(SC.LeftNot(bot, -1, pivot.head)), Seq(premise))
      else
        proof.InvalidProofTactic("Right-hand side of conclusion + φ must be the same as right-hand side of premise.")

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
  object LeftForall extends ProofTactic {
    def apply(using proof: Library#Proof)(phi: Formula, x: VariableLabel, t: Term)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.LeftForall(bot, -1, phi, x, t)), Seq(premise))

    def apply(using proof: Library#Proof)(t: Term)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premise)
      val pivot = bot.left.diff(premiseSequent.left)
      lazy val instantiatedPivot = premiseSequent.left.diff(bot.left)

      if (pivot.nonEmpty)
        if (pivot.tail.isEmpty)
          pivot.head match {
            case BinderFormula(Forall, x, phi) => proof.ValidProofTactic(Seq(SC.LeftForall(bot, -1, phi, x, t)), Seq(premise))
            case _ => proof.InvalidProofTactic("Could not infer a universally quantified pivot from premise and conclusion.")
          }
        else
          proof.InvalidProofTactic("Left-hand side of conclusion + φ[t/x] must be the same as left-hand side of premise + ∀x. φ.")
      else if (instantiatedPivot.isEmpty) proof.ValidProofTactic(Seq(SC.Weakening(bot, -1)), Seq(premise))
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
          case Some(BinderFormula(Forall, x, phi)) => proof.ValidProofTactic(Seq(SC.LeftForall(bot, -1, phi, x, t)), Seq(premise))
          case _ => proof.InvalidProofTactic("Could not infer a universally quantified pivot from premise and conclusion.")
        }
      } else proof.InvalidProofTactic("Left-hand side of conclusion + φ[t/x] must be the same as left-hand side of premise + ∀x. φ.")
    }
  }

  /**
   * <pre>
   *    Γ, φ |- Δ
   * ------------------- if x is not free in the resulting sequent
   *  Γ, ∃x φ|- Δ
   *
   * </pre>
   */
  object LeftExists extends ProofTactic with ParameterlessAndThen {
    def apply(using proof: Library#Proof)(phi: Formula, x: VariableLabel)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.LeftExists(bot, -1, phi, x)), Seq(premise))

    def apply(using proof: Library#Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premise)
      val pivot = bot.left.diff(premiseSequent.left)
      lazy val instantiatedPivot = premiseSequent.left.diff(bot.left)
      if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty) proof.ValidProofTactic(Seq(SC.Rewrite(bot, -1)), Seq(premise))
        else if (instantiatedPivot.tail.isEmpty) {
          val in: Formula = instantiatedPivot.head
          val quantifiedPhi: Option[Formula] = bot.left.find(f =>
            f match {
              case BinderFormula(Exists, _, g) => isSame(g, in)
              case _ => false
            }
          )

          quantifiedPhi match {
            case Some(BinderFormula(Exists, x, phi)) => proof.ValidProofTactic(Seq(SC.LeftExists(bot, -1, phi, x)), Seq(premise))
            case _ => proof.InvalidProofTactic("Could not infer an existensially quantified pivot from premise and conclusion.")
          }
        } else proof.InvalidProofTactic("Left-hand side of conclusion + φ must be the same as left-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case BinderFormula(Exists, x, phi) => proof.ValidProofTactic(Seq(SC.LeftExists(bot, -1, phi, x)), Seq(premise))
          case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
        }
      else
        proof.InvalidProofTactic("Left-hand side of conclusion + φ must be the same as left-hand side of premise + ∃x. φ.")
    }
  }

  /**
   * <pre>
   *  Γ, ∃y.∀x. (x=y) ↔ φ |-  Δ
   * ---------------------------- if y is not free in φ
   *      Γ, ∃!x. φ |- Δ
   * </pre>
   */
  object LeftExistsOne extends ProofTactic with ParameterlessAndThen {
    def apply(using proof: Library#Proof)(phi: Formula, x: VariableLabel)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.LeftExistsOne(bot, -1, phi, x)), Seq(premise))

    def apply(using proof: Library#Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premise)
      val pivot = bot.left.diff(premiseSequent.left)
      lazy val instantiatedPivot = premiseSequent.left.diff(bot.left)

      if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty)
          proof.ValidProofTactic(Seq(SC.Rewrite(bot, -1)), Seq(premise))
        else if (instantiatedPivot.tail.isEmpty) {
          instantiatedPivot.head match {
            // ∃_. ∀x. _ ↔ φ == extract ==> x, phi
            case BinderFormula(Exists, _, BinderFormula(Forall, x, ConnectorFormula(Iff, Seq(_, phi)))) =>
              proof.ValidProofTactic(Seq(SC.LeftExistsOne(bot, -1, phi, x)), Seq(premise))
            case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
          }
        } else
          proof.InvalidProofTactic("Left-hand side of conclusion + φ must be the same as left-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case BinderFormula(ExistsOne, x, phi) => proof.ValidProofTactic(Seq(SC.LeftExistsOne(bot, -1, phi, x)), Seq(premise))
          case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
        }
      else
        proof.InvalidProofTactic("Left-hand side of conclusion + φ must be the same as left-hand side of premise + ∃x. φ.")
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
  object RightAnd extends ProofTactic {
    def apply(using proof: Library#Proof)(cunjuncts: Seq[Formula])(premises: Seq[proof.Fact])(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.RightAnd(bot, Range(-1, -premises.length - 1, -1), cunjuncts)), premises)

    def apply(using proof: Library#Proof)(premises: Seq[proof.Fact])(bot: Sequent): proof.ProofTacticJudgement = {
      val premiseSequents = premises.map(proof.getSequent)
      val pivots = premiseSequents.map(_.right.diff(bot.right))

      if (pivots.exists(_.isEmpty))
        proof.ValidProofTactic(Seq(SC.Weakening(bot, pivots.indexWhere(_.isEmpty))), premises)
      else if (pivots.forall(_.tail.isEmpty))
        proof.ValidProofTactic(Seq(SC.RightAnd(bot, Range(-1, -premises.length - 1, -1), pivots.map(_.head))), premises)
      else
        // some extraneous formulae
        proof.InvalidProofTactic("Right-hand side of conclusion + φ + ψ is not the same as the union of the right-hand sides of the premises +φ∧ψ.")
    }
  }

  /**
   * <pre>
   *   Γ |- φ, Δ               Γ |- φ, ψ, Δ
   * --------------    or    ---------------
   *  Γ |- φ∨ψ, Δ              Γ |- φ∨ψ, Δ
   * </pre>
   */
  object RightOr extends ProofTactic with ParameterlessAndThen {
    def apply(using proof: Library#Proof)(phi: Formula, psi: Formula)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.RightOr(bot, -1, phi, psi)), Seq(premise))

    def apply(using proof: Library#Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premise)
      val pivot = bot.right.diff(premiseSequent.right)

      if (pivot.nonEmpty && pivot.tail.isEmpty)
        pivot.head match {
          case ConnectorFormula(Or, Seq(phi, psi)) =>
            if (premiseSequent.left.contains(phi))
              proof.ValidProofTactic(Seq(SC.RightOr(bot, -1, phi, psi)), Seq(premise))
            else
              proof.ValidProofTactic(Seq(SC.RightOr(bot, -1, psi, phi)), Seq(premise))
          case _ => proof.InvalidProofTactic("Could not infer a disjunction as pivot from premise and conclusion.")
        }
      else
      // try a rewrite, if it works, go ahead with it, otherwise malformed
      if (SC.isSameSequent(premiseSequent, bot))
        proof.ValidProofTactic(Seq(SC.Rewrite(bot, -1)), Seq(premise))
      else
        proof.InvalidProofTactic("Right-hand side of conclusion + φ∧ψ must be same as right-hand side of premise + either φ, ψ or both.")
    }
  }

  /**
   * <pre>
   *  Γ, φ |- ψ, Δ
   * --------------
   *  Γ |- φ→ψ, Δ
   * </pre>
   */
  object RightImplies extends ProofTactic with ParameterlessAndThen {
    def apply(using proof: Library#Proof)(phi: Formula, psi: Formula)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.RightImplies(bot, -1, phi, psi)), Seq(premise))

    def apply(using proof: Library#Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premise)
      val leftPivot = premiseSequent.left.diff(bot.left)
      val rightPivot = premiseSequent.right.diff(bot.right)

      if (
        leftPivot.nonEmpty && leftPivot.tail.isEmpty &&
        rightPivot.nonEmpty && rightPivot.tail.isEmpty
      )
        proof.ValidProofTactic(Seq(SC.RightImplies(bot, -1, leftPivot.head, rightPivot.head)), Seq(premise))
      else
        proof.InvalidProofTactic("Right-hand side of conclusion + ψ must be same as right-hand side of premise + φ→ψ.")
    }
  }

  /**
   * <pre>
   *  Γ |- φ→ψ, Δ    Σ |- ψ→φ, Π
   * ----------------------------
   *      Γ, Σ |- φ↔ψ, Π, Δ
   * </pre>
   */
  object RightIff extends ProofTactic {
    def apply(using proof: Library#Proof)(phi: Formula, psi: Formula)(prem1: proof.Fact, prem2: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.RightIff(bot, -1, -2, phi, psi)), Seq(prem1, prem2))

    def apply(using proof: Library#Proof)(prem1: proof.Fact, prem2: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(prem1)
      val pivot = premiseSequent.right.diff(bot.right)

      if (pivot.isEmpty)
        proof.ValidProofTactic(Seq(SC.Weakening(bot, -1)), Seq(prem1))
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case ConnectorFormula(Implies, Seq(phi, psi)) => proof.ValidProofTactic(Seq(SC.RightIff(bot, -1, -2, phi, psi)), Seq(prem1, prem2))
          case _ => proof.InvalidProofTactic("Could not infer an implication as pivot from premise and conclusion.")
        }
      else
        proof.InvalidProofTactic("Right-hand side of conclusion + φ→ψ + ψ→φ is not the same as the union of the right-hand sides of the premises φ↔ψ.")
    }
  }

  /**
   * <pre>
   *  Γ, φ |- Δ
   * --------------
   *   Γ |- ¬φ, Δ
   * </pre>
   */
  object RightNot extends ProofTactic with ParameterlessAndThen {
    def apply(using proof: Library#Proof)(phi: Formula)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.RightNot(bot, -1, phi)), Seq(premise))

    def apply(using proof: Library#Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premise)
      val pivot = premiseSequent.left.diff(bot.left)

      if (pivot.isEmpty)
        proof.ValidProofTactic(Seq(SC.Weakening(bot, -1)), Seq(premise))
      else if (pivot.tail.isEmpty)
        proof.ValidProofTactic(Seq(SC.RightNot(bot, -1, pivot.head)), Seq(premise))
      else
        proof.InvalidProofTactic("Left-hand side of conclusion + φ must be the same as left-hand side of premise.")

    }
  }

  /**
   * <pre>
   *    Γ |- φ, Δ
   * ------------------- if x is not free in the resulting sequent
   *  Γ |- ∀x. φ, Δ
   * </pre>
   */
  object RightForall extends ProofTactic with ParameterlessAndThen {
    def apply(using proof: Library#Proof)(phi: Formula, x: VariableLabel)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.RightForall(bot, -1, phi, x)), Seq(premise))

    def apply(using proof: Library#Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premise)
      val pivot = bot.right.diff(premiseSequent.right)
      lazy val instantiatedPivot = premiseSequent.right.diff(bot.right)

      if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty) proof.ValidProofTactic(Seq(SC.Rewrite(bot, -1)), Seq(premise))
        else if (instantiatedPivot.tail.isEmpty) {
          val in: Formula = instantiatedPivot.head
          val quantifiedPhi: Option[Formula] = bot.right.find(f =>
            f match {
              case BinderFormula(Forall, _, g) => isSame(g, in)
              case _ => false
            }
          )

          quantifiedPhi match {
            case Some(BinderFormula(Forall, x, phi)) => proof.ValidProofTactic(Seq(SC.RightForall(bot, -1, phi, x)), Seq(premise))
            case _ => proof.InvalidProofTactic("Could not infer a universally quantified pivot from premise and conclusion.")
          }
        } else proof.InvalidProofTactic("Right-hand side of conclusion + φ must be the same as right-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case BinderFormula(Forall, x, phi) => proof.ValidProofTactic(Seq(SC.RightForall(bot, -1, phi, x)), Seq(premise))
          case _ => proof.InvalidProofTactic("Could not infer a universally quantified pivot from premise and conclusion.")
        }
      else
        proof.InvalidProofTactic("Right-hand side of conclusion + φ must be the same as right-hand side of premise + ∃x. φ.")
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
  object RightExists extends ProofTactic {
    def apply(using proof: Library#Proof)(phi: Formula, x: VariableLabel, t: Term)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.RightExists(bot, -1, phi, x, t)), Seq(premise))

    def apply(using proof: Library#Proof)(t: Term)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premise)
      val pivot = bot.right.diff(premiseSequent.right)
      lazy val instantiatedPivot = premiseSequent.right.diff(bot.right)

      if (pivot.nonEmpty)
        if (pivot.tail.isEmpty)
          pivot.head match {
            case BinderFormula(Exists, x, phi) => proof.ValidProofTactic(Seq(SC.RightExists(bot, -1, phi, x, t)), Seq(premise))
            case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
          }
        else
          proof.InvalidProofTactic("Right-hand side of conclusion + φ[t/x] must be the same as right-hand side of premise + ∀x. φ.")
      else if (instantiatedPivot.isEmpty) proof.ValidProofTactic(Seq(SC.Weakening(bot, -1)), Seq(premise))
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
          case Some(BinderFormula(Exists, x, phi)) => proof.ValidProofTactic(Seq(SC.RightExists(bot, -1, phi, x, t)), Seq(premise))
          case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
        }
      } else proof.InvalidProofTactic("Right-hand side of conclusion + φ[t/x] must be the same as right-hand side of premise + ∀x. φ.")
    }
  }

  /**
   * <pre>
   *  Γ |- ∃y.∀x. (x=y) ↔ φ, Δ
   * ---------------------------- if y is not free in φ
   *      Γ|- ∃!x. φ,  Δ
   * </pre>
   */
  object RightExistsOne extends ProofTactic with ParameterlessAndThen {
    def apply(using proof: Library#Proof)(phi: Formula, x: VariableLabel)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.RightExistsOne(bot, -1, phi, x)), Seq(premise))

    def apply(using proof: Library#Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premise)
      val pivot = bot.right.diff(premiseSequent.right)
      lazy val instantiatedPivot = premiseSequent.right.diff(bot.right)

      if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty)
          proof.ValidProofTactic(Seq(SC.Rewrite(bot, -1)), Seq(premise))
        else if (instantiatedPivot.tail.isEmpty) {
          instantiatedPivot.head match {
            // ∃_. ∀x. _ ↔ φ == extract ==> x, phi
            case BinderFormula(Exists, _, BinderFormula(Forall, x, ConnectorFormula(Iff, Seq(_, phi)))) => proof.ValidProofTactic(Seq(SC.RightExistsOne(bot, -1, phi, x)), Seq(premise))
            case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
          }
        } else
          proof.InvalidProofTactic("Right-hand side of conclusion + φ must be the same as right-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case BinderFormula(ExistsOne, x, phi) => proof.ValidProofTactic(Seq(SC.RightExistsOne(bot, -1, phi, x)), Seq(premise))
          case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
        }
      else
        proof.InvalidProofTactic("Right-hand side of conclusion + φ must be the same as right-hand side of premise + ∃x. φ.")
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
  object Weakening extends ProofTactic with ParameterlessAndThen {
    def apply(using proof: Library#Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.Weakening(bot, -1)), Seq(premise))
  }

  // Equality Rules
  /**
   * <pre>
   *  Γ, s=s |- Δ
   * --------------
   *     Γ |- Δ
   * </pre>
   */
  object LeftRefl extends ProofTactic with ParameterlessAndThen {
    def apply(using proof: Library#Proof)(fa: Formula)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.LeftRefl(bot, -1, fa)), Seq(premise))

    def apply(using proof: Library#Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.Rewrite(bot, -1)), Seq(premise))
  }

  /**
   * <pre>
   *
   * --------------
   *     |- s=s
   * </pre>
   */
  object RightRefl extends ProofTactic with ParameterlessAndThen {
    def apply(using proof: Library#Proof)(fa: Formula)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.RightRefl(bot, fa)), Seq(premise))

    def apply(using proof: Library#Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.RewriteTrue(bot)), Seq(premise))
  }

  /**
   * <pre>
   *    Γ, φ(s1,...,sn) |- Δ
   * ---------------------
   *  Γ, s1=-1, ..., sn=tn, φ(-1,...tn) |- Δ
   * </pre>
   */
  object LeftSubstEq extends ProofTactic {
    def apply(using proof: Library#Proof)(equals: List[(Term, Term)], lambdaPhi: LambdaTermFormula)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.LeftSubstEq(bot, -1, equals, lambdaPhi)), Seq(premise))
  }

  /**
   * <pre>
   *    Γ |- φ(s1,...,sn), Δ
   * ---------------------
   *  Γ, s1=-1, ..., sn=tn |- φ(-1,...tn), Δ
   * </pre>
   */
  object RightSubstEq extends ProofTactic {
    def apply(using proof: Library#Proof)(equals: List[(Term, Term)], lambdaPhi: LambdaTermFormula)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.RightSubstEq(bot, -1, equals, lambdaPhi)), Seq(premise))
  }

  /**
   * <pre>
   *    Γ, φ(a1,...an) |- Δ
   * ---------------------
   *  Γ, a1↔b1, ..., an↔bn, φ(b1,...bn) |- Δ
   * </pre>
   */
  object LeftSubstIff extends ProofTactic {
    def apply(using proof: Library#Proof)(equals: List[(Formula, Formula)], lambdaPhi: LambdaFormulaFormula)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.LeftSubstIff(bot, -1, equals, lambdaPhi)), Seq(premise))
  }

  /**
   * <pre>
   *    Γ |- φ(a1,...an), Δ
   * ---------------------
   *  Γ, a1↔b1, ..., an↔bn |- φ(b1,...bn), Δ
   * </pre>
   */
  object RightSubstIff extends ProofTactic {
    def apply(using proof: Library#Proof)(equals: List[(Formula, Formula)], lambdaPhi: LambdaFormulaFormula)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.RightSubstIff(bot, -1, equals, lambdaPhi)), Seq(premise))
  }

  /**
   * <pre>
   *           Γ |- Δ
   * --------------------------
   *  Γ[r(a)/?f] |- Δ[r(a)/?f]
   * </pre>
   */
  object InstFunSchema extends ProofTactic {
    def apply(using proof: Library#Proof)(insts: Map[SchematicTermLabel, LambdaTermTerm])(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.InstFunSchema(bot, -1, insts)), Seq(premise))
  }

  /**
   * <pre>
   *           Γ |- Δ
   * --------------------------
   *  Γ[ψ(a)/?p] |- Δ[ψ(a)/?p]
   * </pre>
   */
  object InstPredSchema extends ProofTactic {
    def apply(using proof: Library#Proof)(insts: Map[SchematicVarOrPredLabel, LambdaTermFormula])(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.InstPredSchema(bot, -1, insts)), Seq(premise))
  }

  class SUBPROOF(using val proof: Library#Proof, om: OutputManager)(statement: Sequent | String, val line: sourcecode.Line, val file: sourcecode.File)(computeProof: proof.InnerProof ?=> Unit)
      extends ProofTactic {
    val bot: Sequent = statement match {
      case s: Sequent => s
      case s: String => lisa.utils.Parser.parseSequent(s)
    }

    val iProof: proof.InnerProof = new proof.InnerProof(bot)
    val scproof: SCProof = {
      try {
        computeProof(using iProof)
      } catch {
        case e: NotImplementedError =>
          om.lisaThrow(new UserLisaException.UnimplementedProof(proof.owningTheorem))
        case e: UserLisaException =>
          om.lisaThrow(e)
      }
      if (proof.length == 0)
        om.lisaThrow(new UserLisaException.UnimplementedProof(proof.owningTheorem))
      iProof.toSCProof
    }
    val premises: Seq[proof.Fact] = iProof.getImports.map(of => of._1)
    def judgement: proof.ValidProofTactic = proof.ValidProofTactic(scproof.steps, premises)
  }

}
