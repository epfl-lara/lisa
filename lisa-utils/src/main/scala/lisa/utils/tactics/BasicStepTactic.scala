package lisa.utils.tactics

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.SCProofStep
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.kernel.proof.SequentCalculus as SC
import lisa.utils.Helpers.*
import lisa.utils.{Library, LisaException, OutputManager, UserLisaException}
import lisa.utils.tactics.ProofTacticLib.{*, given}

object BasicStepTactic {

  object Hypothesis extends ProofTactic {
    def apply()(using proof: Library#Proof)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.Hypothesis(bot, bot.left.intersect(bot.right).head)), Seq())
  }

  
  final class Rewrite extends ProofTactic {
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

    def apply(using proof: Library#Proof)(prem1: proof.Fact, prem2: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = CutWithoutFormula(prem1: proof.Fact, prem2: proof.Fact)(bot: Sequent)
  }

  object CutWithoutFormula extends ProofTactic {
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
  object LeftAnd extends ProofTactic {
    def apply(using proof: Library#Proof)(phi: Formula, psi: Formula)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.LeftAnd(bot, -1, phi, psi)), Seq(premise))
    def apply(using proof: Library#Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
      LeftAndWithoutFormula.apply(premise)(bot)
  }

  object LeftAndWithoutFormula extends ProofTactic {
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
/*

  /**
   * <pre>
   *  Γ, φ |- Δ    Σ, ψ |- Π    ...
   * --------------------------------
   *    Γ, Σ, φ∨ψ∨... |- Δ, Π
   * </pre>
   */
  final class LeftOr(disjuncts: Seq[Formula])(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(-1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement = {
      SC.LeftOr(bot, Range(-1, -premises.length-1, -1), disjuncts)
    }
  }
  final class LeftOrWithoutFormula(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(-1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement = {
      val premiseSequents = premises.map(proof.getSequent(_))
      val pivots = premiseSequents.map(_.left.diff(bot.left))

      if (pivots.exists(_.isEmpty))
        SC.Weakening(bot, pivots.indexWhere(_.isEmpty))
      else if (pivots.forall(_.tail.isEmpty))
        SC.LeftOr(bot, Range(-1, -premises.length-1, -1), pivots.map(_.head))
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
  final class LeftImplies(phi: Formula, psi: Formula)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(2) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement =
      SC.LeftImplies(bot, -1, -2, phi, psi)
  }

  final class LeftImpliesWithoutFormula(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(2) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement = {
      val leftSequent = proof.getSequent(premises(0))
      val rightSequent = proof.getSequent(premises(1))
      val pivotLeft = leftSequent.right.diff(bot.right)
      lazy val pivotRight = rightSequent.left.diff(bot.left)

      if (pivotLeft.isEmpty)
        SC.Weakening(bot, -1)
      else if (pivotRight.isEmpty)
        SC.Weakening(bot, -2)
      else if (pivotLeft.tail.isEmpty && pivotRight.tail.isEmpty)
        SC.LeftImplies(bot, -1, -2, pivotLeft.head, pivotRight.head)
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
  final class LeftIff(phi: Formula, psi: Formula)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement =
      SC.LeftIff(bot, -1, phi, psi)
  }

  final class LeftIffWithoutFormula()(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premises(0))
      val pivot = premiseSequent.left.diff(bot.left)

      if (pivot.isEmpty)
        SC.Weakening(bot, -1)
      else
        pivot.head match {
          case ConnectorFormula(Implies, Seq(phi, psi)) => SC.LeftIff(bot, -1, phi, psi)
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
  final class LeftNot(phi: Formula)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement =
      SC.LeftNot(bot, -1, phi)
  }

  final class LeftNotWithoutFormula(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premises(0))
      val pivot = premiseSequent.right.diff(bot.right)

      if (pivot.isEmpty)
        SC.Weakening(bot, -1)
      else if (pivot.tail.isEmpty)
        SC.LeftNot(bot, -1, pivot.head)
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
  final class LeftForall(phi: Formula, x: VariableLabel, t: Term)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement =
      SC.LeftForall(bot, -1, phi, x, t)
  }

  final class LeftForallWithoutFormula(t: Term)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premises(0))
      val pivot = bot.left.diff(premiseSequent.left)
      lazy val instantiatedPivot = premiseSequent.left.diff(bot.left)

      if (pivot.nonEmpty)
        if (pivot.tail.isEmpty)
          pivot.head match {
            case BinderFormula(Forall, x, phi) => SC.LeftForall(bot, -1, phi, x, t)
            case _ => proof.InvalidProofTactic("Could not infer a universally quantified pivot from premise and conclusion.")
          }
        else
          proof.InvalidProofTactic("Left-hand side of conclusion + φ[t/x] must be the same as left-hand side of premise + ∀x. φ.")
      else if (instantiatedPivot.isEmpty) SC.Weakening(bot, -1)
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
          case Some(BinderFormula(Forall, x, phi)) => SC.LeftForall(bot, -1, phi, x, t)
          case _ => proof.InvalidProofTactic("Could not infer a universally quantified pivot from premise and conclusion.")
        }
      } else proof.InvalidProofTactic("Left-hand side of conclusion + φ[t/x] must be the same as left-hand side of premise + ∀x. φ.")
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
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement =
      SC.LeftExists(bot, -1, phi, x)
  }

  final class LeftExistsWithoutFormula()(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premises(0))
      val pivot = bot.left.diff(premiseSequent.left)
      lazy val instantiatedPivot = premiseSequent.left.diff(bot.left)

      if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty) SC.Rewrite(bot, -1)
        else if (instantiatedPivot.tail.isEmpty) {
          val in: Formula = instantiatedPivot.head
          val quantifiedPhi: Option[Formula] = bot.left.find(f =>
            f match {
              case BinderFormula(Exists, _, g) => isSame(g, in)
              case _ => false
            }
          )

          quantifiedPhi match {
            case Some(BinderFormula(Exists, x, phi)) => SC.LeftExists(bot, -1, phi, x)
            case _ => proof.InvalidProofTactic("Could not infer an existensially quantified pivot from premise and conclusion.")
          }
        } else proof.InvalidProofTactic("Left-hand side of conclusion + φ must be the same as left-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case BinderFormula(Exists, x, phi) => SC.LeftExists(bot, -1, phi, x)
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
  final class LeftExistsOne(phi: Formula, x: VariableLabel)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement =
      SC.LeftExistsOne(bot, -1, phi, x)
  }

  final class LeftExistsOneWithoutFormula()(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premises(0))
      val pivot = bot.left.diff(premiseSequent.left)
      lazy val instantiatedPivot = premiseSequent.left.diff(bot.left)

      if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty)
          SC.Rewrite(bot, -1)
        else if (instantiatedPivot.tail.isEmpty) {
          instantiatedPivot.head match {
            // ∃_. ∀x. _ ↔ φ == extract ==> x, phi
            case BinderFormula(Exists, _, BinderFormula(Forall, x, ConnectorFormula(Iff, Seq(_, phi)))) => SC.LeftExistsOne(bot, -1, phi, x)
            case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
          }
        } else
          proof.InvalidProofTactic("Left-hand side of conclusion + φ must be the same as left-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case BinderFormula(ExistsOne, x, phi) => SC.LeftExistsOne(bot, -1, phi, x)
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
  final class RightAnd(cunjuncts: Seq[Formula])(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(-1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement =
      SC.RightAnd(bot, Range(-1, -premises.length-1, -1), cunjuncts)
  }
  final class RightAndWithoutFormula(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(-1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement = {
      val premiseSequents = premises.map(proof.getSequent(_))
      val pivots = premiseSequents.map(_.right.diff(bot.right))

      if (pivots.exists(_.isEmpty))
        SC.Weakening(bot, pivots.indexWhere(_.isEmpty))
      else if (pivots.forall(_.tail.isEmpty))
        SC.RightAnd(bot, Range(-1, -premises.length-1, -1), pivots.map(_.head))
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
  final class RightOr(phi: Formula, psi: Formula)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement =
      SC.RightOr(bot, -1, phi, psi)
  }

  final class RightOrWithoutFormula()(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premises(0))
      val pivot = bot.right.diff(premiseSequent.right)

      if (!pivot.isEmpty && pivot.tail.isEmpty)
        pivot.head match {
          case ConnectorFormula(Or, Seq(phi, psi)) =>
            if (premiseSequent.left.contains(phi))
              SC.RightOr(bot, -1, phi, psi)
            else
              SC.RightOr(bot, -1, psi, phi)
          case _ => proof.InvalidProofTactic("Could not infer a disjunction as pivot from premise and conclusion.")
        }
      else
      // try a rewrite, if it works, go ahead with it, otherwise malformed
        if (SC.isSameSequent(premiseSequent, bot))
          SC.Rewrite(bot, -1)
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
  final class RightImplies(phi: Formula, psi: Formula)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement =
      SC.RightImplies(bot, -1, phi, psi)
  }

  final class RightImpliesWithoutFormula()(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premises(0))
      val leftPivot = premiseSequent.left.diff(bot.left)
      val rightPivot = premiseSequent.right.diff(bot.right)

      if (
        !leftPivot.isEmpty && leftPivot.tail.isEmpty &&
            !rightPivot.isEmpty && rightPivot.tail.isEmpty
      )
        SC.RightImplies(bot, -1, leftPivot.head, rightPivot.head)
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
  final class RightIff(phi: Formula, psi: Formula)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(2) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement =
      SC.RightIff(bot, -1, -2, phi, psi)
  }

  final class RightIffWithoutFormula()(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(2) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premises(0))
      val pivot = premiseSequent.right.diff(bot.right)

      if (pivot.isEmpty)
        SC.Weakening(bot, -1)
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case ConnectorFormula(Implies, Seq(phi, psi)) => SC.RightIff(bot, -1, -2, phi, psi)
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
  final class RightNot(phi: Formula)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement =
      SC.RightNot(bot, -1, phi)
  }

  final class RightNotWithoutFormula()(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premises(0))
      val pivot = premiseSequent.left.diff(bot.left)

      if (pivot.isEmpty)
        SC.Weakening(bot, -1)
      else if (pivot.tail.isEmpty)
        SC.RightNot(bot, -1, pivot.head)
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
  final class RightForall(phi: Formula, x: VariableLabel)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement =
      SC.RightForall(bot, -1, phi, x)
  }

  final class RightForallWithoutFormula()(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premises(0))
      val pivot = bot.right.diff(premiseSequent.right)
      lazy val instantiatedPivot = premiseSequent.right.diff(bot.right)

      if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty) SC.Rewrite(bot, -1)
        else if (instantiatedPivot.tail.isEmpty) {
          val in: Formula = instantiatedPivot.head
          val quantifiedPhi: Option[Formula] = bot.right.find(f =>
            f match {
              case BinderFormula(Forall, _, g) => isSame(g, in)
              case _ => false
            }
          )

          quantifiedPhi match {
            case Some(BinderFormula(Forall, x, phi)) => SC.RightForall(bot, -1, phi, x)
            case _ => proof.InvalidProofTactic("Could not infer a universally quantified pivot from premise and conclusion.")
          }
        } else proof.InvalidProofTactic("Right-hand side of conclusion + φ must be the same as right-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case BinderFormula(Forall, x, phi) => SC.RightForall(bot, -1, phi, x)
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
  final class RightExists(phi: Formula, x: VariableLabel, t: Term)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement =
      SC.RightExists(bot, -1, phi, x, t)
  }

  final class RightExistsWithoutFormula(t: Term)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premises(0))
      val pivot = bot.right.diff(premiseSequent.right)
      lazy val instantiatedPivot = premiseSequent.right.diff(bot.right)

      if (!pivot.isEmpty)
        if (pivot.tail.isEmpty)
          pivot.head match {
            case BinderFormula(Exists, x, phi) => SC.RightExists(bot, -1, phi, x, t)
            case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
          }
        else
          proof.InvalidProofTactic("Right-hand side of conclusion + φ[t/x] must be the same as right-hand side of premise + ∀x. φ.")
      else if (instantiatedPivot.isEmpty) SC.Weakening(bot, -1)
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
          case Some(BinderFormula(Exists, x, phi)) => SC.RightExists(bot, -1, phi, x, t)
          case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
        }
      } else
        proof.InvalidProofTactic("Right-hand side of conclusion + φ[t/x] must be the same as right-hand side of premise + ∀x. φ.")
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
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement =
      SC.RightExistsOne(bot, -1, phi, x)
  }

  final class RightExistsOneWithoutFormula(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premises(0))
      val pivot = bot.right.diff(premiseSequent.right)
      lazy val instantiatedPivot = premiseSequent.right.diff(bot.right)

      if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty)
          SC.Rewrite(bot, -1)
        else if (instantiatedPivot.tail.isEmpty) {
          instantiatedPivot.head match {
            // ∃_. ∀x. _ ↔ φ == extract ==> x, phi
            case BinderFormula(Exists, _, BinderFormula(Forall, x, ConnectorFormula(Iff, Seq(_, phi)))) => SC.RightExistsOne(bot, -1, phi, x)
            case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
          }
        } else
          proof.InvalidProofTactic("Right-hand side of conclusion + φ must be the same as right-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case BinderFormula(ExistsOne, x, phi) => SC.RightExistsOne(bot, -1, phi, x)
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
  final class Weakening(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement =
      SC.Weakening(bot, -1)
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
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement =
      SC.LeftRefl(bot, -1, fa)
  }

  final class LeftReflWithoutFormula(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement =
      SC.Rewrite(bot, -1)
  }


  /**
   * <pre>
   *
   * --------------
   *     |- s=s
   * </pre>
   */
  final class RightRefl(using val proof: Library#Proof)(fa: Formula) extends ProofTacticWithoutBotNorPrem(0) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement =
      SC.RightRefl(bot, fa)
  }

  final class RightReflWithoutFormula(using val proof: Library#Proof)() extends ProofTacticWithoutBotNorPrem(0) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement =
      SC.RewriteTrue(bot)
  }


  /**
   * <pre>
   *    Γ, φ(s1,...,sn) |- Δ
   * ---------------------
   *  Γ, s1=-1, ..., sn=tn, φ(-1,...tn) |- Δ
   * </pre>
   */
  final class LeftSubstEq(equals: List[(Term, Term)], lambdaPhi: LambdaTermFormula)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement =
      SC.LeftSubstEq(bot, -1, equals, lambdaPhi)
  }

  /**
   * <pre>
   *    Γ |- φ(s1,...,sn), Δ
   * ---------------------
   *  Γ, s1=-1, ..., sn=tn |- φ(-1,...tn), Δ
   * </pre>
   */
  final class RightSubstEq(equals: List[(Term, Term)], lambdaPhi: LambdaTermFormula)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement =
      SC.RightSubstEq(bot, -1, equals, lambdaPhi)
  }

  /**
   * <pre>
   *    Γ, φ(a1,...an) |- Δ
   * ---------------------
   *  Γ, a1↔b1, ..., an↔bn, φ(b1,...bn) |- Δ
   * </pre>
   */
  final class LeftSubstIff(equals: List[(Formula, Formula)], lambdaPhi: LambdaFormulaFormula)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement =
      SC.LeftSubstIff(bot, -1, equals, lambdaPhi)
  }

  /**
   * <pre>
   *    Γ |- φ(a1,...an), Δ
   * ---------------------
   *  Γ, a1↔b1, ..., an↔bn |- φ(b1,...bn), Δ
   * </pre>
   */
  final class RightSubstIff(equals: List[(Formula, Formula)], lambdaPhi: LambdaFormulaFormula)(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement =
      SC.RightSubstIff(bot, -1, equals, lambdaPhi)
  }

  /**
   * <pre>
   *           Γ |- Δ
   * --------------------------
   *  Γ[r(a)/?f] |- Δ[r(a)/?f]
   * </pre>
   */
  final class InstFunSchema(insts: Map[SchematicTermLabel, LambdaTermTerm])(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement =
      SC.InstFunSchema(bot, -1, insts)
  }

  /**
   * <pre>
   *           Γ |- Δ
   * --------------------------
   *  Γ[ψ(a)/?p] |- Δ[ψ(a)/?p]
   * </pre>
   */
  final class InstPredSchema(insts: Map[SchematicVarOrPredLabel, LambdaTermFormula])(using val proof: Library#Proof) extends ProofTacticWithoutBotNorPrem(1) {
    def asSCProof(bot: Sequent, premises: Seq[proof.Fact]): proof.ProofTacticJudgement =
      SC.InstPredSchema(bot, -1, insts)
  }
*/


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
      } catch {/*
        case e: NotImplementedError => om.lisaThrow(new UserLisaException.UnimplementedProof(proof.owningTheorem))*/
        case e: LisaException => om.lisaThrow(e)
      }
      if (proof.length == 0)
        om.lisaThrow(new UserLisaException.UnimplementedProof(proof.owningTheorem))
      iProof.toSCProof
    }
    val premises = iProof.getImports.map(of => of._1)
  }



}