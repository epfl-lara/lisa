package lisa.prooflib

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.SCProofStep
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.kernel.proof.SequentCalculus.isSameSequent
import lisa.kernel.proof.SequentCalculus as SC
import lisa.prooflib.ProofTacticLib.{_, given}
import lisa.prooflib.SimpleDeducedSteps.Restate
import lisa.prooflib.*
import lisa.utils.KernelHelpers.*
import lisa.utils.UserLisaException
import lisa.utils.parsing.FOLPrinter
import lisa.utils.unification.UnificationUtils

object BasicStepTactic {

  def unwrapTactic(using lib: Library, proof: lib.Proof)(using tactic: ProofTactic)(judgement: proof.ProofTacticJudgement)(message: String): proof.ProofTacticJudgement = {
    judgement match {
      case j: proof.ValidProofTactic => proof.ValidProofTactic(j.scps, j.imports)
      case j: proof.InvalidProofTactic => proof.InvalidProofTactic(s"Internal tactic call failed! $message\n${j.message}")
    }
  }

  object Hypothesis extends ProofTactic with ProofSequentTactic {
    def apply(using lib: Library, proof: lib.Proof)(bot: Sequent): proof.ProofTacticJudgement = {
      val intersectedPivot = bot.left.intersect(bot.right)

      if (intersectedPivot.isEmpty)
        proof.InvalidProofTactic("A formula for input to Hypothesis could not be inferred from left and right side of the sequent.")
      else
        proof.ValidProofTactic(Seq(SC.Hypothesis(bot, intersectedPivot.head)), Seq())
    }
  }

  object Rewrite extends ProofTactic with ProofFactSequentTactic {
    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      if (!SC.isSameSequent(bot, proof.getSequent(premise)))
        proof.InvalidProofTactic("The premise and the conclusion are not trivially equivalent.")
      else
        proof.ValidProofTactic(Seq(SC.Restate(bot, -1)), Seq(premise))
    }
  }

  object RewriteTrue extends ProofTactic with ProofSequentTactic {
    def apply(using lib: Library, proof: lib.Proof)(bot: Sequent): proof.ProofTacticJudgement = {
      if (!SC.isSameSequent(bot, () |- PredicateFormula(top, Nil)))
        proof.InvalidProofTactic("The desired conclusion is not a trivial tautology.")
      else
        proof.ValidProofTactic(Seq(SC.RestateTrue(bot)), Seq())
    }
  }

  /**
   * <pre>
   *  Γ |- Δ, φ    φ, Σ |- Π
   * ------------------------
   *       Γ, Σ |- Δ, Π
   * </pre>
   */
  object Cut extends ProofTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: Formula)(prem1: proof.Fact, prem2: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val leftSequent = proof.getSequent(prem1)
      lazy val rightSequent = proof.getSequent(prem2)

      if (!contains(leftSequent.right, phi))
        proof.InvalidProofTactic("Right-hand side of first premise does not contain φ as claimed.")
      else if (!contains(rightSequent.left, phi))
        proof.InvalidProofTactic("Left-hand side of second premise does not contain φ as claimed.")
      else if (!isSameSet(bot.left + phi, leftSequent.left ++ rightSequent.left))
        proof.InvalidProofTactic("Left-hand side of conclusion + φ is not the union of the left-hand sides of the premises.")
      else if (!isSameSet(bot.right + phi, leftSequent.right ++ rightSequent.right))
        proof.InvalidProofTactic("Right-hand side of conclusion + φ is not the union of the right-hand sides of the premises.")
      else
        proof.ValidProofTactic(Seq(SC.Cut(bot, -1, -2, phi)), Seq(prem1, prem2))
    }

    def apply(using lib: Library, proof: lib.Proof)(prem1: proof.Fact, prem2: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val leftSequent = proof.getSequent(prem1)
      lazy val rightSequent = proof.getSequent(prem2)
      // cutSet: (rightSequent.left - bot.left) ++ (leftSequent.right - bot.right)
      // `xxx?` sequent operations are used to drop OL (and thus alpha-eq) formulas
      lazy val cutSet = (((rightSequent --<? bot).left |- ()) ++? ((leftSequent -->? bot).right |- ())).left
      lazy val intersectedCutSet = rightSequent.left intersect leftSequent.right

      if (!cutSet.isEmpty)
        if (cutSet.tail.isEmpty)
          Cut.withParameters(cutSet.head)(prem1, prem2)(bot)
        else
          proof.InvalidProofTactic("Inferred cut pivot is not a singleton set.")
      else if (!intersectedCutSet.isEmpty && intersectedCutSet.tail.isEmpty)
        // can still find a pivot
        Cut.withParameters(intersectedCutSet.head)(prem1, prem2)(bot)
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
  object LeftAnd extends ProofTactic with ProofFactSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: Formula, psi: Formula)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val phiAndPsi = ConnectorFormula(And, Seq(phi, psi))

      if (!isSameSet(bot.right, premiseSequent.right))
        proof.InvalidProofTactic("Right-hand side of the conclusion is not the same as the right-hand side of the premise.")
      else if (
        !isSameSet(bot.left + phi, premiseSequent.left + phiAndPsi) &&
        !isSameSet(bot.left + psi, premiseSequent.left + phiAndPsi) &&
        !isSameSet(bot.left + phi + psi, premiseSequent.left + phiAndPsi)
      )
        proof.InvalidProofTactic("Left-hand side of premise + φ∧ψ is not the same as left-hand side of conclusion + either φ, ψ or both.")
      else
        proof.ValidProofTactic(Seq(SC.LeftAnd(bot, -1, phi, psi)), Seq(premise))
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = bot.left.diff(premiseSequent.left)

      if (!pivot.isEmpty && pivot.tail.isEmpty)
        pivot.head match {
          case ConnectorFormula(And, Seq(phi, psi)) =>
            if (premiseSequent.left.contains(phi))
              LeftAnd.withParameters(phi, psi)(premise)(bot)
            else
              LeftAnd.withParameters(phi, psi)(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not infer a conjunction as pivot from premise and conclusion.")
        }
      else
      // try a rewrite, if it works, go ahead with it, otherwise malformed
      if (SC.isSameSequent(premiseSequent, bot))
        unwrapTactic(Rewrite(premise)(bot))("Attempted rewrite on trivial LeftAnd failed.")
      else
        proof.InvalidProofTactic("Left-hand side of premise + φ∧ψ is not the same as left-hand side of conclusion + either φ, ψ or both.")
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
    def withParameters(using lib: Library, proof: lib.Proof)(disjuncts: Formula*)(premises: proof.Fact*)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequents = premises.map(proof.getSequent(_))
      lazy val disjunction = ConnectorFormula(Or, disjuncts)

      if (premises.length == 0)
        proof.InvalidProofTactic(s"Premises expected, ${premises.length} received.")
      else if (premises.length != disjuncts.length)
        proof.InvalidProofTactic(s"Premises and disjuncts expected to be equal in number, but ${premises.length} premises and ${disjuncts.length} disjuncts received.")
      else if (!isSameSet(bot.right, premiseSequents.map(_.right).reduce(_ union _)))
        proof.InvalidProofTactic("Right-hand side of conclusion is not the union of the right-hand sides of the premises.")
      else if (!isSameSet(disjuncts.foldLeft(bot.left)(_ + _), premiseSequents.map(_.left).reduce(_ union _) + disjunction))
        proof.InvalidProofTactic("Left-hand side of conclusion + disjuncts is not the same as the union of the left-hand sides of the premises + φ∨ψ.")
      else
        proof.ValidProofTactic(Seq(SC.LeftOr(bot, Range(-1, -premises.length - 1, -1), disjuncts)), premises.toSeq)
    }

    def apply(using lib: Library, proof: lib.Proof)(premises: proof.Fact*)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequents = premises.map(proof.getSequent(_))
      lazy val pivots = premiseSequents.map(_.left.diff(bot.left))

      if (premises.length == 0) proof.InvalidProofTactic(s"Premises expected, ${premises.length} received.")
      else if (pivots.exists(_.isEmpty)) {
        val emptyIndex = pivots.indexWhere(_.isEmpty)
        if (isSubset(premiseSequents(emptyIndex).left, bot.left))
          unwrapTactic(Weakening(premises(emptyIndex))(bot))("Attempted weakening on trivial premise for LeftOr failed.")
        else
          proof.InvalidProofTactic("Right-hand side of conclusion is not a superset of the one of the premises.")
      } else if (pivots.forall(_.tail.isEmpty))
        LeftOr.withParameters(pivots.map(_.head): _*)(premises: _*)(bot)
      else
        // some extraneous formulae
        proof.InvalidProofTactic("Left-hand side of conclusion + disjuncts is not the same as the union of the left-hand sides of the premises + φ∨ψ.")
    }
  }

  /**
   * <pre>
   *  Γ |- φ, Δ    Σ, ψ |- Π
   * ------------------------
   *    Γ, Σ, φ⇒ψ |- Δ, Π
   * </pre>
   */
  object LeftImplies extends ProofTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: Formula, psi: Formula)(prem1: proof.Fact, prem2: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val leftSequent = proof.getSequent(prem1)
      lazy val rightSequent = proof.getSequent(prem2)
      lazy val implication = ConnectorFormula(Implies, Seq(phi, psi))

      if (!isSameSet(bot.right + phi, leftSequent.right union rightSequent.right))
        proof.InvalidProofTactic("Right-hand side of conclusion + φ is not the union of right-hand sides of premises.")
      else if (!isSameSet(bot.left + psi, leftSequent.left union rightSequent.left + implication))
        proof.InvalidProofTactic("Left-hand side of conclusion + ψ is not the union of left-hand sides of premises + φ⇒ψ.")
      else
        proof.ValidProofTactic(Seq(SC.LeftImplies(bot, -1, -2, phi, psi)), Seq(prem1, prem2))
    }
    def apply(using lib: Library, proof: lib.Proof)(prem1: proof.Fact, prem2: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val leftSequent = proof.getSequent(prem1)
      lazy val rightSequent = proof.getSequent(prem2)
      lazy val pivotLeft = leftSequent.right.diff(bot.right)
      lazy val pivotRight = rightSequent.left.diff(bot.left)

      if (pivotLeft.isEmpty)
        if (isSubset(leftSequent.left, bot.left))
          unwrapTactic(Weakening(prem1)(bot))("Attempted weakening on trivial left premise for LeftImplies failed.")
        else
          proof.InvalidProofTactic("Left-hand side of conclusion is not a superset of the first premises.")
      else if (pivotRight.isEmpty)
        if (isSubset(rightSequent.right, bot.right))
          unwrapTactic(Weakening(prem2)(bot))("Attempted weakening on trivial right premise for LeftImplies failed.")
        else
          proof.InvalidProofTactic("Right-hand side of conclusion is not a superset of the second premises.")
      else if (pivotLeft.tail.isEmpty && pivotRight.tail.isEmpty)
        LeftImplies.withParameters(pivotLeft.head, pivotRight.head)(prem1, prem2)(bot)
      else
        proof.InvalidProofTactic("Could not infer an implication as a pivot from the premises and conclusion, possible extraneous formulae in premises.")
    }
  }

  /**
   * <pre>
   *  Γ, φ⇒ψ |- Δ               Γ, φ⇒ψ, ψ⇒φ |- Δ
   * --------------    or     --------------------
   *  Γ, φ⇔ψ |- Δ                 Γ, φ⇔ψ |- Δ
   * </pre>
   */
  object LeftIff extends ProofTactic with ProofFactSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: Formula, psi: Formula)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val implication = ConnectorFormula(Iff, Seq(phi, psi))
      lazy val impLeft = ConnectorFormula(Implies, Seq(phi, psi))
      lazy val impRight = ConnectorFormula(Implies, Seq(psi, phi))

      if (!isSameSet(bot.right, premiseSequent.right))
        proof.InvalidProofTactic("Right-hand side of premise is not the same as right-hand side of conclusion.")
      else if (
        !isSameSet(bot.left + impLeft, premiseSequent.left + implication) &&
        !isSameSet(bot.left + impRight, premiseSequent.left + implication) &&
        !isSameSet(bot.left + impLeft + impRight, premiseSequent.left + implication)
      )
        proof.InvalidProofTactic("Left-hand side of premise + φ⇔ψ is not the same as left-hand side of conclusion + either φ⇒ψ, ψ⇒φ or both.")
      else
        proof.ValidProofTactic(Seq(SC.LeftIff(bot, -1, phi, psi)), Seq(premise))
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = premiseSequent.left.diff(bot.left)

      if (pivot.isEmpty)
        if (isSubset(premiseSequent.right, bot.right))
          unwrapTactic(Weakening(premise)(bot))("Attempted weakening on trivial premise for LeftIff failed.")
        else
          proof.InvalidProofTactic("Right-hand side of conclusion is not a superset of the premises.")
      else
        pivot.head match {
          case ConnectorFormula(Implies, Seq(phi, psi)) => LeftIff.withParameters(phi, psi)(premise)(bot)
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
  object LeftNot extends ProofTactic with ProofFactSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: Formula)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val negation = ConnectorFormula(Neg, Seq(phi))

      if (!isSameSet(bot.right + phi, premiseSequent.right))
        proof.InvalidProofTactic("Right-hand side of conclusion + φ is not the same as right-hand side of premise.")
      else if (!isSameSet(bot.left, premiseSequent.left + negation))
        proof.InvalidProofTactic("Left-hand side of conclusion is not the same as left-hand side of premise + ¬φ.")
      else
        proof.ValidProofTactic(Seq(SC.LeftNot(bot, -1, phi)), Seq(premise))
    }
    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = premiseSequent.right.diff(bot.right)

      if (pivot.isEmpty)
        if (isSubset(premiseSequent.left, bot.left))
          unwrapTactic(Weakening(premise)(bot))("Attempted weakening on trivial premise for LeftNot failed.")
        else
          proof.InvalidProofTactic("Left-hand side of conclusion is not a superset of the premises.")
      else if (!pivot.isEmpty && pivot.tail.isEmpty)
        LeftNot.withParameters(pivot.head)(premise)(bot)
      else
        proof.InvalidProofTactic("Right-hand side of conclusion + φ is not the same as right-hand side of premise.")

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
  object LeftForall extends ProofTactic with ProofFactSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: Formula, x: VariableLabel, t: Term)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val quantified = BinderFormula(Forall, x, phi)
      lazy val instantiated = substituteVariables(phi, Map(x -> t))

      if (!isSameSet(bot.right, premiseSequent.right))
        proof.InvalidProofTactic("Right-hand side of conclusion is not the same as right-hand side of premise")
      else if (!isSameSet(bot.left + instantiated, premiseSequent.left + quantified))
        proof.InvalidProofTactic("Left-hand side of conclusion + φ[t/x] is not the same as left-hand side of premise + ∀x. φ")
      else
        proof.ValidProofTactic(Seq(SC.LeftForall(bot, -1, phi, x, t)), Seq(premise))
    }

    def withParameters(using lib: Library, proof: lib.Proof)(t: Term)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = bot.left.diff(premiseSequent.left)
      lazy val instantiatedPivot = premiseSequent.left // .diff(bot.left)

      if (!pivot.isEmpty)
        if (pivot.tail.isEmpty)
          pivot.head match {
            case BinderFormula(Forall, x, phi) => LeftForall.withParameters(phi, x, t)(premise)(bot)
            case _ => proof.InvalidProofTactic("Could not infer a universally quantified pivot from premise and conclusion.")
          }
        else
          proof.InvalidProofTactic("Left-hand side of conclusion + φ[t/x] is not the same as left-hand side of premise + ∀x. φ.")
      else if (instantiatedPivot.isEmpty)
        if (isSubset(premiseSequent.right, bot.right))
          unwrapTactic(Weakening(premise)(bot))("Attempted weakening on trivial premise for LeftForall failed.")
        else
          proof.InvalidProofTactic("Right-hand side of conclusion is not a superset of the premises.")
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
          case Some(BinderFormula(Forall, x, phi)) => LeftForall.withParameters(phi, x, t)(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not match discovered quantified pivot with premise.")
        }
      } else proof.InvalidProofTactic("Left-hand side of conclusion + φ[t/x] is not the same as left-hand side of premise + ∀x. φ.")
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val prepivot = bot.left.diff(premiseSequent.left)
      lazy val pivot = if (prepivot.isEmpty) bot.left else prepivot
      lazy val instantiatedPivot = premiseSequent.left.diff(bot.left)

      if (instantiatedPivot.isEmpty)
        if (isSubset(premiseSequent.right, bot.right))
          unwrapTactic(Weakening(premise)(bot))("Attempted weakening on trivial premise for LeftForall failed.")
        else
          proof.InvalidProofTactic("Right-hand side of conclusion is not a superset of the premises.")
      else if (instantiatedPivot.tail.isEmpty) {
        // go through conclusion to find a matching quantified formula

        val in: Formula = instantiatedPivot.head
        val quantifiedPhi: Option[Formula] = pivot.find(f =>
          f match {
            case g @ BinderFormula(Forall, x, phi) => UnificationUtils.matchFormula(in, phi, takenTermVariables = (phi.freeVariables - x)).isDefined
            case _ => false
          }
        )

        quantifiedPhi match {
          case Some(BinderFormula(Forall, x, phi)) =>
            LeftForall.withParameters(phi, x, UnificationUtils.matchFormula(in, phi, takenTermVariables = (phi.freeVariables - x)).get._2.getOrElse(x, Term(x, Nil)))(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not match discovered quantified pivot with premise.")
        }
      } else proof.InvalidProofTactic("Left-hand side of conclusion + φ[t/x] is not the same as left-hand side of premise + ∀x. φ.")
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
  object LeftExists extends ProofTactic with ProofFactSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: Formula, x: VariableLabel)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val quantified = BinderFormula(Exists, x, phi)

      if ((bot.left union bot.right).exists(_.freeVariables.contains(x)))
        proof.InvalidProofTactic("The variable x must not be free in the resulting sequent.")
      else if (!isSameSet(bot.right, premiseSequent.right))
        proof.InvalidProofTactic("Right-hand side of conclusion is not the same as right-hand side of premise")
      else if (!isSameSet(bot.left + phi, premiseSequent.left + quantified))
        proof.InvalidProofTactic("Left-hand side of conclusion + φ is not the same as left-hand side of premise + ∃x. φ")
      else
        proof.ValidProofTactic(Seq(SC.LeftExists(bot, -1, phi, x)), Seq(premise))
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = bot.left.diff(premiseSequent.left)
      lazy val instantiatedPivot = premiseSequent.left.diff(bot.left)

      if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty)
          if (SC.isSameSequent(premiseSequent, bot))
            unwrapTactic(Rewrite(premise)(bot))("Attempted rewrite on trivial premise for LeftExists failed.")
          else
            proof.InvalidProofTactic("Could not infer a pivot from premise and conclusion.")
        else if (instantiatedPivot.tail.isEmpty) {
          val in: Formula = instantiatedPivot.head
          val quantifiedPhi: Option[Formula] = bot.left.find(f =>
            f match {
              case BinderFormula(Exists, _, g) => isSame(g, in)
              case _ => false
            }
          )

          quantifiedPhi match {
            case Some(BinderFormula(Exists, x, phi)) => LeftExists.withParameters(phi, x)(premise)(bot)
            case _ => proof.InvalidProofTactic("Could not infer an existensially quantified pivot from premise and conclusion.")
          }
        } else proof.InvalidProofTactic("Left-hand side of conclusion + φ is not the same as left-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case BinderFormula(Exists, x, phi) => LeftExists.withParameters(phi, x)(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
        }
      else
        proof.InvalidProofTactic("Left-hand side of conclusion + φ is not the same as left-hand side of premise + ∃x. φ.")
    }
  }

  /**
   * <pre>
   *  Γ, ∃y.∀x. (x=y) ⇔ φ |-  Δ
   * ---------------------------- if y is not free in φ
   *      Γ, ∃!x. φ |- Δ
   * </pre>
   */
  object LeftExistsOne extends ProofTactic with ProofFactSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: Formula, x: VariableLabel)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val y = VariableLabel(freshId(phi.freeVariables.map(_.id), x.id))
      lazy val instantiated = BinderFormula(Exists, y, BinderFormula(Forall, x, ConnectorFormula(Iff, List(PredicateFormula(equality, List(VariableTerm(x), VariableTerm(y))), phi))))
      lazy val quantified = BinderFormula(ExistsOne, x, phi)

      if (!isSameSet(bot.right, premiseSequent.right))
        proof.InvalidProofTactic("Right-hand side of conclusion is not the same as right-hand side of premise.")
      else if (!isSameSet(bot.left + instantiated, premiseSequent.left + quantified))
        proof.InvalidProofTactic("Left-hand side of conclusion + ∃y.∀x. (x=y) ⇔ φ is not the same as left-hand side of premise + ∃!x. φ.")
      else
        proof.ValidProofTactic(Seq(SC.LeftExistsOne(bot, -1, phi, x)), Seq(premise))
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = bot.left.diff(premiseSequent.left)
      lazy val instantiatedPivot = premiseSequent.left.diff(bot.left)

      if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty)
          if (SC.isSameSequent(premiseSequent, bot))
            unwrapTactic(Rewrite(premise)(bot))("Attempted rewrite on trivial premise for LeftExistsOne failed.")
          else
            proof.InvalidProofTactic("Right-hand side of conclusion is not a superset of the premises.")
        else if (instantiatedPivot.tail.isEmpty) {
          instantiatedPivot.head match {
            // ∃_. ∀x. _ ⇔ φ == extract ==> x, phi
            case BinderFormula(Exists, _, BinderFormula(Forall, x, ConnectorFormula(Iff, Seq(_, phi)))) => LeftExistsOne.withParameters(phi, x)(premise)(bot)
            case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
          }
        } else
          proof.InvalidProofTactic("Left-hand side of conclusion + φ is not the same as left-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case BinderFormula(ExistsOne, x, phi) => LeftExistsOne.withParameters(phi, x)(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
        }
      else
        proof.InvalidProofTactic("Left-hand side of conclusion + φ is not the same as left-hand side of premise + ∃x. φ.")
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
    def withParameters(using lib: Library, proof: lib.Proof)(conjuncts: Formula*)(premises: proof.Fact*)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequents = premises.map(proof.getSequent(_))
      lazy val conjunction = ConnectorFormula(And, conjuncts)

      if (premises.length == 0)
        proof.InvalidProofTactic(s"Premises expected, ${premises.length} received.")
      else if (premises.length != conjuncts.length)
        proof.InvalidProofTactic(s"Premises and conjuncts expected to be equal in number, but ${premises.length} premises and ${conjuncts.length} conjuncts received.")
      else if (!isSameSet(bot.left, premiseSequents.map(_.left).reduce(_ union _)))
        proof.InvalidProofTactic("Left-hand side of conclusion is not the union of the left-hand sides of the premises.")
      else if (!isSameSet(conjuncts.foldLeft(bot.right)(_ + _), premiseSequents.map(_.right).reduce(_ union _) + conjunction))
        proof.InvalidProofTactic("Right-hand side of conclusion + conjuncts is not the same as the union of the right-hand sides of the premises + φ∧ψ....")
      else
        proof.ValidProofTactic(Seq(SC.RightAnd(bot, Range(-1, -premises.length - 1, -1), conjuncts)), premises)
    }

    def apply(using lib: Library, proof: lib.Proof)(premises: proof.Fact*)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequents = premises.map(proof.getSequent(_))
      lazy val pivots = premiseSequents.map(_.right.diff(bot.right))

      if (premises.length == 0) proof.InvalidProofTactic(s"Premises expected, ${premises.length} received.")
      else if (pivots.exists(_.isEmpty)) {
        val emptyIndex = pivots.indexWhere(_.isEmpty)
        if (isSubset(premiseSequents(emptyIndex).left, bot.left))
          unwrapTactic(Weakening(premises(emptyIndex))(bot))("Attempted weakening on trivial premise for RightAnd failed.")
        else
          proof.InvalidProofTactic("Left-hand side of conclusion is not a superset of the one of the premises.")
      } else if (pivots.forall(_.tail.isEmpty))
        RightAnd.withParameters(pivots.map(_.head): _*)(premises: _*)(bot)
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
  object RightOr extends ProofTactic with ProofFactSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: Formula, psi: Formula)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val phiAndPsi = ConnectorFormula(Or, Seq(phi, psi))

      if (!isSameSet(bot.left, premiseSequent.left))
        proof.InvalidProofTactic("Left-hand side of the premise is not the same as the left-hand side of the conclusion.")
      else if (
        !isSameSet(bot.right + phi, premiseSequent.right + phiAndPsi) &&
        !isSameSet(bot.right + psi, premiseSequent.right + phiAndPsi) &&
        !isSameSet(bot.right + phi + psi, premiseSequent.right + phiAndPsi)
      )
        proof.InvalidProofTactic("Right-hand side of premise + φ∧ψ is not the same as right-hand side of conclusion + either φ, ψ or both.")
      else
        proof.ValidProofTactic(Seq(SC.RightOr(bot, -1, phi, psi)), Seq(premise))
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = bot.right.diff(premiseSequent.right)

      if (!pivot.isEmpty && pivot.tail.isEmpty)
        pivot.head match {
          case ConnectorFormula(Or, Seq(phi, psi)) =>
            if (premiseSequent.left.contains(phi))
              RightOr.withParameters(phi, psi)(premise)(bot)
            else
              RightOr.withParameters(psi, phi)(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not infer a disjunction as pivot from premise and conclusion.")
        }
      else
      // try a rewrite, if it works, go ahead with it, otherwise malformed
      if (SC.isSameSequent(premiseSequent, bot))
        unwrapTactic(Rewrite(premise)(bot))("Attempted rewrite on trivial premise for RightOr failed.")
      else
        proof.InvalidProofTactic("Right-hand side of conclusion + φ∧ψ is not the same as right-hand side of premise + either φ, ψ or both.")
    }
  }

  /**
   * <pre>
   *  Γ, φ |- ψ, Δ
   * --------------
   *  Γ |- φ⇒ψ, Δ
   * </pre>
   */
  object RightImplies extends ProofTactic with ProofFactSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: Formula, psi: Formula)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val implication = ConnectorFormula(Implies, Seq(phi, psi))

      if (!isSameSet(bot.left + phi, premiseSequent.left))
        proof.InvalidProofTactic("Left-hand side of conclusion + φ is not the same as left-hand side of premise.")
      else if (!isSameSet(bot.right + psi, premiseSequent.right + implication))
        proof.InvalidProofTactic("Right-hand side of conclusion + ψ is not the same as right-hand side of premise + φ⇒ψ.")
      else
        proof.ValidProofTactic(Seq(SC.RightImplies(bot, -1, phi, psi)), Seq(premise))
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val leftPivot = premiseSequent.left.diff(bot.left)
      lazy val rightPivot = premiseSequent.right.diff(bot.right)

      if (
        !leftPivot.isEmpty && leftPivot.tail.isEmpty &&
        !rightPivot.isEmpty && rightPivot.tail.isEmpty
      )
        RightImplies.withParameters(leftPivot.head, rightPivot.head)(premise)(bot)
      else
        proof.InvalidProofTactic("Could not infer an implication as pivot from premise and conclusion.")
    }
  }

  /**
   * <pre>
   *  Γ |- φ⇒ψ, Δ    Σ |- ψ⇒φ, Π
   * ----------------------------
   *      Γ, Σ |- φ⇔ψ, Π, Δ
   * </pre>
   */
  object RightIff extends ProofTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: Formula, psi: Formula)(prem1: proof.Fact, prem2: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val leftSequent = proof.getSequent(prem1)
      lazy val rightSequent = proof.getSequent(prem2)
      lazy val implication = ConnectorFormula(Iff, Seq(phi, psi))
      lazy val impLeft = ConnectorFormula(Implies, Seq(phi, psi))
      lazy val impRight = ConnectorFormula(Implies, Seq(psi, phi))

      if (!isSameSet(bot.left, leftSequent.left union rightSequent.left))
        proof.InvalidProofTactic("Left-hand side of conclusion is not the union of the left-hand sides of the premises.")
      else if (!isSameSet(bot.right + impLeft + impRight, leftSequent.right union rightSequent.right + implication))
        proof.InvalidProofTactic("Right-hand side of conclusion + φ⇒ψ + ψ⇒φ is not the same as the union of the right-hand sides of the premises + φ⇔ψ.")
      else
        proof.ValidProofTactic(Seq(SC.RightIff(bot, -1, -2, phi, psi)), Seq(prem1, prem2))
    }

    def apply(using lib: Library, proof: lib.Proof)(prem1: proof.Fact, prem2: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(prem1)
      lazy val pivot = premiseSequent.right.diff(bot.right)

      if (pivot.isEmpty)
        if (isSubset(premiseSequent.left, bot.left))
          unwrapTactic(Weakening(prem1)(bot))("Attempted weakening on trivial premise for RightIff failed.")
        else
          proof.InvalidProofTactic("Left-hand side of conclusion is not a superset of the premises.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case ConnectorFormula(Implies, Seq(phi, psi)) => RightIff.withParameters(phi, psi)(prem1, prem2)(bot)
          case _ => proof.InvalidProofTactic("Could not infer an implication as pivot from premise and conclusion.")
        }
      else
        proof.InvalidProofTactic("Right-hand side of conclusion + φ⇒ψ + ψ⇒φ is not the same as the union of the right-hand sides of the premises φ⇔ψ.")
    }
  }

  /**
   * <pre>
   *  Γ, φ |- Δ
   * --------------
   *   Γ |- ¬φ, Δ
   * </pre>
   */
  object RightNot extends ProofTactic with ProofFactSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: Formula)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val negation = ConnectorFormula(Neg, Seq(phi))

      if (!isSameSet(bot.left + phi, premiseSequent.left))
        proof.InvalidProofTactic("Left-hand side of conclusion + φ is not the same as left-hand side of premise.")
      else if (!isSameSet(bot.right, premiseSequent.right + negation))
        proof.InvalidProofTactic("Right-hand side of conclusion is not the same as right-hand side of premise + ¬φ.")
      else
        proof.ValidProofTactic(Seq(SC.RightNot(bot, -1, phi)), Seq(premise))
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = premiseSequent.left.diff(bot.left)

      if (pivot.isEmpty)
        if (isSubset(premiseSequent.right, bot.right))
          unwrapTactic(Weakening(premise)(bot))("Attempted weakening on trivial premise for RightIff failed.")
        else
          proof.InvalidProofTactic("Right-hand side of conclusion is not a superset of the premises.")
      else if (pivot.tail.isEmpty)
        RightNot.withParameters(pivot.head)(premise)(bot)
      else
        proof.InvalidProofTactic("Left-hand side of conclusion + φ is not the same as left-hand side of premise.")

    }
  }

  /**
   * <pre>
   *    Γ |- φ, Δ
   * ------------------- if x is not free in the resulting sequent
   *  Γ |- ∀x. φ, Δ
   * </pre>
   */
  object RightForall extends ProofTactic with ProofFactSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: Formula, x: VariableLabel)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val quantified = BinderFormula(Forall, x, phi)

      if ((bot.left union bot.right).exists(_.freeVariables.contains(x)))
        proof.InvalidProofTactic("The variable x is free in the resulting sequent.")
      else if (!isSameSet(bot.left, premiseSequent.left))
        proof.InvalidProofTactic("Left-hand side of conclusion is not the same as left-hand side of premise.")
      else if (!isSameSet(bot.right + phi, premiseSequent.right + quantified))
        proof.InvalidProofTactic("Right-hand side of conclusion + φ is not the same as right-hand side of premise + ∀x. φ.")
      else
        proof.ValidProofTactic(Seq(SC.RightForall(bot, -1, phi, x)), Seq(premise))
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = bot.right.diff(premiseSequent.right)
      lazy val instantiatedPivot = premiseSequent.right.diff(bot.right)

      if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty)
          if (SC.isSameSequent(premiseSequent, bot))
            unwrapTactic(Rewrite(premise)(bot))("Attempted rewrite on trivial premise for RightForall failed.")
          else
            proof.InvalidProofTactic("Could not infer a pivot from the premise and conclusion.")
        else if (instantiatedPivot.tail.isEmpty) {
          val in: Formula = instantiatedPivot.head
          val quantifiedPhi: Option[Formula] = bot.right.find(f =>
            f match {
              case BinderFormula(Forall, _, g) => isSame(g, in)
              case _ => false
            }
          )

          quantifiedPhi match {
            case Some(BinderFormula(Forall, x, phi)) => RightForall.withParameters(phi, x)(premise)(bot)
            case _ => proof.InvalidProofTactic("Could not infer a universally quantified pivot from premise and conclusion.")
          }
        } else proof.InvalidProofTactic("Right-hand side of conclusion + φ is not the same as right-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case BinderFormula(Forall, x, phi) => RightForall.withParameters(phi, x)(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not infer a universally quantified pivot from premise and conclusion.")
        }
      else
        proof.InvalidProofTactic("Right-hand side of conclusion + φ is not the same as right-hand side of premise + ∃x. φ.")
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
  object RightExists extends ProofTactic with ProofFactSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: Formula, x: VariableLabel, t: Term)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val quantified = BinderFormula(Exists, x, phi)
      lazy val instantiated = substituteVariables(phi, Map(x -> t))

      if (!isSameSet(bot.left, premiseSequent.left))
        proof.InvalidProofTactic("Left-hand side of conclusion is not the same as left-hand side of premise")
      else if (!isSameSet(bot.right + instantiated, premiseSequent.right + quantified))
        proof.InvalidProofTactic("Right-hand side of conclusion + φ[t/x] is not the same as right-hand side of premise + ∃x. φ")
      else
        proof.ValidProofTactic(Seq(SC.RightExists(bot, -1, phi, x, t)), Seq(premise))
    }

    def withParameters(using lib: Library, proof: lib.Proof)(t: Term)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = bot.right.diff(premiseSequent.right)
      lazy val instantiatedPivot = premiseSequent.right.diff(bot.right)

      if (!pivot.isEmpty)
        if (pivot.tail.isEmpty)
          pivot.head match {
            case BinderFormula(Exists, x, phi) => RightExists.withParameters(phi, x, t)(premise)(bot)
            case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
          }
        else
          proof.InvalidProofTactic("Right-hand side of conclusion + φ[t/x] is not the same as right-hand side of premise + ∃x. φ.")
      else if (instantiatedPivot.isEmpty)
        if (isSubset(premiseSequent.left, bot.left))
          unwrapTactic(Weakening(premise)(bot))("Attempted weakening on trivial premise for RightExists failed.")
        else
          proof.InvalidProofTactic("Left-hand side of conclusion is not a superset of the premises.")
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
          case Some(BinderFormula(Exists, x, phi)) => RightExists.withParameters(phi, x, t)(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not match discovered quantified pivot with premise.")
        }
      } else proof.InvalidProofTactic("Right-hand side of conclusion + φ[t/x] is not the same as right-hand side of premise + ∃x. φ.")
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val prepivot = bot.right.diff(premiseSequent.right)
      lazy val pivot = if (prepivot.isEmpty) bot.right else prepivot
      lazy val instantiatedPivot = premiseSequent.right.diff(bot.right)

      if (instantiatedPivot.isEmpty)
        if (isSubset(premiseSequent.left, bot.left))
          unwrapTactic(Weakening(premise)(bot))("Attempted weakening on trivial premise for RightForall failed.")
        else
          proof.InvalidProofTactic("Left-hand side of conclusion is not a superset of the premises.")
      else if (instantiatedPivot.tail.isEmpty) {
        // go through conclusion to find a matching quantified formula

        val in: Formula = instantiatedPivot.head
        val quantifiedPhi: Option[Formula] = pivot.find(f =>
          f match {
            case g @ BinderFormula(Exists, x, phi) => UnificationUtils.matchFormula(in, phi, takenTermVariables = (phi.freeVariables - x)).isDefined
            case _ => false
          }
        )

        quantifiedPhi match {
          case Some(BinderFormula(Exists, x, phi)) =>
            RightExists.withParameters(phi, x, UnificationUtils.matchFormula(in, phi, takenTermVariables = (phi.freeVariables - x)).get._2.getOrElse(x, Term(x, Nil)))(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not match discovered quantified pivot with premise.")
        }
      } else proof.InvalidProofTactic("Right-hand side of conclusion + φ[t/x] is not the same as right-hand side of premise + ∃x. φ.")
    }
  }

  /**
   * <pre>
   *  Γ |- ∃y.∀x. (x=y) ⇔ φ, Δ
   * ---------------------------- if y is not free in φ
   *      Γ|- ∃!x. φ,  Δ
   * </pre>
   */
  object RightExistsOne extends ProofTactic with ProofFactSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: Formula, x: VariableLabel)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val y = VariableLabel(freshId(phi.freeVariables.map(_.id), x.id))
      lazy val instantiated = BinderFormula(Exists, y, BinderFormula(Forall, x, ConnectorFormula(Iff, List(PredicateFormula(equality, List(VariableTerm(x), VariableTerm(y))), phi))))
      lazy val quantified = BinderFormula(ExistsOne, x, phi)

      if (!isSameSet(bot.left, premiseSequent.left))
        proof.InvalidProofTactic("Left-hand side of conclusion is not the same as left-hand side of premise.")
      else if (!isSameSet(bot.right + instantiated, premiseSequent.right + quantified))
        proof.InvalidProofTactic("Right-hand side of conclusion + ∃y.∀x. (x=y) ⇔ φ is not the same as right-hand side of premise + ∃!x. φ.")
      else
        proof.ValidProofTactic(Seq(SC.RightExistsOne(bot, -1, phi, x)), Seq(premise))
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = bot.right.diff(premiseSequent.right)
      lazy val instantiatedPivot = premiseSequent.right.diff(bot.right)

      if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty)
          if (SC.isSameSequent(premiseSequent, bot))
            unwrapTactic(Rewrite(premise)(bot))("Attempted rewrite on trivial premise for RightExistsOne failed.")
          else
            proof.InvalidProofTactic("Could not infer a pivot from premise and conclusion.")
        else if (instantiatedPivot.tail.isEmpty) {
          instantiatedPivot.head match {
            // ∃_. ∀x. _ ⇔ φ == extract ==> x, phi
            case BinderFormula(Exists, _, BinderFormula(Forall, x, ConnectorFormula(Iff, Seq(_, phi)))) => RightExistsOne.withParameters(phi, x)(premise)(bot)
            case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
          }
        } else
          proof.InvalidProofTactic("Right-hand side of conclusion + φ is not the same as right-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case BinderFormula(ExistsOne, x, phi) => RightExistsOne.withParameters(phi, x)(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
        }
      else
        proof.InvalidProofTactic("Right-hand side of conclusion + φ is not the same as right-hand side of premise + ∃x. φ.")
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
  object Weakening extends ProofTactic with ProofFactSequentTactic {
    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)

      if (!SC.isImplyingSequent(premiseSequent, bot))
        proof.InvalidProofTactic("Conclusion cannot be trivially derived from premise.")
      else
        proof.ValidProofTactic(Seq(SC.Weakening(bot, -1)), Seq(premise))
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
  object LeftRefl extends ProofTactic with ProofFactSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(fa: Formula)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)

      if (!isSameSet(bot.left + fa, premiseSequent.left) || !premiseSequent.left.exists(_ == fa) || bot.left.exists(_ == fa))
        proof.InvalidProofTactic("Left-hand sides of the conclusion + φ is not the same as left-hand side of the premise.")
      else if (!isSameSet(bot.right, premiseSequent.right))
        proof.InvalidProofTactic("Right-hand side of the premise is not the same as the right-hand side of the conclusion.")
      else
        fa match {
          case PredicateFormula(`equality`, Seq(left, right)) =>
            if (isSameTerm(left, right))
              proof.ValidProofTactic(Seq(SC.LeftRefl(bot, -1, fa)), Seq(premise))
            else
              proof.InvalidProofTactic("φ is not an instance of reflexivity.")
          case _ => proof.InvalidProofTactic("φ is not an equality.")
        }
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = premiseSequent.left.diff(bot.left)

      if (!pivot.isEmpty && pivot.tail.isEmpty)
        LeftRefl.withParameters(pivot.head)(premise)(bot)
      else
        proof.InvalidProofTactic("Could not infer an equality as pivot from premise and conclusion.")
    }
  }

  /**
   * <pre>
   *
   * --------------
   *     |- s=s
   * </pre>
   */
  object RightRefl extends ProofTactic with ProofSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(fa: Formula)(bot: Sequent): proof.ProofTacticJudgement = {
      if (!bot.right.exists(_ == fa))
        proof.InvalidProofTactic("Right-hand side of conclusion does not contain φ.")
      else
        fa match {
          case PredicateFormula(`equality`, Seq(left, right)) =>
            if (isSameTerm(left, right))
              proof.ValidProofTactic(Seq(SC.RightRefl(bot, fa)), Seq())
            else
              proof.InvalidProofTactic("φ is not an instance of reflexivity.")
          case _ => proof.InvalidProofTactic("φ is not an equality.")
        }
    }

    def apply(using lib: Library, proof: lib.Proof)(bot: Sequent): proof.ProofTacticJudgement = {
      if (bot.right.isEmpty) proof.InvalidProofTactic("Right-hand side of conclusion does not contain an instance of reflexivity.")
      else {
        // go through conclusion to see if you can find an reflexive formula
        val pivot: Option[Formula] = bot.right.find(f =>
          f match {
            case PredicateFormula(`equality`, Seq(l, r)) => isSameTerm(l, r)
            case _ => false
          }
        )

        pivot match {
          case Some(phi) => RightRefl.withParameters(phi)(bot)
          case _ => proof.InvalidProofTactic("Could not infer an equality as pivot from conclusion.")
        }

      }

    }
  }

  /**
   * <pre>
   *           Γ, φ(s1,...,sn) |- Δ
   * ----------------------------------------
   *  Γ, s1=t1, ..., sn=tn, φ(t1,...tn) |- Δ
   * </pre>
   */
  object LeftSubstEq extends ProofTactic {
    def apply(using lib: Library, proof: lib.Proof)(equals: List[(Term, Term)], lambdaPhi: LambdaTermFormula)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val (s_es, t_es) = equals.unzip
      lazy val phi_s = lambdaPhi(s_es)
      lazy val phi_t = lambdaPhi(t_es)
      lazy val equalities = equals map { case (s, t) => PredicateFormula(equality, Seq(s, t)) }

      if (!isSameSet(bot.right, premiseSequent.right))
        proof.InvalidProofTactic("Right-hand side of the premise is not the same as the right-hand side of the conclusion.")
      else if (
        !isSameSet(bot.left + phi_s, premiseSequent.left ++ equalities + phi_t) &&
        !isSameSet(bot.left + phi_t, premiseSequent.left ++ equalities + phi_s)
      )
        proof.InvalidProofTactic("Left-hand side of the conclusion + φ(s_) is not the same as left-hand side of the premise + (s=t)_ + φ(t_) (or with s_ and t_ swapped).")
      else
        proof.ValidProofTactic(Seq(SC.LeftSubstEq(bot, -1, equals, lambdaPhi)), Seq(premise))
    }
  }

  /**
   * <pre>
   *          Γ |- φ(s1,...,sn), Δ
   * ----------------------------------------
   *  Γ, s1=t1, ..., sn=tn |- φ(t1,...tn), Δ
   * </pre>
   */
  object RightSubstEq extends ProofTactic {
    def apply(using lib: Library, proof: lib.Proof)(equals: List[(Term, Term)], lambdaPhi: LambdaTermFormula)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val (s_es, t_es) = equals.unzip
      lazy val phi_s = lambdaPhi(s_es)
      lazy val phi_t = lambdaPhi(t_es)
      lazy val equalities = equals map { case (s, t) => PredicateFormula(equality, Seq(s, t)) }

      if (!isSameSet(bot.left, premiseSequent.left ++ equalities))
        proof.InvalidProofTactic("Left-hand side of the conclusion is not the same as the left-hand side of the premise + (s=t)_.")
      else if (
        !isSameSet(bot.right + phi_s, premiseSequent.right + phi_t) &&
        !isSameSet(bot.right + phi_t, premiseSequent.right + phi_s)
      )
        proof.InvalidProofTactic("Right-hand side of the conclusion + φ(s_) is not the same as right-hand side of the premise + φ(t_) (or with s_ and t_ swapped).")
      else
        proof.ValidProofTactic(Seq(SC.RightSubstEq(bot, -1, equals, lambdaPhi)), Seq(premise))
    }

    def apply2(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      val premRight = ConnectorFormula(Or, premiseSequent.right.toSeq)
      val botRight = ConnectorFormula(Or, bot.right.toSeq)

      val equalities = bot.left.collect { case PredicateFormula(equality, Seq(l, r)) => (l, r) }
      val canReach = UnificationUtils.getContextFormula(
        first = premRight,
        second = botRight,
        confinedTermRules = equalities.toSeq,
        takenTermVariables = equalities.flatMap(e => e._1.freeVariables ++ e._2.freeVariables)
      )

      if (canReach.isEmpty) proof.InvalidProofTactic("Could not find a set of equalities to rewrite premise into conclusion successfully.")
      else
        val termLambda = canReach.get.toTermLambda
        RightSubstEq(equalities.toList, termLambda)(premise)(bot)
    }
  }

  /**
   * <pre>
   *           Γ, φ(a1,...an) |- Δ
   * ----------------------------------------
   *  Γ, a1⇔b1, ..., an⇔bn, φ(b1,...bn) |- Δ
   * </pre>
   */
  object LeftSubstIff extends ProofTactic {
    def apply(using lib: Library, proof: lib.Proof)(equals: List[(Formula, Formula)], lambdaPhi: LambdaFormulaFormula)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val (psi_es, tau_es) = equals.unzip
      lazy val phi_psi = lambdaPhi(psi_es)
      lazy val phi_tau = lambdaPhi(tau_es)
      lazy val implications = equals map { case (s, t) => ConnectorFormula(Iff, Seq(s, t)) }

      if (!isSameSet(bot.right, premiseSequent.right))
        proof.InvalidProofTactic("Right-hand side of the premise is not the same as the right-hand side of the conclusion.")
      else if (
        !isSameSet(bot.left + phi_psi, premiseSequent.left ++ implications + phi_tau) &&
        !isSameSet(bot.left + phi_tau, premiseSequent.left ++ implications + phi_psi)
      )
        proof.InvalidProofTactic("Left-hand side of the conclusion + φ(ψ_) is not the same as left-hand side of the premise + (ψ ⇔ τ)_ + φ(τ_) (or with ψ_ and τ_ swapped).")
      else
        proof.ValidProofTactic(Seq(SC.LeftSubstIff(bot, -1, equals, lambdaPhi)), Seq(premise))
    }
  }

  /**
   * <pre>
   *           Γ |- φ(a1,...an), Δ
   * ----------------------------------------
   *  Γ, a1⇔b1, ..., an⇔bn |- φ(b1,...bn), Δ
   * </pre>
   */
  object RightSubstIff extends ProofTactic {
    def apply(using lib: Library, proof: lib.Proof)(equals: List[(Formula, Formula)], lambdaPhi: LambdaFormulaFormula)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val (psi_es, tau_es) = equals.unzip
      lazy val phi_psi = lambdaPhi(psi_es)
      lazy val phi_tau = lambdaPhi(tau_es)
      lazy val implications = equals map { case (s, t) => ConnectorFormula(Iff, Seq(s, t)) }

      if (!isSameSet(bot.left, premiseSequent.left ++ implications)) {
        println(lisa.utils.parsing.FOLPrinter.prettySequent(bot))
        println(lisa.utils.parsing.FOLPrinter.prettySequent(premiseSequent ++<< (implications |- ())))
        proof.InvalidProofTactic("Left-hand side of the conclusion is not the same as the left-hand side of the premise + (ψ ⇔ τ)_.")
      } else if (
        !isSameSet(bot.right + phi_psi, premiseSequent.right + phi_tau) &&
        !isSameSet(bot.right + phi_tau, premiseSequent.right + phi_psi)
      ) {
        println(s"========================")
        println(s"RIGHT SUBST IFF")
        println(s"bot right: ${bot.right.map(FOLPrinter.prettyFormula(_))}")
        println(s"prm right: ${premiseSequent.right.map(FOLPrinter.prettyFormula(_))}")
        println(s"phi psi: ${(FOLPrinter.prettyFormula(phi_psi))}")
        println(s"phi tau: ${(FOLPrinter.prettyFormula(phi_tau))}")
        println(s"========================")
        proof.InvalidProofTactic("Right-hand side of the conclusion + φ(ψ_) is not the same as right-hand side of the premise + φ(τ_) (or with ψ_ and τ_ swapped).")
      } else proof.ValidProofTactic(Seq(SC.RightSubstIff(bot, -1, equals, lambdaPhi)), Seq(premise))
    }
  }

  /**
   * <pre>
   *           Γ |- Δ
   * --------------------------
   *  Γ[r(a)/?f] |- Δ[r(a)/?f]
   * </pre>
   */
  object InstFunSchema extends ProofTactic {
    def apply(using lib: Library, proof: lib.Proof)(insts: Map[SchematicTermLabel, LambdaTermTerm])(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)

      if (!isSameSet(bot.left, premiseSequent.left.map(instantiateTermSchemas(_, insts))))
        proof.InvalidProofTactic("Left-hand side of premise instantiated with the map 'insts' is not the same as left-hand side of conclusion.")
      else if (!isSameSet(bot.right, premiseSequent.right.map(instantiateTermSchemas(_, insts))))
        proof.InvalidProofTactic("Right-hand side of premise instantiated with the map 'insts' is not the same as right-hand side of conclusion.")
      else
        proof.ValidProofTactic(Seq(SC.InstSchema(bot, -1, Map.empty, Map.empty, insts)), Seq(premise))
    }
  }

  /**
   * <pre>
   *           Γ |- Δ
   * --------------------------
   *  Γ[ψ(a)/?p] |- Δ[ψ(a)/?p]
   * </pre>
   */
  object InstPredSchema extends ProofTactic {
    def apply(using lib: Library, proof: lib.Proof)(insts: Map[SchematicVarOrPredLabel, LambdaTermFormula])(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)

      if (!isSameSet(bot.left, premiseSequent.left.map(instantiatePredicateSchemas(_, insts))))
        proof.InvalidProofTactic("Left-hand side of premise instantiated with the map 'insts' is not the same as left-hand side of conclusion.")
      else if (!isSameSet(bot.right, premiseSequent.right.map(instantiatePredicateSchemas(_, insts))))
        proof.InvalidProofTactic("Right-hand side of premise instantiated with the map 'insts' is not the same as right-hand side of conclusion.")
      else
        proof.ValidProofTactic(Seq(SC.InstSchema(bot, -1, Map.empty, insts, Map.empty)), Seq(premise))
    }
  }

  object InstSchema extends ProofTactic {
    def apply(using
        lib: Library,
        proof: lib.Proof
    )(mCon: Map[SchematicConnectorLabel, LambdaFormulaFormula], mPred: Map[SchematicVarOrPredLabel, LambdaTermFormula], mTerm: Map[SchematicTermLabel, LambdaTermTerm])(
        premise: proof.Fact
    ): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premise)
      val bot = instantiateSchemaInSequent(premiseSequent, mCon, mPred, mTerm)
      proof.ValidProofTactic(Seq(SC.InstSchema(bot, -1, mCon, mPred, mTerm)), Seq(premise))
    }
  }

  class SUBPROOF(using val proof: Library#Proof)(statement: Option[Sequent | String])(computeProof: proof.InnerProof ?=> Unit) extends ProofTactic {
    val bot: Option[Sequent] = statement map {
      case s: Sequent => s
      case s: String => lisa.utils.FOLParser.parseSequent(s)
    }

    val iProof: proof.InnerProof = new proof.InnerProof(bot)
    val scproof: SCProof = {
      try {
        computeProof(using iProof)
      } catch {
        case e: NotImplementedError =>
          throw (new UnimplementedProof(proof.owningTheorem))
        case e: UserLisaException =>
          throw (e)
      }
      if (iProof.length == 0)
        throw (new UnimplementedProof(proof.owningTheorem))
      iProof.toSCProof
    }
    val premises: Seq[proof.Fact] = iProof.getImports.map(of => of._1)
    def judgement: proof.ProofTacticJudgement = {
      if (bot.isEmpty)
        proof.ValidProofTactic(scproof.steps, premises)
      else if (!SC.isSameSequent(bot.get, scproof.conclusion))
        proof.InvalidProofTactic(s"The subproof does not prove the desired conclusion.\n\tExpected: ${FOLPrinter.prettySequent(bot.get)}\n\tObtained: ${FOLPrinter.prettySequent(scproof.conclusion)}")
      else
        proof.ValidProofTactic(scproof.steps :+ SC.Restate(bot.get, scproof.length - 1), premises)
    }
  }

  object Sorry extends ProofTactic with ProofSequentTactic {
    def apply(using lib: Library, proof: lib.Proof)(bot: Sequent): proof.ProofTacticJudgement = {
      proof.ValidProofTactic(Seq(SC.Sorry(bot)), Seq())
    }
  }

  // TODO make specific support for subproofs written inside tactics.

  def TacticSubproof(using proof: Library#Proof)(computeProof: proof.InnerProof ?=> Unit) =
    SUBPROOF(using proof)(None)(computeProof).judgement.asInstanceOf[proof.ProofTacticJudgement]

  /*
  def TacticSubproof(using proof: Library#Proof)(bot: Option[Sequent])(computeProof: proof.InnerProof ?=> Unit) =
    SUBPROOF(using proof)(Some(bot))(computeProof).judgement.asInstanceOf[proof.ProofTacticJudgement]
   */
}
