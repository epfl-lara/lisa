package lisa.utils.prooflib
import lisa.utils.K
import lisa.utils.KernelHelpers.{|- => `K|-`, _}
import lisa.utils.collection.Extensions._
import lisa.utils.fol.{FOL => F}
import lisa.utils.prooflib.ProofTacticLib.{_, given}
import lisa.utils.prooflib._
import lisa.utils.unification.UnificationUtils._

object BasicStepTactic {

  def unwrapTactic(using lib: Library, proof: lib.Proof)(using tactic: ProofTactic)(judgement: proof.ProofTacticJudgement)(message: String): proof.ProofTacticJudgement = {
    judgement match {
      case j: proof.ValidProofTactic => proof.ValidProofTactic(j.bot, j.scps, j.imports)
      case j: proof.InvalidProofTactic => proof.InvalidProofTactic(s"Internal tactic call failed! $message\n${j.message}")
    }
  }

  object Hypothesis extends ProofTactic with ProofSequentTactic {
    def apply(using lib: Library, proof: lib.Proof)(bot: F.Sequent): proof.ProofTacticJudgement = {
      val botK = bot.underlying
      val intersectedPivot = botK.left.intersect(botK.right)

      if (intersectedPivot.isEmpty)
        proof.InvalidProofTactic("A formula for input to Hypothesis could not be inferred from left and right side of the sequent.")
      else
        proof.ValidProofTactic(bot, Seq(K.Hypothesis(botK, intersectedPivot.head)), Seq())
    }
  }

  object Rewrite extends ProofTactic with ProofFactSequentTactic {
    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      val botK = bot.underlying
      if (!K.isSameSequent(botK, proof.getSequent(premise).underlying))
        proof.InvalidProofTactic("The premise and the conclusion are not trivially equivalent.")
      else
        proof.ValidProofTactic(bot, Seq(K.Restate(botK, -1)), Seq(premise))
    }
  }

  object RewriteTrue extends ProofTactic with ProofSequentTactic {
    def apply(using lib: Library, proof: lib.Proof)(bot: F.Sequent): proof.ProofTacticJudgement = {
      val botK = bot.underlying
      if (!K.isSameSequent(botK, () `K|-` K.top))
        proof.InvalidProofTactic("The desired conclusion is not a trivial tautology.")
      else
        proof.ValidProofTactic(bot, Seq(K.RestateTrue(botK)), Seq())
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
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Expr[F.Prop])(prem1: proof.Fact, prem2: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val leftSequent = proof.getSequent(prem1).underlying
      lazy val rightSequent = proof.getSequent(prem2).underlying
      val botK = bot.underlying
      val phiK = phi.underlying

      if (!K.contains(leftSequent.right, phiK))
        proof.InvalidProofTactic("Right-hand side of first premise does not contain φ as claimed.")
      else if (!K.contains(rightSequent.left, phiK))
        proof.InvalidProofTactic("Left-hand side of second premise does not contain φ as claimed.")
      else if (!K.isSameSet(botK.left + phiK, leftSequent.left ++ rightSequent.left) || (leftSequent.left.contains(phiK) && !botK.left.contains(phiK)))
        proof.InvalidProofTactic("Left-hand side of conclusion + φ is not the union of the left-hand sides of the premises.")
      else if (!K.isSameSet(botK.right + phiK, leftSequent.right ++ rightSequent.right) || (rightSequent.right.contains(phiK) && !botK.right.contains(phiK)))
        proof.InvalidProofTactic("Right-hand side of conclusion + φ is not the union of the right-hand sides of the premises.")
      else
        proof.ValidProofTactic(bot, Seq(K.Cut(botK, -1, -2, phiK)), Seq(prem1, prem2))
    }

    def apply(using lib: Library, proof: lib.Proof)(prem1: proof.Fact, prem2: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val leftSequent = proof.getSequent(prem1)
      lazy val rightSequent = proof.getSequent(prem2)

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
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Expr[F.Prop], psi: F.Expr[F.Prop])(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      val botK = bot.underlying
      val phiK = phi.underlying
      val psiK = psi.underlying
      lazy val phiAndPsi = phiK /\ psiK

      if (!K.isSameSet(botK.right, premiseSequent.right))
        proof.InvalidProofTactic("Right-hand side of the conclusion is not the same as the right-hand side of the premise.")
      else if (
        !K.isSameSet(botK.left + phiK, premiseSequent.left + phiAndPsi) &&
        !K.isSameSet(botK.left + psiK, premiseSequent.left + phiAndPsi) &&
        !K.isSameSet(botK.left + phiK + psiK, premiseSequent.left + phiAndPsi)
      )
        proof.InvalidProofTactic("Left-hand side of premise + φ∧ψ is not the same as left-hand side of conclusion + either φ, ψ or both.")
      else
        proof.ValidProofTactic(bot, Seq(K.LeftAnd(botK, -1, phiK, psiK)), Seq(premise))
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = bot.left.diff(premiseSequent.left)

      if (!pivot.isEmpty && pivot.tail.isEmpty)
        pivot.head match {
          case F.App(F.App(F.and, phi), psi) =>
            if (premiseSequent.left.contains(phi))
              LeftAnd.withParameters(phi, psi)(premise)(bot)
            else
              LeftAnd.withParameters(phi, psi)(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not infer a conjunction as pivot from premise and conclusion.")
        }
      else
        // try a rewrite, if it works, go ahead with it, otherwise malformed
        if (F.isSameSequent(premiseSequent, bot))
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
    def withParameters(using lib: Library, proof: lib.Proof)(disjuncts: F.Expr[F.Prop]*)(premises: proof.Fact*)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequents = premises.map(proof.getSequent(_).underlying)
      val botK = bot.underlying
      val disjunctsK = disjuncts.map(_.underlying)
      lazy val disjunction = K.multior(disjunctsK)

      if (premises.length == 0)
        proof.InvalidProofTactic(s"Premises expected, ${premises.length} received.")
      else if (premises.length != disjuncts.length)
        proof.InvalidProofTactic(s"Premises and disjuncts expected to be equal in number, but ${premises.length} premises and ${disjuncts.length} disjuncts received.")
      else if (!K.isSameSet(botK.right, premiseSequents.map(_.right).reduce(_ union _)))
        proof.InvalidProofTactic("Right-hand side of conclusion is not the union of the right-hand sides of the premises.")
      else if (
        premiseSequents.zip(disjunctsK).forall((sequent, disjunct) => K.isSubset(sequent.left, botK.left + disjunct)) // \forall i. premise_i.left \subset bot.left + phi_i
        && !K.isSubset(botK.left, premiseSequents.map(_.left).reduce(_ union _) + disjunction) // bot.left \subseteq \bigcup premise_i.left
      )
        proof.InvalidProofTactic("Left-hand side of conclusion + disjuncts is not the same as the union of the left-hand sides of the premises + φ∨ψ.")
      else
        proof.ValidProofTactic(bot, Seq(K.LeftOr(botK, Range(-1, -premises.length - 1, -1), disjunctsK)), premises.toSeq)
    }

    def apply(using lib: Library, proof: lib.Proof)(premises: proof.Fact*)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequents = premises.map(proof.getSequent(_))
      lazy val pivots = premiseSequents.map(_.left.diff(bot.left))

      if (premises.length == 0) proof.InvalidProofTactic(s"Premises expected, ${premises.length} received.")
      else if (pivots.exists(_.isEmpty)) {
        val emptyIndex = pivots.indexWhere(_.isEmpty)
        if (F.isSubset(premiseSequents(emptyIndex).left, bot.left))
          unwrapTactic(Weakening(premises(emptyIndex))(bot))("Attempted weakening on trivial premise for LeftOr failed.")
        else
          proof.InvalidProofTactic("Right-hand side of conclusion is not a superset of the one of the premises.")
      } else if (pivots.forall(_.tail.isEmpty))
        LeftOr.withParameters(pivots.map(_.head)*)(premises*)(bot)
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
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Expr[F.Prop], psi: F.Expr[F.Prop])(prem1: proof.Fact, prem2: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val leftSequent = proof.getSequent(prem1).underlying
      lazy val rightSequent = proof.getSequent(prem2).underlying
      val botK = bot.underlying
      val phiK = phi.underlying
      val psiK = psi.underlying
      lazy val implication = (phiK ==> psiK)

      if (!K.isSameSet(botK.right + phiK, leftSequent.right union rightSequent.right))
        proof.InvalidProofTactic("Right-hand side of conclusion + φ is not the union of right-hand sides of premises.")
      else if (!K.isSameSet(botK.left + psiK, leftSequent.left union rightSequent.left + implication))
        proof.InvalidProofTactic("Left-hand side of conclusion + ψ is not the union of left-hand sides of premises + φ⇒ψ.")
      else
        proof.ValidProofTactic(bot, Seq(K.LeftImplies(botK, -1, -2, phiK, psiK)), Seq(prem1, prem2))
    }
    def apply(using lib: Library, proof: lib.Proof)(prem1: proof.Fact, prem2: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val leftSequent = proof.getSequent(prem1)
      lazy val rightSequent = proof.getSequent(prem2)
      lazy val pivotLeft = leftSequent.right.diff(bot.right)
      lazy val pivotRight = rightSequent.left.diff(bot.left)

      if (pivotLeft.isEmpty)
        if (F.isSubset(leftSequent.left, bot.left))
          unwrapTactic(Weakening(prem1)(bot))("Attempted weakening on trivial left premise for LeftImplies failed.")
        else
          proof.InvalidProofTactic("Left-hand side of conclusion is not a superset of the first premises.")
      else if (pivotRight.isEmpty)
        if (F.isSubset(rightSequent.right, bot.right))
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
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Expr[F.Prop], psi: F.Expr[F.Prop])(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      val botK = bot.underlying
      val phiK = phi.underlying
      val psiK = psi.underlying
      lazy val implication = phiK <=> psiK
      lazy val impLeft = phiK ==> psiK
      lazy val impRight = psiK ==> phiK

      if (!K.isSameSet(botK.right, premiseSequent.right))
        proof.InvalidProofTactic("Right-hand side of premise is not the same as right-hand side of conclusion.")
      else if (
        !K.isSameSet(botK.left + impLeft, premiseSequent.left + implication) &&
        !K.isSameSet(botK.left + impRight, premiseSequent.left + implication) &&
        !K.isSameSet(botK.left + impLeft + impRight, premiseSequent.left + implication)
      )
        proof.InvalidProofTactic("Left-hand side of premise + φ⇔ψ is not the same as left-hand side of conclusion + either φ⇒ψ, ψ⇒φ or both.")
      else
        proof.ValidProofTactic(bot, Seq(K.LeftIff(botK, -1, phiK, psiK)), Seq(premise))
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = premiseSequent.left.diff(bot.left)

      if (pivot.isEmpty)
        if (F.isSubset(premiseSequent.right, bot.right))
          unwrapTactic(Weakening(premise)(bot))("Attempted weakening on trivial premise for LeftIff failed.")
        else
          proof.InvalidProofTactic("Right-hand side of conclusion is not a superset of the premises.")
      else
        pivot.head match {
          case F.App(F.App(F.implies, phi), psi) => LeftIff.withParameters(phi, psi)(premise)(bot)
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
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Expr[F.Prop])(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      val botK = bot.underlying
      val phiK = phi.underlying
      lazy val negation = !phiK

      if (!K.isSameSet(botK.right + phiK, premiseSequent.right))
        proof.InvalidProofTactic("Right-hand side of conclusion + φ is not the same as right-hand side of premise.")
      else if (!K.isSameSet(botK.left, premiseSequent.left + negation))
        proof.InvalidProofTactic("Left-hand side of conclusion is not the same as left-hand side of premise + ¬φ.")
      else
        proof.ValidProofTactic(bot, Seq(K.LeftNot(botK, -1, phiK)), Seq(premise))
    }
    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = premiseSequent.right.diff(bot.right)

      if (pivot.isEmpty)
        if (F.isSubset(premiseSequent.left, bot.left))
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
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Expr[F.Prop], x: F.Variable[F.Ind], t: F.Expr[F.Ind])(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      lazy val xK = x.underlying
      lazy val tK = t.underlying
      lazy val phiK = phi.underlying
      lazy val botK = bot.underlying
      lazy val quantified = K.forall(xK, phiK)
      lazy val instantiated = K.substituteVariables(phiK, Map(xK -> tK))

      if (!K.isSameSet(botK.right, premiseSequent.right))
        proof.InvalidProofTactic("Right-hand side of conclusion is not the same as right-hand side of premise")
      else if (!K.isSameSet(botK.left + instantiated, premiseSequent.left + quantified))
        proof.InvalidProofTactic("Left-hand side of conclusion + φ[t/x] is not the same as left-hand side of premise + ∀x. φ")
      else
        proof.ValidProofTactic(bot, Seq(K.LeftForall(botK, -1, phiK, xK, tK)), Seq(premise))
    }

    def withParameters(using lib: Library, proof: lib.Proof)(t: F.Expr[F.Ind])(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = bot.left.diff(premiseSequent.left)
      lazy val instantiatedPivot = premiseSequent.left // .diff(botK.left)

      if (!pivot.isEmpty)
        if (pivot.tail.isEmpty)
          pivot.head match {
            case F.forall(x, phi) => LeftForall.withParameters(phi, x, t)(premise)(bot)
            case _ => proof.InvalidProofTactic("Could not infer a universally quantified pivot from premise and conclusion.")
          }
        else
          proof.InvalidProofTactic("Left-hand side of conclusion + φ[t/x] is not the same as left-hand side of premise + ∀x. φ.")
      else if (instantiatedPivot.isEmpty)
        if (F.isSubset(premiseSequent.right, bot.right))
          unwrapTactic(Weakening(premise)(bot))("Attempted weakening on trivial premise for LeftForall failed.")
        else
          proof.InvalidProofTactic("Right-hand side of conclusion is not a superset of the premises.")
      else if (instantiatedPivot.tail.isEmpty) {
        // go through conclusion to find a matching quantified formula

        val in: F.Expr[F.Prop] = instantiatedPivot.head
        val quantifiedPhi: Option[F.Expr[F.Prop]] = bot.left.find(f =>
          f match {
            case g @ F.forall(v, e) => F.isSame(e.substitute(v := t), in)
            case _ => false
          }
        )

        quantifiedPhi match {
          case Some(F.forall(x, phi)) => LeftForall.withParameters(phi, x, t)(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not match discovered quantified pivot with premise.")
        }
      } else proof.InvalidProofTactic("Left-hand side of conclusion + φ[t/x] is not the same as left-hand side of premise + ∀x. φ.")
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val prepivot = bot.left.diff(premiseSequent.left)
      lazy val pivot = if (prepivot.isEmpty) bot.left else prepivot
      lazy val instantiatedPivot = premiseSequent.left.diff(bot.left)

      if (instantiatedPivot.isEmpty)
        if (F.isSubset(premiseSequent.right, bot.right))
          unwrapTactic(Weakening(premise)(bot))("Attempted weakening on trivial premise for LeftForall failed.")
        else
          proof.InvalidProofTactic("Right-hand side of conclusion is not a superset of the premises.")
      else if (instantiatedPivot.tail.isEmpty) {
        // go through conclusion to find a matching quantified formula

        val in: F.Expr[F.Prop] = instantiatedPivot.head
        val quantifiedPhi: Option[(F.Expr[F.Prop], Substitution)] = pivot.collectFirstDefined(f =>
          f match {
            case g @ F.forall(x, phi) =>
              val ctx = RewriteContext.withBound(phi.freeVars - x)
              matchExpr(using ctx)(phi, in).map(f -> _)
            case _ => None
          }
        )

        quantifiedPhi match {
          case Some((F.forall(x, phi), subst)) =>
            LeftForall.withParameters(phi, x, subst(x).getOrElse(x))(premise)(bot)
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
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Expr[F.Prop], x: F.Variable[F.Ind])(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      lazy val xK = x.underlying
      lazy val phiK = phi.underlying
      lazy val botK = bot.underlying
      lazy val quantified = K.exists(xK, phiK)

      if ((botK.left union botK.right).exists(_.freeVariables.contains(xK)))
        proof.InvalidProofTactic("The variable x must not be free in the resulting sequent.")
      else if (!K.isSameSet(botK.right, premiseSequent.right))
        proof.InvalidProofTactic("Right-hand side of conclusion is not the same as right-hand side of premise")
      else if (!K.isSameSet(botK.left + phiK, premiseSequent.left + quantified))
        proof.InvalidProofTactic("Left-hand side of conclusion + φ is not the same as left-hand side of premise + ∃x. φ")
      else
        proof.ValidProofTactic(bot, Seq(K.LeftExists(botK, -1, phiK, xK)), Seq(premise))
    }

    var debug = false
    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = bot.left.diff(premiseSequent.left)
      lazy val instantiatedPivot = premiseSequent.left.diff(bot.left)

      if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty)
          if (F.isSameSequent(premiseSequent, bot))
            unwrapTactic(Rewrite(premise)(bot))("Attempted rewrite on trivial premise for LeftExists failed.")
          else
            proof.InvalidProofTactic("Could not infer a pivot from premise and conclusion.")
        else if (instantiatedPivot.tail.isEmpty) {
          val in: F.Expr[F.Prop] = instantiatedPivot.head
          val quantifiedPhi: Option[F.Expr[F.Prop]] = bot.left.find(f =>
            f match {
              case F.exists(_, g) => F.isSame(g, in)
              case _ => false
            }
          )

          quantifiedPhi match {
            case Some(F.exists(x, phi)) => LeftExists.withParameters(phi, x)(premise)(bot)
            case _ => proof.InvalidProofTactic("Could not infer an existensially quantified pivot from premise and conclusion.")
          }
        } else proof.InvalidProofTactic("Ambigous application of LeftExists, multiple pivots corresponding to the unquantified formula found.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case F.exists(x, phi) => LeftExists.withParameters(phi, x)(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
        }
      else
        proof.InvalidProofTactic("Ambigous application of LeftExists, multiple pivots corresponding to the quantified formula found.")
    }
  }

  /*
  /**
   * <pre>
   *  Γ, ∃y.∀x. (x=y) ⇔ φ |-  Δ
   * ---------------------------- if y is not free in φ
   *      Γ, ∃!x. φ |- Δ
   * </pre>
   */
  object LeftExistsOne extends ProofTactic with ProofFactSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Expr[F.Prop], x: F.Variable[F.T])(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      lazy val xK = x.underlying
      lazy val phiK = phi.underlying
      lazy val botK = bot.underlying
      lazy val y = K.Variable(lisa.utils.KernelHelpers.freshId(phiK.freeVariables.map(_.id), x.id), K.Ind)
      lazy val instantiated = K.exists(y, K.forall(xK, (xK === y) <=> phiK ))
      lazy val quantified = K.ExistsOne(xK, phiK)

      if (!K.isSameSet(botK.right, premiseSequent.right))
        proof.InvalidProofTactic("Right-hand side of conclusion is not the same as right-hand side of premise.")
      else if (!K.isSameSet(botK.left + instantiated, premiseSequent.left + quantified))
        proof.InvalidProofTactic("Left-hand side of conclusion + ∃y.∀x. (x=y) ⇔ φ is not the same as left-hand side of premise + ∃!x. φ.")
      else
        proof.ValidProofTactic(bot, Seq(K.LeftExistsOne(botK, -1, phiK, xK)), Seq(premise))
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = bot.left.diff(premiseSequent.left)
      lazy val instantiatedPivot = premiseSequent.left.diff(bot.left)

      if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty)
          if (F.isSameSequent(premiseSequent, bot))
            unwrapTactic(Rewrite(premise)(bot))("Attempted rewrite on trivial premise for LeftExistsOne failed.")
          else
            proof.InvalidProofTactic("Right-hand side of conclusion is not a superset of the premises.")
        else if (instantiatedPivot.tail.isEmpty) {
          instantiatedPivot.head match {
            // ∃_. ∀x. _ ⇔ φ == extract ==> x, phi
            case F.exists(_, F.forall(x, F.AppliedConnector(F.Iff, Seq(_, phi)))) => LeftExistsOne.withParameters(phi, x)(premise)(bot)
            case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
          }
        } else
          proof.InvalidProofTactic("Left-hand side of conclusion + φ is not the same as left-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case F.BinderFormula(F.ExistsOne, x, phi) => LeftExistsOne.withParameters(phi, x)(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
        }
      else
        proof.InvalidProofTactic("Left-hand side of conclusion + φ is not the same as left-hand side of premise + ∃x. φ.")
    }
  }

   */

  // Right rules
  /**
   * <pre>
   *  Γ |- φ, Δ    Σ |- ψ, Π     ...
   * ------------------------------------
   *    Γ, Σ |- φ∧ψ∧..., Π, Δ
   * </pre>
   */
  object RightAnd extends ProofTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(conjuncts: F.Expr[F.Prop]*)(premises: proof.Fact*)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequents = premises.map(proof.getSequent(_).underlying)
      lazy val botK = bot.underlying
      lazy val conjunctsK = conjuncts.map(_.underlying)
      lazy val conjunction = K.multiand(conjunctsK)

      if (premises.length == 0)
        proof.InvalidProofTactic(s"Premises expected, ${premises.length} received.")
      else if (premises.length != conjuncts.length)
        proof.InvalidProofTactic(s"Premises and conjuncts expected to be equal in number, but ${premises.length} premises and ${conjuncts.length} conjuncts received.")
      else if (!K.isSameSet(botK.left, premiseSequents.map(_.left).reduce(_ union _)))
        proof.InvalidProofTactic("Left-hand side of conclusion is not the union of the left-hand sides of the premises.")
      else if (
        premiseSequents.zip(conjunctsK).forall((sequent, conjunct) => K.isSubset(sequent.right, botK.right + conjunct)) // \forall i. premise_i.right \subset bot.right + phi_i
        && !K.isSubset(botK.right, premiseSequents.map(_.right).reduce(_ union _) + conjunction) // bot.right \subseteq \bigcup premise_i.right
      )
        proof.InvalidProofTactic("Right-hand side of conclusion + conjuncts is not the same as the union of the right-hand sides of the premises + φ∧ψ....")
      else
        proof.ValidProofTactic(bot, Seq(K.RightAnd(botK, Range(-1, -premises.length - 1, -1), conjunctsK)), premises)
    }

    def apply(using lib: Library, proof: lib.Proof)(premises: proof.Fact*)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequents = premises.map(proof.getSequent(_))
      lazy val pivots = premiseSequents.map(_.right.diff(bot.right))

      if (premises.length == 0) proof.InvalidProofTactic(s"Premises expected, ${premises.length} received.")
      else if (pivots.exists(_.isEmpty)) {
        val emptyIndex = pivots.indexWhere(_.isEmpty)
        if (F.isSubset(premiseSequents(emptyIndex).left, bot.left))
          unwrapTactic(Weakening(premises(emptyIndex))(bot))("Attempted weakening on trivial premise for RightAnd failed.")
        else
          proof.InvalidProofTactic("Left-hand side of conclusion is not a superset of the one of the premises.")
      } else if (pivots.forall(_.tail.isEmpty))
        RightAnd.withParameters(pivots.map(_.head)*)(premises*)(bot)
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
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Expr[F.Prop], psi: F.Expr[F.Prop])(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      lazy val phiK = phi.underlying
      lazy val psiK = psi.underlying
      lazy val botK = bot.underlying
      lazy val phiAndPsi = phiK \/ psiK

      if (!K.isSameSet(botK.left, premiseSequent.left))
        proof.InvalidProofTactic("Left-hand side of the premise is not the same as the left-hand side of the conclusion.")
      else if (
        !K.isSameSet(botK.right + phiK, premiseSequent.right + phiAndPsi) &&
        !K.isSameSet(botK.right + psiK, premiseSequent.right + phiAndPsi) &&
        !K.isSameSet(botK.right + phiK + psiK, premiseSequent.right + phiAndPsi)
      )
        proof.InvalidProofTactic("Right-hand side of premise + φ∧ψ is not the same as right-hand side of conclusion + either φ, ψ or both.")
      else
        proof.ValidProofTactic(bot, Seq(K.RightOr(botK, -1, phiK, psiK)), Seq(premise))
    }
    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = bot.right.diff(premiseSequent.right)

      if (!pivot.isEmpty && pivot.tail.isEmpty)
        pivot.head match {
          case F.App(F.App(F.or, phi), psi) =>
            if (premiseSequent.left.contains(phi))
              RightOr.withParameters(phi, psi)(premise)(bot)
            else
              RightOr.withParameters(psi, phi)(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not infer a disjunction as pivot from premise and conclusion.")
        }
      else
        // try a rewrite, if it works, go ahead with it, otherwise malformed
        if (F.isSameSequent(premiseSequent, bot))
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
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Expr[F.Prop], psi: F.Expr[F.Prop])(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      lazy val phiK = phi.underlying
      lazy val psiK = psi.underlying
      lazy val botK = bot.underlying
      lazy val implication = phiK ==> psiK

      if (!K.isSameSet(botK.left + phiK, premiseSequent.left))
        proof.InvalidProofTactic("Left-hand side of conclusion + φ is not the same as left-hand side of premise.")
      else if (!K.isSameSet(botK.right + psiK, premiseSequent.right + implication))
        proof.InvalidProofTactic("Right-hand side of conclusion + ψ is not the same as right-hand side of premise + φ⇒ψ.")
      else
        proof.ValidProofTactic(bot, Seq(K.RightImplies(botK, -1, phiK, psiK)), Seq(premise))
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
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
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Expr[F.Prop], psi: F.Expr[F.Prop])(prem1: proof.Fact, prem2: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val leftSequent = proof.getSequent(prem1).underlying
      lazy val rightSequent = proof.getSequent(prem2).underlying
      lazy val phiK = phi.underlying
      lazy val psiK = psi.underlying
      lazy val botK = bot.underlying
      lazy val implication = phiK <=> psiK
      lazy val impLeft = phiK ==> psiK
      lazy val impRight = psiK ==> phiK

      if (!K.isSameSet(botK.left, leftSequent.left union rightSequent.left))
        proof.InvalidProofTactic("Left-hand side of conclusion is not the union of the left-hand sides of the premises.")
      else if (!K.isSubset(leftSequent.right, botK.right + impLeft))
        proof.InvalidProofTactic(
          "Conclusion is missing the following formulas from the left premise: " + (leftSequent.right -- botK.right).map(f => s"[${f.repr}]").reduce(_ ++ ", " ++ _)
        )
      else if (!K.isSubset(rightSequent.right, botK.right + impRight))
        proof.InvalidProofTactic(
          "Conclusion is missing the following formulas from the right premise: " + (rightSequent.right -- botK.right).map(f => s"[${f.repr}]").reduce(_ ++ ", " ++ _)
        )
      else if (!K.isSubset(botK.right, leftSequent.right union rightSequent.right + implication))
        proof.InvalidProofTactic(
          "Conclusion has extraneous formulas apart from premises and implication: " ++ (botK.right
            .removedAll(leftSequent.right union rightSequent.right + implication))
            .map(f => s"[${f.repr}]")
            .reduce(_ ++ ", " ++ _)
        )
      else
        proof.ValidProofTactic(bot, Seq(K.RightIff(botK, -1, -2, phiK, psiK)), Seq(prem1, prem2))
    }

    def apply(using lib: Library, proof: lib.Proof)(prem1: proof.Fact, prem2: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(prem1)
      lazy val pivot = premiseSequent.right.diff(bot.right)

      if (pivot.isEmpty)
        if (F.isSubset(premiseSequent.left, bot.left))
          unwrapTactic(Weakening(prem1)(bot))("Attempted weakening on trivial premise for RightIff failed.")
        else
          proof.InvalidProofTactic("Left-hand side of conclusion is not a superset of the premises.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case F.App(F.App(F.implies, phi), psi) => RightIff.withParameters(phi, psi)(prem1, prem2)(bot)
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
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Expr[F.Prop])(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      lazy val phiK = phi.underlying
      lazy val botK = bot.underlying
      lazy val negation = !phiK

      if (!K.isSameSet(botK.left + phiK, premiseSequent.left))
        proof.InvalidProofTactic("Left-hand side of conclusion + φ is not the same as left-hand side of premise.")
      else if (!K.isSameSet(botK.right, premiseSequent.right + negation))
        proof.InvalidProofTactic("Right-hand side of conclusion is not the same as right-hand side of premise + ¬φ.")
      else
        proof.ValidProofTactic(bot, Seq(K.RightNot(botK, -1, phiK)), Seq(premise))
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = premiseSequent.left.diff(bot.left)

      if (pivot.isEmpty)
        if (F.isSubset(premiseSequent.right, bot.right))
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
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Expr[F.Prop], x: F.Variable[F.Ind])(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      lazy val xK = x.underlying
      lazy val phiK = phi.underlying
      lazy val botK = bot.underlying
      lazy val quantified = K.forall(xK, phiK)

      if ((botK.left union botK.right).exists(_.freeVariables.contains(xK)))
        proof.InvalidProofTactic("The variable x is free in the resulting sequent.")
      else if (!K.isSameSet(botK.left, premiseSequent.left))
        proof.InvalidProofTactic("Left-hand side of conclusion is not the same as left-hand side of premise.")
      else if (!K.isSameSet(botK.right + phiK, premiseSequent.right + quantified))
        proof.InvalidProofTactic("Right-hand side of conclusion + φ is not the same as right-hand side of premise + ∀x. φ.")
      else
        proof.ValidProofTactic(bot, Seq(K.RightForall(botK, -1, phiK, xK)), Seq(premise))
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = bot.right.diff(premiseSequent.right)
      lazy val instantiatedPivot = premiseSequent.right.diff(bot.right)

      if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty)
          if (F.isSameSequent(premiseSequent, bot))
            unwrapTactic(Rewrite(premise)(bot))("Attempted rewrite on trivial premise for RightForall failed.")
          else
            proof.InvalidProofTactic("Could not infer a pivot from the premise and conclusion.")
        else if (instantiatedPivot.tail.isEmpty) {
          val in: F.Expr[F.Prop] = instantiatedPivot.head
          val quantifiedPhi: Option[F.Expr[F.Prop]] = bot.right.find(f =>
            f match {
              case F.forall(_, g) => F.isSame(g, in)
              case _ => false
            }
          )

          quantifiedPhi match {
            case Some(F.forall(x, phi)) => RightForall.withParameters(phi, x)(premise)(bot)
            case _ => proof.InvalidProofTactic("Could not infer a universally quantified pivot from premise and conclusion.")
          }
        } else proof.InvalidProofTactic("Right-hand side of conclusion + φ is not the same as right-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case F.forall(x, phi) => RightForall.withParameters(phi, x)(premise)(bot)
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
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Expr[F.Prop], x: F.Variable[F.Ind], t: F.Expr[F.Ind])(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      lazy val xK = x.underlying
      lazy val tK = t.underlying
      lazy val phiK = phi.underlying
      lazy val botK = bot.underlying
      lazy val quantified = K.exists(xK, phiK)
      lazy val instantiated = K.substituteVariables(phiK, Map(xK -> tK))

      if (!K.isSameSet(botK.left, premiseSequent.left))
        proof.InvalidProofTactic("Left-hand side of conclusion is not the same as left-hand side of premise")
      else if (!K.isSameSet(botK.right + instantiated, premiseSequent.right + quantified))
        proof.InvalidProofTactic("Right-hand side of conclusion + φ[t/x] is not the same as right-hand side of premise + ∃x. φ")
      else
        proof.ValidProofTactic(bot, Seq(K.RightExists(botK, -1, phiK, xK, tK)), Seq(premise))
    }

    def withParameters(using lib: Library, proof: lib.Proof)(t: F.Expr[F.Ind])(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = bot.right.diff(premiseSequent.right)
      lazy val instantiatedPivot = premiseSequent.right.diff(bot.right)

      if (!pivot.isEmpty)
        if (pivot.tail.isEmpty)
          pivot.head match {
            case F.exists(x, phi) => RightExists.withParameters(phi, x, t)(premise)(bot)
            case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
          }
        else
          proof.InvalidProofTactic("Right-hand side of conclusion + φ[t/x] is not the same as right-hand side of premise + ∃x. φ.")
      else if (instantiatedPivot.isEmpty)
        if (F.isSubset(premiseSequent.left, bot.left))
          unwrapTactic(Weakening(premise)(bot))("Attempted weakening on trivial premise for RightExists failed.")
        else
          proof.InvalidProofTactic("Left-hand side of conclusion is not a superset of the premises.")
      else if (instantiatedPivot.tail.isEmpty) {
        // go through conclusion to find a matching quantified formula

        val in: F.Expr[F.Prop] = instantiatedPivot.head
        val quantifiedPhi: Option[F.Expr[F.Prop]] = bot.right.find(f =>
          f match {
            case g @ F.exists(v, e) => F.isSame(e.substitute(v := t), in)
            case _ => false
          }
        )

        quantifiedPhi match {
          case Some(F.exists(x, phi)) => RightExists.withParameters(phi, x, t)(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not match discovered quantified pivot with premise.")
        }
      } else proof.InvalidProofTactic("Right-hand side of conclusion + φ[t/x] is not the same as right-hand side of premise + ∃x. φ.")
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val prepivot = bot.right.diff(premiseSequent.right)
      lazy val pivot = if (prepivot.isEmpty) bot.right else prepivot
      lazy val instantiatedPivot = premiseSequent.right.diff(bot.right)

      if (instantiatedPivot.isEmpty)
        if (F.isSubset(premiseSequent.left, bot.left))
          unwrapTactic(Weakening(premise)(bot))("Attempted weakening on trivial premise for RightForall failed.")
        else
          proof.InvalidProofTactic("Left-hand side of conclusion is not a superset of the premises.")
      else if (instantiatedPivot.tail.isEmpty) {
        // go through conclusion to find a matching quantified formula

        val in: F.Expr[F.Prop] = instantiatedPivot.head

        val quantifiedPhi: Option[(F.Expr[F.Prop], Substitution)] = pivot.collectFirstDefined(f =>
          f match {
            case g @ F.exists(x, phi) =>
              val ctx = RewriteContext.withBound(phi.freeVars - x)
              matchExpr(using ctx)(phi, in).map(f -> _)
            case _ => None
          }
        )

        quantifiedPhi match {
          case Some((F.exists(x, phi), subst)) =>
            RightExists.withParameters(phi, x, subst(x).getOrElse(x))(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not match discovered quantified pivot with premise.")
        }
      } else proof.InvalidProofTactic("Right-hand side of conclusion + φ[t/x] is not the same as right-hand side of premise + ∃x. φ.")
    }
  }

  /*
  /**
   * <pre>
   *  Γ |- ∃y.∀x. (x=y) ⇔ φ, Δ
   * ---------------------------- if y is not free in φ
   *      Γ|- ∃!x. φ,  Δ
   * </pre>
   */
  object RightExistsOne extends ProofTactic with ProofFactSequentTactic {
    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Expr[F.Prop], x: F.Variable)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      lazy val xK = x.underlying
      lazy val phiK = phi.underlying
      lazy val botK = bot.underlying
      lazy val y = K.Variable(lisa.utils.KernelHelpers.freshId(phiK.freeVariables.map(_.id), x.id))
      lazy val instantiated = K.BinderFormula(
        K.Exists,
        y,
        K.BinderFormula(
          K.Forall,
          xK,
          K.ConnectorFormula(K.Iff, Seq(K.AtomicFormula(K.equality, Seq(K.VariableTerm(xK), K.VariableTerm(y))), phiK))
        )
      )
      lazy val quantified = K.BinderFormula(K.ExistsOne, xK, phiK)

      if (!K.isSameSet(botK.left, premiseSequent.left))
        proof.InvalidProofTactic("Left-hand side of conclusion is not the same as left-hand side of premise.")
      else if (!K.isSameSet(botK.right + instantiated, premiseSequent.right + quantified))
        proof.InvalidProofTactic("Right-hand side of conclusion + ∃y.∀x. (x=y) ⇔ φ is not the same as right-hand side of premise + ∃!x. φ.")
      else
        proof.ValidProofTactic(bot, Seq(K.RightExistsOne(botK, -1, phiK, xK)), Seq(premise))
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)
      lazy val pivot = bot.right.diff(premiseSequent.right)
      lazy val instantiatedPivot = premiseSequent.right.diff(bot.right)

      if (pivot.isEmpty)
        if (instantiatedPivot.isEmpty)
          if (F.isSameSequent(premiseSequent, bot))
            unwrapTactic(Rewrite(premise)(bot))("Attempted rewrite on trivial premise for RightExistsOne failed.")
          else
            proof.InvalidProofTactic("Could not infer a pivot from premise and conclusion.")
        else if (instantiatedPivot.tail.isEmpty) {
          instantiatedPivot.head match {
            // ∃_. ∀x. _ ⇔ φ == extract ==> x, phi
            case F.exists(_, F.forall(x, F.AppliedConnector(F.Iff, Seq(_, phi)))) =>
              RightExistsOne.withParameters(phi, x)(premise)(bot)
            case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
          }
        } else
          proof.InvalidProofTactic("Right-hand side of conclusion + φ is not the same as right-hand side of premise + ∃x. φ.")
      else if (pivot.tail.isEmpty)
        pivot.head match {
          case F.BinderFormula(F.ExistsOne, x, phi) => RightExistsOne.withParameters(phi, x)(premise)(bot)
          case _ => proof.InvalidProofTactic("Could not infer an existentially quantified pivot from premise and conclusion.")
        }
      else
        proof.InvalidProofTactic("Right-hand side of conclusion + φ is not the same as right-hand side of premise + ∃x. φ.")
    }
  }

   */

  /**
   * <pre>
   *       Γ |- φ[t/x], Δ
   * --------------------------
   *     Γ|- φ[(εx. φ)/x], Δ
   * </pre>
   *
   * Note that if Δ contains φ[(εx. φ)/x] as well, the parameter inference will
   * fail. In that case, use [[RightEpsilon.withParameters]] instead.
   */
  object RightEpsilon extends ProofTactic with ProofFactSequentTactic {
    def collectEpsilons(in: F.Expr[?]): Set[F.Expr[F.Ind]] =
      in.collect { case e @ F.ε(_, _) => e.asInstanceOf[F.Expr[F.Ind]] }.toSet

    def withParameters(using lib: Library, proof: lib.Proof)(phi: F.Expr[F.Prop], x: F.Variable[F.Ind], t: F.Expr[F.Ind])(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      lazy val xK = x.underlying
      lazy val tK = t.underlying
      lazy val phiK = phi.underlying
      lazy val botK = bot.underlying
      lazy val epsilonTerm = K.epsilon(xK, phiK)
      lazy val instantiated = K.substituteVariables(phiK, Map(xK -> tK))
      lazy val bound = K.substituteVariables(phiK, Map(xK -> epsilonTerm))

      if (!K.isSameSet(botK.left, premiseSequent.left))
        proof.InvalidProofTactic("Left-hand side of conclusion is not the same as left-hand side of premise.")
      else if (!K.isSameSet(botK.right + instantiated, premiseSequent.right + bound))
        proof.InvalidProofTactic("Right-hand side of conclusion + φ[t/x] is not the same as right-hand side of premise + φ[(εx. φ)/x].")
      else
        proof.ValidProofTactic(bot, Seq(K.RightEpsilon(botK, -1, phiK, xK, tK)), Seq(premise))
    }
    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement =
      val premiseSequent = proof.getSequent(premise)
      val pivotSet = premiseSequent.right -- bot.right
      val targetSet = bot.right -- premiseSequent.right

      inline def theFailure =
        proof.InvalidProofTactic("Could not infer an epsilon pivot from premise and conclusion.")

      if pivotSet.size == 0 || targetSet.size == 0 then theFailure
      else if pivotSet.size == 1 && targetSet.size == 1 then
        val pivot = pivotSet.head
        val target = targetSet.head

        // the new binding is one of these
        val epsilons = collectEpsilons(target)

        val newBindingOption = epsilons.collectFirstDefined:
          case eps @ F.ε(x, phi) =>
            val substituted = phi.substitute(x := eps)
            if F.isSame(substituted, target) then Some(eps) else None
          case _ => None

        newBindingOption match
          case Some(F.ε(x, phi)) =>
            // match pivot with phi to discover t
            val pivotMatch = matchExpr(using RewriteContext.withBound(phi.freeVars - x))(phi, pivot)
            pivotMatch match
              case Some(subst) =>
                val t = subst(x).getOrElse(x)
                RightEpsilon.withParameters(phi, x, t)(premise)(bot)
              case _ => theFailure
          case _ => theFailure
      else theFailure
  }

  object Beta extends ProofTactic with ProofFactSequentTactic {

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      val botK = bot.underlying
      val red1 = K.sequentToFormula(botK).betaNormalForm
      val red2 = K.sequentToFormula(proof.getSequent(premise).underlying).betaNormalForm
      if (!K.isSame(red1, red2))
        proof.InvalidProofTactic("The conclusion is not beta-OL-equivalent to the premise.")
      else
        proof.ValidProofTactic(bot, Seq(K.Beta(botK, -1)), Seq(premise))
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
    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise)

      if (!F.isImplyingSequent(premiseSequent, bot))
        proof.InvalidProofTactic("Conclusion cannot be trivially derived from premise.")
      else
        proof.ValidProofTactic(bot, Seq(K.Weakening(bot.underlying, -1)), Seq(premise))
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
    def withParameters(using lib: Library, proof: lib.Proof)(fa: F.Expr[F.Prop])(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      lazy val faK = fa.underlying
      lazy val botK = bot.underlying

      if (!K.isSameSet(botK.left + faK, premiseSequent.left) || !premiseSequent.left.exists(_ == faK) || botK.left.exists(_ == faK))
        proof.InvalidProofTactic("Left-hand sides of the conclusion + φ is not the same as left-hand side of the premise.")
      else if (!K.isSameSet(botK.right, premiseSequent.right))
        proof.InvalidProofTactic("Right-hand side of the premise is not the same as the right-hand side of the conclusion.")
      else
        faK match {
          case K.Application(K.Application(K.equality, left), right) =>
            if (K.isSame(left, right))
              proof.ValidProofTactic(bot, Seq(K.LeftRefl(botK, -1, faK)), Seq(premise))
            else
              proof.InvalidProofTactic("φ is not an instance of reflexivity.")
          case _ => proof.InvalidProofTactic("φ is not an equality.")
        }
    }

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
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
    def withParameters(using lib: Library, proof: lib.Proof)(fa: F.Expr[F.Prop])(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val faK = fa.underlying
      lazy val botK = bot.underlying
      if (!botK.right.exists(_ == faK))
        proof.InvalidProofTactic("Right-hand side of conclusion does not contain φ.")
      else
        faK match {
          case K.Application(K.Application(K.equality, left), right) =>
            if (K.isSame(left, right))
              proof.ValidProofTactic(bot, Seq(K.RightRefl(botK, faK)), Seq())
            else
              proof.InvalidProofTactic("φ is not an instance of reflexivity.")
          case _ => proof.InvalidProofTactic("φ is not an equality.")
        }
    }

    def apply(using lib: Library, proof: lib.Proof)(bot: F.Sequent): proof.ProofTacticJudgement = {
      if (bot.right.isEmpty) proof.InvalidProofTactic("Right-hand side of conclusion does not contain an instance of reflexivity.")
      else {
        // go through conclusion to see if you can find an reflexive formula
        val pivot: Option[F.Expr[F.Prop]] = bot.right.find(f =>
          val Eq = F.equality // (F.equality: (F.|->[F.**[F.Expr[F.Ind], 2], F.Expr[F.Prop]]))
          f match {
            case F.App(F.App(e, l), r) =>
              (F.equality) == (e) && l == r // termequality
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
   *   Γ, φ(s) |- Δ     Σ |- s=t, Π
   * --------------------------------
   *        Γ, Σ φ(t) |- Δ, Π
   * </pre>
   */
  object LeftSubstEq extends ProofTactic {
    @deprecated("Use withParameters instead", "0.9")
    def withParametersSimple(using
        lib: Library,
        proof: lib.Proof
    )(
        equals: Seq[(F.Expr[F.Ind], F.Expr[F.Ind])],
        lambdaPhi: (Seq[F.Variable[?]], F.Expr[F.Prop])
    )(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      withParameters(equals, lambdaPhi)(premise)(bot)
    }

    def withParameters(using
        lib: Library,
        proof: lib.Proof
    )(
        equals: Seq[(F.Expr[?], F.Expr[?])],
        lambdaPhi: (Seq[F.Variable[?]], F.Expr[F.Prop])
    )(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      lazy val botK = bot.underlying
      lazy val equalsK = equals.map(p => (p._1.underlying, p._2.underlying))
      lazy val lambdaPhiK = (lambdaPhi._1.map(_.underlying), lambdaPhi._2.underlying)

      val (s_es, t_es) = equalsK.unzip
      val (phi_args, phi_body) = lambdaPhiK
      if (phi_args.size != s_es.size) // Not strictly necessary, but it's a good sanity check. To reactivate when tactics have been modified.
        proof.InvalidProofTactic("The number of arguments of φ must be the same as the number of equalities.")
      else if (equals.zip(phi_args).exists { case ((s, t), arg) => s.sort != arg.sort || t.sort != arg.sort })
        proof.InvalidProofTactic("The arities of symbols in φ must be the same as the arities of equalities.")
      else {
        val phi_s_for_f = K.substituteVariables(phi_body, (phi_args zip s_es).toMap)
        val phi_t_for_f = K.substituteVariables(phi_body, (phi_args zip t_es).toMap)
        val sEqT_es = equalsK map { case (s, t) =>
          val no = (s.freeVariables ++ t.freeVariables).view.map(_.id.no).max + 1
          val vars = (no until no + s.sort.depth).map(i => K.Variable(K.Identifier("x", i), K.Ind))
          val inner1 = vars.foldLeft(s)(_(_))
          val inner2 = vars.foldLeft(t)(_(_))
          val base = if (inner1.sort == K.Prop) K.iff(inner1)(inner2) else K.equality(inner1)(inner2)
          vars.foldLeft(base: K.Expression) { case (acc, s_arg) => K.forall(s_arg, acc) }
        }

        if (K.isSameSet(botK.right, premiseSequent.right)) then
          if (
            K.isSameSet(botK.left + phi_t_for_f, premiseSequent.left ++ sEqT_es + phi_s_for_f) ||
            K.isSameSet(botK.left + phi_s_for_f, premiseSequent.left ++ sEqT_es + phi_t_for_f)
          )
            proof.ValidProofTactic(bot, Seq(K.LeftSubstEq(botK, -1, equalsK, lambdaPhiK)), Seq(premise))
          else
            proof.InvalidProofTactic("Left-hand sides of the conclusion + φ(s_) must be the same as left-hand side of the premise + (s=t)_ + φ(t_) (or with s_ and t_ swapped).")
        else proof.InvalidProofTactic("Right-hand sides of the premise and the conclusion aren't the same.")
      }
    }
  }

  /**
   * <pre>
   *  Γ |- φ(s), Δ     Σ |- s=t, Π
   * ---------------------------------
   *         Γ, Σ |- φ(t), Δ, Π
   * </pre>
   */
  object RightSubstEq extends ProofTactic {
    @deprecated("Use withParameters instead", "0.9")
    def withParametersSimple(using
        lib: Library,
        proof: lib.Proof
    )(
        equals: Seq[(F.Expr[F.Ind], F.Expr[F.Ind])],
        lambdaPhi: (Seq[F.Variable[?]], F.Expr[F.Prop])
    )(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      withParameters(equals, lambdaPhi)(premise)(bot)
    }

    def withParameters(using
        lib: Library,
        proof: lib.Proof
    )(
        equals: Seq[(F.Expr[?], F.Expr[?])],
        lambdaPhi: (Seq[F.Variable[?]], F.Expr[F.Prop])
    )(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lazy val premiseSequent = proof.getSequent(premise).underlying
      lazy val botK = bot.underlying
      lazy val equalsK = equals.map(p => (p._1.underlying, p._2.underlying))
      lazy val lambdaPhiK = (lambdaPhi._1.map(_.underlying), lambdaPhi._2.underlying)

      val (s_es, t_es) = equalsK.unzip
      val (phi_args, phi_body) = lambdaPhiK
      if (phi_args.size != s_es.size) // Not strictly necessary, but it's a good sanity check. To reactivate when tactics have been modified.
        proof.InvalidProofTactic("The number of arguments of φ must be the same as the number of equalities.")
      else if (equals.zip(phi_args).exists { case ((s, t), arg) => s.sort != arg.sort || t.sort != arg.sort })
        proof.InvalidProofTactic("The arities of symbols in φ must be the same as the arities of equalities.")
      else {
        val phi_s_for_f = K.substituteVariables(phi_body, (phi_args zip s_es).toMap)
        val phi_t_for_f = K.substituteVariables(phi_body, (phi_args zip t_es).toMap)
        val sEqT_es = equalsK map { case (s, t) =>
          val no = (s.freeVariables ++ t.freeVariables).view.map(_.id.no).maxOption.getOrElse(-1) + 1
          val vars = (no until no + s.sort.depth).map(i => K.Variable(K.Identifier("x", i), K.Ind))
          val inner1 = vars.foldLeft(s)(_(_))
          val inner2 = vars.foldLeft(t)(_(_))
          val base = if (inner1.sort == K.Prop) K.iff(inner1)(inner2) else K.equality(inner1)(inner2)
          vars.foldLeft(base: K.Expression) { case (acc, s_arg) => K.forall(s_arg, acc) }
        }

        if (K.isSameSet(botK.left, premiseSequent.left ++ sEqT_es))
          if (
            K.isSameSet(botK.right + phi_t_for_f, premiseSequent.right + phi_s_for_f) ||
            K.isSameSet(botK.right + phi_s_for_f, premiseSequent.right + phi_t_for_f)
          )
            proof.ValidProofTactic(bot, Seq(K.RightSubstEq(botK, -1, equalsK, lambdaPhiK)), Seq(premise))
          else
            proof.InvalidProofTactic("Right-hand side of the premise and the conclusion should be the same with each containing one of φ(s_) φ(t_), but it isn't the case.")
        else proof.InvalidProofTactic("Left-hand sides of the premise + (s=t)_ must be the same as left-hand side of the premise.")
      }
    }
  }

  @deprecated("Use LeftSubstEq instead", "0.9")
  val LeftSubstIff = LeftSubstEq
  @deprecated("Use RightSubstEq instead", "0.9")
  val RightSubstIff = RightSubstEq

  /**
   * <pre>
   *           Γ |- Δ
   * --------------------------
   *  Γ[r(a)/?f] |- Δ[r(a)/?f]
   * </pre>
   */
  object InstSchema extends ProofTactic {
    def unsafe(using lib: Library, proof: lib.Proof)(map: Map[F.Variable[?], F.Expr[?]])(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement =
      val premiseSequent = proof.getSequent(premise).underlying
      val mapK = map.map((v, e) => (v.underlying, e.underlying))
      val botK = K.substituteVariablesInSequent(premiseSequent, mapK)
      val res = proof.getSequent(premise).substituteUnsafe(map)
      proof.ValidProofTactic(res, Seq(K.InstSchema(botK, -1, mapK)), Seq(premise))

    def apply(using lib: Library, proof: lib.Proof)(subst: F.SubstPair*)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement =
      val map = subst.map(p => (p._1, p._2)).toMap
      unsafe(using lib, proof)(map)(premise)(bot)

  }

  class SUBPROOF(using val proof: Library#Proof)(statement: Option[F.Sequent])(val iProof: proof.InnerProof) extends ProofTactic {
    val bot: Option[F.Sequent] = statement
    val botK: Option[K.Sequent] = statement map (_.underlying)
    val scproof: Option[K.SCProof] = if (iProof.length == 0) then None else Some(iProof.toSCProof)

    val premises: Seq[proof.Fact] = iProof.getImports.map(of => of._1)
    def judgement: proof.ProofTacticJudgement = {
      if (iProof.length == 0)
        proof.InvalidProofTactic(s"Subproof is empty.")
      else if (botK.isEmpty)
        proof.ValidProofTactic(iProof.mostRecentStep.bot, scproof.get.steps, premises)
      else if (!K.isSameSequent(botK.get, scproof.get.conclusion))
        proof.InvalidProofTactic(s"The subproof does not prove the desired conclusion.\n\tExpected: ${botK.get.repr}\n\tObtained: ${scproof.get.conclusion.repr}")
      else
        proof.ValidProofTactic(bot.get, scproof.get.steps :+ K.Restate(botK.get, scproof.get.length - 1), premises)
    }
  }

  // TODO make specific support for subproofs written inside tactics.kkkkkkk

  inline def TacticSubproof(using proof: Library#Proof)(inline computeProof: proof.InnerProof ?=> Unit): proof.ProofTacticJudgement =
    val iProof: proof.InnerProof = new proof.InnerProof(None)
    computeProof(using iProof)
    SUBPROOF(using proof)(None)(iProof).judgement.asInstanceOf[proof.ProofTacticJudgement]

  object Sorry extends ProofTactic with ProofSequentTactic {
    def apply(using lib: Library, proof: lib.Proof)(bot: F.Sequent): proof.ProofTacticJudgement = {
      proof.ValidProofTactic(bot, Seq(K.Sorry(bot.underlying)), Seq())
    }
  }

}
