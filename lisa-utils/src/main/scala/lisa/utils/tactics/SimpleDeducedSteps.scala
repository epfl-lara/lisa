package lisa.utils.tactics

import lisa.kernel.fol.FOL
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SCProofChecker
import lisa.kernel.proof.SequentCalculus.RewriteTrue
import lisa.kernel.proof.SequentCalculus.SCProofStep
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.kernel.proof.SequentCalculus as SC
import lisa.utils.Helpers.{_, given}
import lisa.utils.Library
import lisa.utils.LisaException
import lisa.utils.OutputManager
import lisa.utils.tactics.ProofTacticLib.{_, given}

object SimpleDeducedSteps {

  object Restate extends ProofTactic with ParameterlessHave with ParameterlessAndThen {
    def apply(using proof: Library#Proof)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.RewriteTrue(bot)), Nil)

    // (proof.ProofStep | proof.OutsideFact | Int)     is definitionally equal to proof.Fact, but for some reason
    // scala compiler doesn't resolve the overload with a type alias, dependant type and implicit parameter

    def apply(using proof: Library#Proof)(premise: proof.ProofStep | proof.OutsideFact | Int)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.Rewrite(bot, -1)), Seq(premise))

    def apply2(using proof: Library#Proof)(premise: proof.ProofStep | proof.OutsideFact | Int)(bot: Sequent): proof.ProofTacticJudgement =
      proof.ValidProofTactic(Seq(SC.Rewrite(bot, -1)), Seq(premise))

  }

  object Discharge extends ProofTactic {
    def apply(using proof: Library#Proof)(premises: proof.Fact*): proof.ProofTacticJudgement = {
      val seqs = premises map proof.getSequent
      if (!seqs.forall(_.right.size == 1))
        return proof.InvalidProofTactic("When discharging this way, the discharged sequent must have only a single formula on the right handside.")
      val s = seqs.head
      val f = s.right.head
      val first = SC.Cut((proof.mostRecentStep.bot -< f) ++ (s -> f), -1, -2, f)

      proof.ValidProofTactic(
        first +: seqs.tail.zipWithIndex.scanLeft(first)((prev, next) => {
          val f = next._1.right.head
          SC.Cut((prev.bot -< f) ++ (next._1 -> f), next._2, -next._2 - 3, f)
        }),
        proof.mostRecentStep +: premises
      )
    }

  }

  /**
   * Instantiate universal quantifier
   *
   * The premise is a proof of φ (phi), with φ (phi) of the form ∀x.ψ
   *
   * t is the term to instantiate the quantifier with
   *
   * <pre>
   *       Γ ⊢ ∀x.ψ, Δ
   * -------------------------
   *     Γ |- ψ[t/x], Δ
   *
   * </pre>
   *
   * Returns a subproof containing the instantiation steps
   */
  object InstantiateForall extends ProofTactic {
    def apply(using proof: Library#Proof)(phi: FOL.Formula, t: FOL.Term*)(premise: proof.Fact): proof.ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premise)
      if (!premiseSequent.right.contains(phi)) {
        proof.InvalidProofTactic("Input formula was not found in the RHS of the premise sequent.")
      } else {
        val emptyProof = SCProof(IndexedSeq(), IndexedSeq(proof.getSequent(-1)))
        val j = proof.ValidProofTactic(Seq(SC.Rewrite(premiseSequent, -1)), Seq(premise))
        // some unfortunate code reuse
        // ProofStep tactics cannot be composed easily at the moment
        val res = t.foldLeft((emptyProof, phi, j: proof.ProofTacticJudgement)) { case ((p, f, j), t) =>
          j match {
            case proof.InvalidProofTactic(_) => (p, f, j) // propagate error
            case proof.ValidProofTactic(_, _) =>
              // good state, continue instantiating
              // by construction the premise is well-formed
              // verify the formula structure and instantiate
              f match {
                case psi @ FOL.BinderFormula(FOL.Forall, _, _) =>
                  val tempVar = FOL.VariableLabel(FOL.freshId(psi.freeVariables.map(_.id), "x"))
                  // instantiate the formula with input
                  val in = instantiateBinder(psi, t)
                  val bot = p.conclusion -> f +> in
                  // construct proof
                  val p0 = SC.Hypothesis(in |- in, in)
                  val p1 = SC.LeftForall(f |- in, 0, instantiateBinder(psi, tempVar), tempVar, t)
                  val p2 = SC.Cut(bot, -1, 1, f)

                  /**
                   * in  = ψ[t/x]
                   *
                   * s1  = Γ ⊢ ∀x.ψ, Δ        Premise
                   * bot = Γ ⊢ ψ[t/x], Δ      Result
                   *
                   * p0  = ψ[t/x] ⊢ ψ[t/x]    Hypothesis
                   * p1  = ∀x.ψ ⊢ ψ[t/x]      LeftForall p0
                   * p2  = Γ ⊢ ψ[t/x], Δ      Cut s1, p1
                   */
                  val newStep = SC.SCSubproof(SCProof(IndexedSeq(p0, p1, p2), IndexedSeq(p.conclusion)), Seq(p.length - 1))
                  (
                    p withNewSteps IndexedSeq(newStep),
                    in,
                    j
                  )
                case _ =>
                  (p, f, proof.InvalidProofTactic("Input formula is not universally quantified"))
              }
          }
        }

        res._3 match {
          case proof.InvalidProofTactic(_) => res._3
          case proof.ValidProofTactic(_, _) => proof.ValidProofTactic(Seq(SC.SCSubproof(res._1, Seq(-1))), Seq(premise))
        }
      }
    }

    def apply(using proof: Library#Proof)(t: FOL.Term*)(premise: proof.Fact): proof.ProofTacticJudgement = {
      val prem = proof.getSequent(premise)
      if (prem.right.tail.isEmpty) {
        // well formed
        apply(using proof)(prem.right.head, t*)(premise): proof.ProofTacticJudgement
      } else proof.InvalidProofTactic("RHS of premise sequent is not a singleton.")
    }
  }

  /**
   * Performs a cut when the formula to be used as pivot for the cut is
   * inside a conjunction, preserving the conjunction structure
   *
   * <pre>
   *
   * PartialCut(ϕ, ϕ ∧ ψ)(left, right) :
   *
   *     left: Γ ⊢ ϕ ∧ ψ, Δ      right: ϕ, Σ ⊢ γ1 , γ2, …, γn
   * -----------------------------------------------------------
   *            Γ, Σ ⊢ Δ, ψ ∧ γ1, ψ ∧ γ2, … , ψ ∧ γn
   *
   * </pre>
   */
  object PartialCut extends ProofTactic {
    def apply(using proof: Library#Proof)(phi: FOL.Formula, conjunction: FOL.Formula)(prem1: proof.Fact, prem2: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {

      def invalid(message: String) = proof.InvalidProofTactic(message)

      val leftSequent = proof.getSequent(prem1)
      val rightSequent = proof.getSequent(prem2)

      if (leftSequent.right.contains(conjunction)) {

        if (rightSequent.left.contains(phi)) {
          // check conjunction matches with phi
          conjunction match {
            case FOL.ConnectorFormula(FOL.And, s: Seq[FOL.Formula]) => {
              if (s.contains(phi)) {
                // construct proof

                val psi: Seq[FOL.Formula] = s.filterNot(_ == phi)
                val newConclusions: Set[FOL.Formula] = rightSequent.right.map((f: FOL.Formula) => FOL.ConnectorFormula(FOL.And, f +: psi))

                val Sigma: Set[FOL.Formula] = rightSequent.left - phi

                val p0 = SC.Weakening(rightSequent ++< (psi |- ()), -2)
                val p1 = SC.RewriteTrue(psi |- psi)

                // TODO: can be abstracted into a RightAndAll step
                val emptyProof = SCProof(IndexedSeq(), IndexedSeq(p0.bot, p1.bot))
                val proofRightAndAll = rightSequent.right.foldLeft(emptyProof) { case (p, gamma) =>
                  p withNewSteps IndexedSeq(SC.RightAnd(p.conclusion -> gamma +> FOL.ConnectorFormula(FOL.And, gamma +: psi), Seq(p.length - 1, -2), gamma +: psi))
                }

                val p2 = SC.SCSubproof(proofRightAndAll, Seq(0, 1))
                val p3 = SC.Rewrite(Sigma + conjunction |- newConclusions, 2) // sanity check and correct form
                val p4 = SC.Cut(bot, -1, 3, conjunction)

                /**
                 * newConclusions = ψ ∧ γ1, ψ ∧ γ2, … , ψ ∧ γn
                 *
                 * left   = Γ ⊢ ϕ ∧ ψ, Δ                              Premise
                 * right  = ϕ, Σ ⊢ γ1 , γ2, …, γn                     Premise
                 *
                 * p0     = ϕ, Σ, ψ ⊢ γ1 , γ2, …, γn                  Weakening on right
                 * p1     = ψ ⊢ ψ                                     Hypothesis
                 * p2     = Subproof:
                 *          2.1 = ϕ, Σ, ψ ⊢ ψ ∧ γ1 , γ2, …, γn        RightAnd on p0 and p1 with ψ ∧ γ1
                 *          2.2 = ϕ, Σ, ψ ⊢ ψ ∧ γ1 , ψ ∧ γ2, …, γn    RightAnd on 2.1 and p1 ψ ∧ γ2
                 *          ...
                 *          2.n = ϕ, Σ, ψ ⊢ ψ ∧ γ1, ψ ∧ γ2, …, ψ ∧ γn RightAnd on 2.(n-1) and p1 with ψ ∧ γn
                 *
                 * p3     = ϕ ∧ ψ, Σ ⊢ ψ ∧ γ1, ψ ∧ γ2, … , ψ ∧ γn     Rewrite on p2 (just to have a cleaner form)
                 * p2     = Γ, Σ ⊢ Δ, ψ ∧ γ1, ψ ∧ γ2, … , ψ ∧ γn      Cut on left, p1 with ϕ ∧ ψ
                 *
                 * p2 is the result
                 */

                proof.ValidProofTactic(IndexedSeq(p0, p1, p2, p3, p4), Seq(prem1, prem2))
              } else {
                invalid("Input conjunction does not contain the pivot.")
              }
            }
            case _ => invalid("Input not a conjunction.")
          }
        } else {
          invalid("Input pivot formula not found in right premise.")
        }
      } else {
        invalid("Input conjunction not found in first premise.")
      }
    }
  }

}
