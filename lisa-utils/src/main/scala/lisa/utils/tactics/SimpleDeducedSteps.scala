package lisa.utils.tactics

import lisa.kernel.fol.FOL
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SCProofChecker
import lisa.kernel.proof.SequentCalculus.RewriteTrue
import lisa.kernel.proof.SequentCalculus.SCProofStep
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.kernel.proof.SequentCalculus as SC
import lisa.utils.Helpers.{*, given}
import lisa.utils.{Library, LisaException, OutputManager}
import lisa.utils.tactics.ProofTacticLib.{*, given}

object SimpleDeducedSteps {

  final class Restate(using val proof: Library#Proof) extends ProofTacticWithoutBot with ProofTacticWithoutBotNorPrem(1) {
    override val premises: Seq[Int] = Seq()
    def asSCProof(premMap: proof.Fact => Int, bot: Sequent): ProofTacticJudgement =
      SC.RewriteTrue(bot)

    def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement =
      SC.Rewrite(bot, premises(0))

  }
  def Restate(using _proof: Library#Proof): Restate{val proof: _proof.type} = (new Restate(using _proof)).asInstanceOf



  final class Discharge(using val proof: Library#Proof) extends ProofTacticWithoutPrem(1) {
    override def asSCProof(premises: Seq[Int]): ProofTacticJudgement = {
      val s = proof.getSequent(premises(0))
      if (s.right.size == 1) {
        val f = s.right.head
        val t1 = premises(0)
        val (lastStep, t2) = proof.mostRecentStep
        SC.Cut((lastStep.bot -< f) ++ (proof.getSequent(t1) -> f), t1, t2, f)
      } else {
        ProofTacticJudgement.InvalidProofTactic(this.asProofTactic(premises), "When discharging this way, the target sequent must have only a single formula on the right handside.")
      }
    }
  }

  def Discharge(using proof: Library#Proof)(ij: Library#Proof#Fact) = new Discharge

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
  final class InstantiateForall(using val proof: Library#Proof)(phi: FOL.Formula, t: FOL.Term) extends ProofTacticWithoutPrem(1) with ProofTacticWithoutBotNorPrem(1) {
    override val numbPrem = 1

    override def asSCProof(premises: Seq[Int]): ProofTacticJudgement = {
      phi match {
        case psi @ FOL.BinderFormula(FOL.Forall, _, _) => {
          val in = instantiateBinder(psi, t)
          this.asSCProof(proof.getSequent(premises(0)) -> phi +> in, premises)
        }
        case _ => ProofTacticJudgement.InvalidProofTactic(this.asProofTacticWithoutBot(premises).asProofTactic(() |- ()), "Input formula is not universally quantified")
      }
    }

    override def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premises(0))
      if (premiseSequent.right.contains(phi)) {
        // valid derivation, construct proof
        phi match {
          case psi @ FOL.BinderFormula(FOL.Forall, _, _) => {
            val tempVar = FOL.VariableLabel(FOL.freshId(psi.freeVariables.map(_.id), "x"))
            // instantiate the formula with input
            val in = instantiateBinder(psi, t)
            // construct proof
            val p0 = SC.Hypothesis(in |- in, in)
            val p1 = SC.LeftForall(phi |- in, 0, instantiateBinder(psi, tempVar), tempVar, t)
            val p2 = SC.Cut(bot, -1, 1, phi)
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
            SC.SCSubproof(SCProof(IndexedSeq(p0, p1, p2), IndexedSeq(premiseSequent)), Seq(premises(0)))
          }
          case _ => ProofTacticJudgement.InvalidProofTactic(this.asProofTacticWithoutBot(premises).asProofTactic(bot), "Input formula is not universally quantified")
        }
      } else ProofTacticJudgement.InvalidProofTactic(this.asProofTacticWithoutBot(premises).asProofTactic(bot), "Input formula was not found in the RHS of the premise sequent.")
    }
  }

  def InstantiateForall(using proof: Library#Proof)(phi: FOL.Formula, t: FOL.Term) = new InstantiateForall(phi, t)

  /**
   * Instantiate universal quantifier, with only one formula in the RHS
   *
   * The premise is a proof of φ (phi), with φ (phi) of the form ∀x.ψ,
   *
   * Asserts φ (phi) as the sole formula in the RHS of the premise's conclusion
   *
   * t is the term to instantiate the quantifier with
   *
   * <pre>
   *         Γ ⊢ ∀x.ψ
   * -------------------------
   *       Γ |- ψ[t/x]
   *
   * </pre>
   *
   * Returns a subproof containing the instantiation steps
   */
  final class InstantiateForallWithoutFormula(using val proof: Library#Proof)(t: FOL.Term) extends ProofTacticWithoutPrem(1) with ProofTacticWithoutBotNorPrem(1) {

    override val numbPrem = 1

    override def asSCProof(premises: Seq[Int]): ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premises(0))

      if (premiseSequent.right.tail.isEmpty)
        new InstantiateForall(premiseSequent.right.head, t).asSCProof(premises)
      else
        ProofTacticJudgement.InvalidProofTactic(this.asProofTactic(premises), "RHS of premise sequent is not a singleton.")
    }

    override def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement = {
      val premiseSequent = proof.getSequent(premises(0))

      if (premiseSequent.right.tail.isEmpty) {
        // well formed
        new InstantiateForall(premiseSequent.right.head, t).asSCProof(bot, premises)
      } else ProofTacticJudgement.InvalidProofTactic(this.asProofTacticWithoutBot(premises).asProofTactic(bot), "RHS of premise sequent is not a singleton.")

    }
  }

  /**
   * Instantiate multiple universal quantifiers
   *
   * The premise is a proof of φ (phi), with φ (phi) of the form ∀x1, x2, ..., xn.ψ,
   *
   * t* are the terms to instantiate the quantifiers
   *
   * Asserts t*.length = n
   *
   * Returns a subproof containing individual instantiations as its subproof steps
   *
   * <pre>
   *          Γ ⊢ ∀x1, x2, ..., xn .ψ, Δ
   * --------------------------------------------
   *     Γ |- ψ[t1/x1, t2/x2, ..., tn/xn], Δ
   *
   * </pre>
   */
  final class InstantiateForallMultiple(using val proof: Library#Proof)(phi: FOL.Formula, t: FOL.Term*) extends ProofTacticWithoutPrem(1) with ProofTacticWithoutBotNorPrem(1) {
    override val numbPrem = 1

    override def asSCProof(premises: Seq[Int]): ProofTacticJudgement = {

      val premiseSequent = proof.getSequent(premises(0))

      if (!premiseSequent.right.contains(phi)) {
        ProofTacticJudgement.InvalidProofTactic(this.asProofTactic(premises), "Input formula was not found in the RHS of the premise sequent.")
      } else {
        val emptyProof = SCProof(IndexedSeq(), IndexedSeq(proof.getSequent(premises(0))))
        val j = ProofTacticJudgement.ValidProofTactic(SC.Rewrite(premiseSequent, premises(0)))

        // some unfortunate code reuse
        // ProofStep tactics cannot be composed easily at the moment

        val res = t.foldLeft((emptyProof, phi, j: ProofTacticJudgement)) {
          case ((p, f, j), t) => {
            j match {
              case ProofTacticJudgement.InvalidProofTactic(_, _) => (p, f, j) // propagate error
              case ProofTacticJudgement.ValidProofTactic(_) => {
                // good state, continue instantiating

                // by construction the premise is well-formed

                // verify the formula structure and instantiate
                f match {
                  case psi @ FOL.BinderFormula(FOL.Forall, _, _) => {

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
                  }
                  case _ => {
                    (
                      p,
                      f,
                      ProofTacticJudgement.InvalidProofTactic(this.asProofTactic(premises), "Input formula is not universally quantified")
                    )
                  }
                }
              }
            }
          }
        }

        res._3 match {
          case ProofTacticJudgement.InvalidProofTactic(_, _) => res._3
          case ProofTacticJudgement.ValidProofTactic(_) => SC.SCSubproof(res._1, Seq(premises(0)))
        }
      }
    }

    override def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement = {
      val res = this.asSCProof(premises)

      res match {
        case ProofTacticJudgement.InvalidProofTactic(_, _) => res
        case ProofTacticJudgement.ValidProofTactic(SC.SCSubproof(proof: SCProof, _)) => {
          // check if the same sequent was obtained
          SC.SCSubproof(
            proof withNewSteps IndexedSeq(SC.Rewrite(bot, proof.length - 1)),
            Seq(premises(0))
          )
        }
        case _ => ProofTacticJudgement.InvalidProofTactic(this.asProofTacticWithoutBot(premises).asProofTactic(bot), "Unreachable pattern match")
      }
    }

  }

  /**
   * Instantiate multiple universal quantifiers, with only one formula in the RHS
   *
   * The premise is a proof of φ (phi), with φ (phi) of the form ∀x1, x2, ..., xn.ψ,
   *
   * Asserts φ (phi) is the sole formula in the RHS of the conclusion of the premise
   *
   * t* are the terms to instantiate the quantifiers
   *
   * Asserts t*.length = n
   *
   * Returns a subproof containing individual instantiations as its subproof steps
   *
   * <pre>
   *          Γ ⊢ ∀x1, x2, ..., xn .ψ
   * --------------------------------------------
   *      Γ |- ψ[t1/x1, t2/x2, ..., tn/xn]
   *
   * </pre>
   */
  final class InstantiateForallMultipleWithoutFormula(using val proof: Library#Proof)(t: FOL.Term*) extends ProofTacticWithoutPrem(1) with ProofTacticWithoutBotNorPrem(1) {
    override val numbPrem = 1
    override def asSCProof(premises: Seq[Int]): ProofTacticJudgement = {
      val prem = proof.getSequent(premises(0))
      if (prem.right.tail.isEmpty) {
        // well formed
        InstantiateForall(using proof)(prem.right.head, t: _*).asSCProof(premises)
      } else ProofTacticJudgement.InvalidProofTactic(this.asProofTactic(premises), "RHS of premise sequent is not a singleton.")
    }

    override def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement = {
      val prem = proof.getSequent(premises(0))
      if (prem.right.tail.isEmpty) {
        // well formed
        InstantiateForall(using proof)(prem.right.head, t: _*).asSCProof(bot, premises)
      } else ProofTacticJudgement.InvalidProofTactic(this.asProofTacticWithoutBot(premises).asProofTactic(bot), "RHS of premise sequent is not a singleton.")
    }
  }

  def InstantiateForall(using proof: Library#Proof)(t: FOL.Term) = new InstantiateForallWithoutFormula(t)
  def InstantiateForall(using proof: Library#Proof)(phi: FOL.Formula, t: FOL.Term*) = new InstantiateForallMultiple(phi, t: _*)
  def InstantiateForall(using proof: Library#Proof)(t: FOL.Term*) = new InstantiateForallMultipleWithoutFormula(t: _*)


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
  final class PartialCut(using val proof: Library#Proof)(phi: FOL.Formula, conjunction: FOL.Formula) extends ProofTacticWithoutBotNorPrem(2) {
    override def asSCProof(bot: Sequent, premises: Seq[Int]): ProofTacticJudgement = {

      def invalid(message: String) = ProofTacticJudgement.InvalidProofTactic(this.asProofTacticWithoutBot(premises).asProofTactic(bot), message)

      val leftSequent = proof.getSequent(premises(0))
      val rightSequent = proof.getSequent(premises(1))

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

                SC.SCSubproof(SCProof(IndexedSeq(p0, p1, p2, p3, p4), IndexedSeq(leftSequent, rightSequent)), premises.take(2))
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
