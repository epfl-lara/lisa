package lisa.utils.tactics

import lisa.kernel.fol.FOL
import lisa.kernel.proof.{SCProof, SCProofChecker, SequentCalculus as SC}
import lisa.kernel.proof.SequentCalculus.{RewriteTrue, RightForall, SCProofStep, Sequent}
import lisa.utils.Helpers.*
import lisa.utils.Helpers.{*, given}
import lisa.utils.{Library, OutputManager, Printer}
import lisa.utils.tactics.BasicStepTactic.SCSubproof
import lisa.utils.tactics.ProofStepLib.{*, given}

object SimpleDeducedSteps {

  extension[T <: (ProofStepWithoutPrem with ProofStepWithoutBotNorPrem[1]) | (ProofStepWithoutPrem with ProofStepWithoutBotNorPrem[2])] (pr : T) {
    private def asSCProofAuto(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      val res = pr.asSCProof(premises, currentProof)

      res match {
        case ProofStepJudgement.InvalidProofStep(_, _) => res
        case ProofStepJudgement.ValidProofStep(SC.SCSubproof(proof: SCProof, _)) =>
          SC.SCSubproof(
            proof withNewSteps IndexedSeq(SC.Rewrite(bot, proof.length - 1)),
            Seq(premises.head)
          )
        case _ => ProofStepJudgement.InvalidProofStep(pr.asProofStepWithoutBot(premises).asProofStep(bot), "Unreachable pattern match")
      }
    }
  }

  case object Restate extends ProofStepWithoutBot with ProofStepWithoutBotNorPrem(1) {
    override val premises: Seq[Int] = Seq()
    def asSCProof(bot: Sequent, currentProof: Library#Proof): ProofStepJudgement =
      SC.RewriteTrue(bot)

    def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement =
      SC.Rewrite(bot, premises(0))

  }

  case class FormulaDischarge(f: FOL.Formula) extends ProofStepWithoutPrem {
    override def asSCProof(premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      val t1 = premises(0)
      val (lastStep, t2) = currentProof.mostRecentStep
      SC.Cut((lastStep.bot -< f) ++ (currentProof.getSequent(t1) -> f), t1, t2, f)
    }
  }

  class SUBPROOF(computeProof: => Unit)(using om: OutputManager) extends ProofStepWithoutBot {
    private def cp(): Unit = computeProof
    val premises: Seq[lisa.utils.Library#Proof#Fact] = Seq()

    override def asSCProof(bot: Sequent, currentProof: Library#Proof): ProofStepJudgement = {
      val proof = currentProof.subproof(cp())
      val scproof = proof.toSCProof
      val check = SCProofChecker.checkSCProof(scproof)
      if (!check.isValid) check.showAndGet
      SC.SCSubproof(scproof, proof.getImports.map(imf => imf.reference.asInstanceOf[Int]))
    }
  }

  case object Discharge extends ProofStepWithoutPrem {
    override def asSCProof(premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      val s = currentProof.getSequent(premises(0))
      if (s.right.size == 1) {
        val f = s.right.head
        val t1 = premises(0)
        val (lastStep, t2) = currentProof.mostRecentStep
        SC.Cut((lastStep.bot -< f) ++ (currentProof.getSequent(t1) -> f), t1, t2, f)
      } else {
        ProofStepJudgement.InvalidProofStep(this.asProofStep(premises), "When discharging this way, the target sequent must have only a single formula on the right handside.")
      }
    }
    def apply(f: FOL.Formula): FormulaDischarge = FormulaDischarge(f)
    def apply(ij: Library#Proof#Fact)(using library: Library)(using om: OutputManager): Unit = {
      if (library.proofStack.head.validInThisProof(ij)) {
        Discharge.asProofStep(Seq(ij)).validate(library)
      } else {
        val inv = ProofStepJudgement.InvalidProofStep(Discharge.asProofStep(Seq(ij)), "Illegal reference to justification from another proof in proofstep Discharge.")
        om.finishOutput(inv.launch)
      }
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
  case class InstantiateForall(phi: FOL.Formula, t: FOL.Term) extends ProofStepWithoutPrem with ProofStepWithoutBotNorPrem(1) {

    override def asSCProof(premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {

      phi match {
        case psi @ FOL.BinderFormula(FOL.Forall, _, _) => {
          val in = instantiateBinder(psi, t)

          this.asSCProof(currentProof.getSequent(premises(0)) -> phi +> in, premises, currentProof)
        }
        case _ => ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(() |- ()), "Input formula is not universally quantified")
      }

    }

    override def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {

      val premiseSequent = currentProof.getSequent(premises(0))

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
          case _ => ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Input formula is not universally quantified")
        }
      } else ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "Input formula was not found in the RHS of the premise sequent.")
    }
  }

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
  case class InstantiateForallWithoutFormula(t: FOL.Term) extends ProofStepWithoutPrem with ProofStepWithoutBotNorPrem(1) {

    override def asSCProof(premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      val premiseSequent = currentProof.getSequent(premises(0))

      if (premiseSequent.right.tail.isEmpty)
        InstantiateForall(premiseSequent.right.head, t).asSCProof(premises, currentProof)
      else
        ProofStepJudgement.InvalidProofStep(this.asProofStep(premises), "RHS of premise sequent is not a singleton.")
    }

    override def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      val premiseSequent = currentProof.getSequent(premises(0))

      if (premiseSequent.right.tail.isEmpty) {
        // well formed
        InstantiateForall(premiseSequent.right.head, t).asSCProof(bot, premises, currentProof)
      } else ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "RHS of premise sequent is not a singleton.")

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
  case class InstantiateForallMultiple(phi: FOL.Formula, t: FOL.Term*) extends ProofStepWithoutPrem with ProofStepWithoutBotNorPrem(1) {
    override def asSCProof(premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {

      val premiseSequent = currentProof.getSequent(premises(0))

      if (!premiseSequent.right.contains(phi)) {
        ProofStepJudgement.InvalidProofStep(this.asProofStep(premises), "Input formula was not found in the RHS of the premise sequent.")
      } else {
        val emptyProof = SCProof(IndexedSeq(), IndexedSeq(currentProof.getSequent(premises(0))))
        val j = ProofStepJudgement.ValidProofStep(SC.Rewrite(premiseSequent, premises(0)))

        // some unfortunate code reuse
        // DoubleStep tactics cannot be composed easily at the moment

        val res = t.foldLeft((emptyProof, phi, j: ProofStepJudgement)) {
          case ((p, f, j), t) => {
            j match {
              case ProofStepJudgement.InvalidProofStep(_, _) => (p, f, j) // propagate error
              case ProofStepJudgement.ValidProofStep(_) => {
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
                      ProofStepJudgement.InvalidProofStep(this.asProofStep(premises), "Input formula is not universally quantified")
                    )
                  }
                }
              }
            }
          }
        }

        res._3 match {
          case ProofStepJudgement.InvalidProofStep(_, _) => res._3
          case ProofStepJudgement.ValidProofStep(_) => SC.SCSubproof(res._1, Seq(premises(0)))
        }
      }
    }

    override def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = asSCProofAuto(this)(bot, premises, currentProof)

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
  case class InstantiateForallMultipleWithoutFormula(t: FOL.Term*) extends ProofStepWithoutPrem with ProofStepWithoutBotNorPrem(1) {
    override def asSCProof(premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {

      val prem = currentProof.getSequent(premises(0))

      if (prem.right.tail.isEmpty) {
        // well formed
        InstantiateForall(prem.right.head, t: _*).asSCProof(premises, currentProof)
      } else ProofStepJudgement.InvalidProofStep(this.asProofStep(premises), "RHS of premise sequent is not a singleton.")

    }

    override def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {

      val prem = currentProof.getSequent(premises(0))

      if (prem.right.tail.isEmpty) {
        // well formed
        InstantiateForall(prem.right.head, t: _*).asSCProof(bot, premises, currentProof)
      } else ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "RHS of premise sequent is not a singleton.")

    }

  }

  /**
   * Overload instantiation for ease of use
   *
   * Generates a proof step of the relevant type
   */
  object InstantiateForall {

    // default, automatic
    // def apply(phi: FOL.Formula, t: FOL.Term) = InstantiateForall(phi, t)
    def apply(t: FOL.Term) = InstantiateForallWithoutFormula(t)
    def apply(phi: FOL.Formula, t: FOL.Term*) = InstantiateForallMultiple(phi, t: _*)
    def apply(t: FOL.Term*) = InstantiateForallMultipleWithoutFormula(t: _*)
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
  case class PartialCut(phi: FOL.Formula, conjunction: FOL.Formula) extends ProofStepWithoutBotNorPrem(2) {
    override def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {

      def invalid(message: String) = ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), message)

      val leftSequent = currentProof.getSequent(premises(0))
      val rightSequent = currentProof.getSequent(premises(1))

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

  case class ByEquiv(f: FOL.Formula, f1: FOL.Formula) extends ProofStepWithoutPrem with ProofStepWithoutBotNorPrem(2) {
    override def asSCProof(premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      premises match {
        case Nil | _ +: Nil => ProofStepJudgement.InvalidProofStep(this.asProofStep(premises), "Not enough premises : " + premises)
        case _ => {

          val prem1 = currentProof.getSequent(premises.head)
          val prem2 = currentProof.getSequent(premises.tail.head)
          f match {
            case FOL.ConnectorFormula(FOL.Iff, Seq(fl, fr)) =>
              val pr1 = Seq(prem1, prem2).find(st => st.right.contains(f1))
              val pEq = Seq(prem1, prem2).find(st => st.right.contains(f))

              if (pr1.isEmpty || pEq.isEmpty)
                return ProofStepJudgement.InvalidProofStep(this.asProofStep(premises),
                  "Input formula is not present in given premises : \n" + Printer.prettySequent(prem1) + "\n"
                    + Printer.prettySequent(prem2) + "\n"
                    + " But not : " + Printer.prettyFormula(f1) + "\n" + Printer.prettyFormula(f))

              val f2 = if (FOL.isSame(f1, fl)) fr else if (FOL.isSame(f1, fr)) fl else {
                return ProofStepJudgement.InvalidProofStep(this.asProofStep(premises), "Formulas not the sames")
              }


              val p2 = SC.Hypothesis(emptySeq +< f1 +> f1, f1) // () |- f2
              val p3 = SC.Hypothesis(emptySeq +< f2 +> f2, f2) // () |- f2
              val p4 = SC.LeftImplies(Sequent(Set(f1, f1 ==> f2), Set(f2)), 0, 1, f1, f2) // f1, f1 ==> f2 |- f2
              val p5 = SC.LeftIff(Sequent(Set(f1, f1 <=> f2), Set(f2)), 2, f1, f2) // f1, f1 <=> f2 |- f2
              val p6 = SC.Cut(pEq.get -> (f1 <=> f2) +< f1 +> f2, -2, 3, f1 <=> f2) // f1 |- f2, f1
              val p7 = SC.Cut(p6.bot -< f1 ++ pr1.get -> f1, -1, 4, f1) //() |- f2

              SC.SCSubproof(SCProof(IndexedSeq( p2, p3, p4, p5, p6, p7), IndexedSeq(pEq.get, pr1.get)), premises.take(2))

            case _ => ProofStepJudgement.InvalidProofStep(this.asProofStep(premises), "Input formula is not an Iff")
          }
        }
      }
    }

      override def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = asSCProofAuto(this)(bot, premises, currentProof)
    }

  case class GeneralizeToForallWithoutFormula(t : FOL.VariableLabel*) extends ProofStepWithoutPrem with ProofStepWithoutBotNorPrem(1) {
    override def asSCProof(premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      if (currentProof.getSequent(premises.head).right.tail.isEmpty)
        GeneralizeToForallMultiple(currentProof.getSequent(premises.head).right.head, t:_*).asSCProof(premises, currentProof)
      else
        ProofStepJudgement.InvalidProofStep(this.asProofStep(premises), "RHS of premise sequent is not a singleton.")

    }

    override def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      if (bot.right.tail.isEmpty)
        GeneralizeToForallMultiple(currentProof.getSequent(premises.head).right.head, t:_*).asSCProof(bot, premises, currentProof)
      else
        ProofStepJudgement.InvalidProofStep(this.asProofStepWithoutBot(premises).asProofStep(bot), "RHS of premise sequent is not a singleton.")

    }
  }


  case class GeneralizeToForallMultiple(phi : FOL.Formula, t: FOL.VariableLabel*) extends ProofStepWithoutPrem with ProofStepWithoutBotNorPrem(1) {
    override def asSCProof(premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      if (currentProof.getSequent(premises.head).right.contains(phi)) {
        val premiseSequent = currentProof.getSequent(premises.head)
        val emptyProof = SCProof(IndexedSeq(), IndexedSeq(currentProof.getSequent(premises.head)))
        val j = ProofStepJudgement.ValidProofStep(SC.Rewrite(premiseSequent, premises.head))

        val res = t.foldRight(emptyProof : SCProof, phi : FOL.Formula, j: ProofStepJudgement) {
            case (x1, (p1 : SCProof, phi1, j1)) =>
              j1 match {
                  case ProofStepJudgement.InvalidProofStep (_, _) => (p1, phi1, j1)
                  case ProofStepJudgement.ValidProofStep(_) => {
                    if (!p1.conclusion.right.contains(phi1))
                      (p1, phi1, ProofStepJudgement.InvalidProofStep(this.asProofStep(premises), "Formula is not present in the lass sequent"))

                    val proofStep = SC.RightForall(p1.conclusion -> phi1 +> forall(x1, phi1), p1.length - 1, phi1, x1)
                    (
                      p1 appended proofStep,
                      forall(x1, phi1),
                      j1
                    )
                  }
              }
        }

        res._3 match {
          case ProofStepJudgement.InvalidProofStep(_, _) => res._3
          case ProofStepJudgement.ValidProofStep(_) => SC.SCSubproof(res._1, Seq(premises.head))
        }

      } else
        ProofStepJudgement.InvalidProofStep(this.asProofStep(premises), "RHS of premise sequent contains not phi")

    }

    override def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = asSCProofAuto(this)(bot, premises, currentProof)

  }

  object GeneralizeToForall {

    def apply(phi: FOL.Formula, t: FOL.VariableLabel) = GeneralizeToForallMultiple(phi, t)

    def apply(phi: FOL.Formula, t: FOL.VariableLabel*) = GeneralizeToForallMultiple(phi, t: _*)

    def apply(t: FOL.VariableLabel*) = GeneralizeToForallWithoutFormula(t: _*)
  }


  case class ByCase(phi: FOL.Formula) extends ProofStepWithoutPrem with ProofStepWithoutBotNorPrem(2) {
    override def asSCProof(premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = {
      val nphi = !phi

      val pa = currentProof.getSequent(premises.head)
      val pb = currentProof.getSequent(premises.tail.head)
      val (leftAphi, leftBnphi) = (pa.left.find(FOL.isSame(_, phi)), pb.left.find(FOL.isSame(_, nphi)))
      if (leftAphi.nonEmpty && leftBnphi.nonEmpty) {
        val p2 = SC.RightNot(pa -< leftAphi.get +> nphi, -2, phi)
        val p3 = SC.Cut(pa -< leftAphi.get ++ (pb -< leftBnphi.get), 1, -1, nphi)
        SC.SCSubproof(SCProof(IndexedSeq(p2, p3), IndexedSeq(pa, pb)), premises) //TODO: Check pa/pb orDer

      } else {
        ProofStepJudgement.InvalidProofStep(this.asProofStep(premises), "Premises have not the right syntax")
      }
    }

    override def asSCProof(bot: Sequent, premises: Seq[Int], currentProof: Library#Proof): ProofStepJudgement = asSCProofAuto(this)(bot, premises, currentProof)
  }

}

