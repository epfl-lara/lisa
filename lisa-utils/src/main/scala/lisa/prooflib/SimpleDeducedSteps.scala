package lisa.prooflib

import lisa.fol.FOLHelpers.*
import lisa.fol.FOL as F
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.ProofTacticLib.{_, given}
import lisa.prooflib.*
import lisa.utils.FOLParser
import lisa.utils.K
import lisa.utils.KernelHelpers.{_, given}
import lisa.utils.Printer

object SimpleDeducedSteps {

  object simpleFunctionDefinition extends ProofTactic {

    def apply[N <: Arity](using lib: Library, proof: lib.Proof)(expression: F.LambdaExpression[F.Term, F.Term, N], out: F.Variable) = {
      val scp = {
        import K.{*, given}
        val x = out.underlyingLabel
        val LambdaTermTerm(vars, body) = expression.underlyingLTT
        val xeb = x === body
        val y = VariableLabel(freshId(body.freeVariables.map(_.id) ++ vars.map(_.id) + out.id, "y"))
        val s0 = K.RightRefl(() |- body === body, body === body)
        val s1 = K.Restate(() |- (xeb) <=> (xeb), 0)
        val s2 = K.RightForall(() |- forall(x, (xeb) <=> (xeb)), 1, (xeb) <=> (xeb), x)
        val s3 = K.RightExists(() |- exists(y, forall(x, (x === y) <=> (xeb))), 2, forall(x, (x === y) <=> (xeb)), y, body)
        val s4 = K.Restate(() |- existsOne(x, xeb), 3)
        Vector(s0, s1, s2, s3, s4)
      }
      proof.ValidProofTactic(F.Sequent(Set(), Set(F.ExistsOne(out, out === expression.body))), scp, Seq())
    }

  }

  object Restate extends ProofTactic with ProofSequentTactic with ProofFactSequentTactic {
    def apply(using lib: Library, proof: lib.Proof)(bot: F.Sequent): proof.ProofTacticJudgement =
      unwrapTactic(RewriteTrue(bot))("Attempted true rewrite during tactic Restate failed.")

    // (proof.ProofStep | proof.OutsideFact | Int)     is definitionally equal to proof.Fact, but for some reason
    // scala compiler doesn't resolve the overload with a type alias, dependant type and implicit parameter

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.ProofStep | proof.OutsideFact | Int | proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement =
      unwrapTactic(Rewrite(premise)(bot))("Attempted rewrite during tactic Restate failed.")

    def from(using lib: Library, proof: lib.Proof)(premise: proof.ProofStep | proof.OutsideFact | Int | proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement =
      unwrapTactic(Rewrite(premise)(bot))("Attempted rewrite during tactic Restate failed.")

  }

  object Discharge extends ProofTactic {
    def apply(using lib: Library, proof: lib.Proof)(premises: proof.Fact*)(premise: proof.Fact): proof.ProofTacticJudgement = {
      val ss = premises map (e => proof.getSequent(e))
      val seqs = ss map (e => e.underlying)
      if (!seqs.forall(_.right.size == 1))
        return proof.InvalidProofTactic("When discharging this way, the discharged sequent must have only a single formula on the right handside.")
      val s = seqs.head
      val f = s.right.head
      val first = K.Cut((proof.getSequent(premise).underlying removeLeft f) ++ (s removeRight f), -2, -1, f)

      proof.ValidProofTactic(
        (proof.getSequent(premise) removeAllLeft (ss.flatMap(_.right).toSet)) ++<< (F.Sequent(ss.flatMap(_.left).toSet, Set())),
        seqs.tail.zipWithIndex.scanLeft(first)((prev, next) => {
          val f = next._1.right.head
          K.Cut((prev.bot removeLeft f) ++ (next._1 removeRight f), -next._2 - 3, next._2, f)
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
   * Γ ⊢ ∀x.ψ, Δ
   * -------------------------
   * Γ |- ψ[t/x], Δ
   *
   * </pre>
   *
   * Returns a subproof containing the instantiation steps
   */
  object InstantiateForall extends ProofTactic with ProofSequentTactic {
    def apply(using lib: Library, proof: lib.Proof)(phi: F.Formula, t: F.Term*)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      val botK = bot.underlying
      val phiK = phi.underlying
      val tK = t map (_.underlying)
      val premiseSequent = proof.getSequent(premise)
      val premiseSequentK = premiseSequent.underlying
      if (!premiseSequent.right.contains(phi)) {
        proof.InvalidProofTactic("Input formula was not found in the RHS of the premise sequent.")
      } else {
        val emptyProof = K.SCProof(IndexedSeq(), IndexedSeq(premiseSequentK))
        val j = proof.ValidProofTactic(bot, Seq(K.Restate(premiseSequentK, -1)), Seq(premise))
        val res = tK.foldLeft((emptyProof, phiK, j: proof.ProofTacticJudgement)) { case ((p, f, j), t) =>
          j match {
            case proof.InvalidProofTactic(_) => (p, f, j) // propagate error
            case proof.ValidProofTactic(_, _, _) =>
              // good state, continue instantiating
              // by construction the premise is well-formed
              // verify the formula structure and instantiate
              f match {
                case psi @ K.BinderFormula(K.Forall, x, _) =>
                  val tempVar = K.VariableLabel(K.freshId(psi.freeVariables.map(_.id), x.id))
                  // instantiate the formula with input
                  val in = instantiateBinder(psi, t)
                  val con = p.conclusion ->> f +>> in
                  // construct proof
                  val p0 = K.Hypothesis(in |- in, in)
                  val p1 = K.LeftForall(f |- in, 0, instantiateBinder(psi, tempVar), tempVar, t)
                  val p2 = K.Cut(con, -1, 1, f)

                  /**
                   * in  = ψ[t/x]
                   *
                   * s1  = Γ ⊢ ∀x.ψ, Δ        Premise
                   * con = Γ ⊢ ψ[t/x], Δ      Result
                   *
                   * p0  = ψ[t/x] ⊢ ψ[t/x]    Hypothesis
                   * p1  = ∀x.ψ ⊢ ψ[t/x]      LeftForall p0
                   * p2  = Γ ⊢ ψ[t/x], Δ      Cut s1, p1
                   */
                  val newStep = K.SCSubproof(K.SCProof(IndexedSeq(p0, p1, p2), IndexedSeq(p.conclusion)), Seq(p.length - 1))
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
          case proof.ValidProofTactic(_, _, _) => {
            if (K.isImplyingSequent(res._1.conclusion, botK))
              proof.ValidProofTactic(bot, Seq(K.SCSubproof(res._1.withNewSteps(IndexedSeq(K.Weakening(botK, res._1.length - 1))), Seq(-1))), Seq(premise))
            else
              proof.InvalidProofTactic(s"InstantiateForall proved \n\t${FOLParser.printSequent(res._1.conclusion)}\ninstead of input sequent\n\t${FOLParser.printSequent(botK)}")
          }
        }
      }
    }

    def apply(using lib: Library, proof: lib.Proof)(t: F.Term*)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      val prem = proof.getSequent(premise)
      if (prem.right.tail.isEmpty) {
        // well formed
        apply(using lib, proof)(prem.right.head, t*)(premise)(bot): proof.ProofTacticJudgement
      } else proof.InvalidProofTactic("RHS of premise sequent is not a singleton.")
    }

    def apply(using lib: Library, proof: lib.Proof)(bot: F.Sequent): proof.ProofTacticJudgement = {
      try {
        val sp = new BasicStepTactic.SUBPROOF(using proof)(Some(bot))({
          // lazy val premiseSequent = proof.getSequent(premise)
          val s1 = proof.library.have(bot +<< bot.right.head) by Restate
          proof.library.have(bot) by LeftForall(s1)
        })
        BasicStepTactic.unwrapTactic(sp.judgement.asInstanceOf[proof.ProofTacticJudgement])("Subproof substitution fail.")
      } catch {
        case e: Exception => proof.InvalidProofTactic("Impossible to justify desired step with instantiation.")
      }

    }

  }
  /*
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
    def apply(using lib: Library, proof: lib.Proof)(phi: K.Formula, conjunction: K.Formula)(prem1: proof.Fact, prem2: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      val leftSequent = proof.getSequent(prem1)
      val rightSequent = proof.getSequent(prem2)

      if (leftSequent.right.contains(conjunction)) {

        if (rightSequent.left.contains(phi)) {
          // check conjunction matches with phi
          conjunction match {
            case K.ConnectorFormula(K.And, s: Seq[K.Formula]) => {
              if (s.contains(phi)) {
                // construct proof

                val psi: Seq[K.Formula] = s.filterNot(_ == phi)
                val newConclusions: Set[K.Formula] = rightSequent.right.map((f: K.Formula) => K.ConnectorFormula(K.And, f +: psi))

                val Sigma: Set[K.Formula] = rightSequent.left - phi

                val p0 = K.Weakening(rightSequent ++<< (psi |- ()), -2)
                val p1 = K.RestateTrue(psi |- psi)

                // TODO: can be abstracted into a RightAndAll step
                val emptyProof = SCProof(IndexedSeq(), IndexedSeq(p0.bot, p1.bot))
                val proofRightAndAll = rightSequent.right.foldLeft(emptyProof) { case (p, gamma) =>
                  p withNewSteps IndexedSeq(K.RightAnd(p.conclusion ->> gamma +>> K.ConnectorFormula(K.And, gamma +: psi), Seq(p.length - 1, -2), gamma +: psi))
                }

                val p2 = K.SCSubproof(proofRightAndAll, Seq(0, 1))
                val p3 = K.Restate(Sigma + conjunction |- newConclusions, 2) // sanity check and correct form
                val p4 = K.Cut(bot, -1, 3, conjunction)

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
                proof.InvalidProofTactic("Input conjunction does not contain the pivot.")
              }
            }
            case _ => proof.InvalidProofTactic("Input not a conjunction.")
          }
        } else {
          proof.InvalidProofTactic("Input pivot formula not found in right premise.")
        }
      } else {
        proof.InvalidProofTactic("Input conjunction not found in first premise.")
      }
    }
  }

  object destructRightAnd extends ProofTactic {
    def apply(using lib: Library, proof: lib.Proof)(a: K.Formula, b: K.Formula)(prem: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      val conc = proof.getSequent(prem)
      val p0 = K.Hypothesis(emptySeq +<< a +>> a, a)
      val p1 = K.LeftAnd(emptySeq +<< (a /\ b) +>> a, 0, a, b)
      val p2 = K.Cut(conc ->> (a /\ b) ->> (b /\ a) +>> a, -1, 1, a /\ b)
      proof.ValidProofTactic(IndexedSeq(p0, p1, p2), Seq(prem))
    }
  }
  object destructRightOr extends ProofTactic {
    def apply(using lib: Library, proof: lib.Proof)(a: K.Formula, b: K.Formula)(prem: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      val conc = proof.getSequent(prem)
      val mat = conc.right.find(f => K.isSame(f, a \/ b))
      if (mat.nonEmpty) {

        val p0 = K.Hypothesis(emptySeq +<< a +>> a, a)
        val p1 = K.Hypothesis(emptySeq +<< b +>> b, b)

        val p2 = K.LeftOr(emptySeq +<< (a \/ b) +>> a +>> b, Seq(0, 1), Seq(a, b))
        val p3 = K.Cut(conc ->> mat.get +>> a +>> b, -1, 2, a \/ b)
        proof.ValidProofTactic(IndexedSeq(p0, p1, p2, p3), Seq(prem))
      } else {
        proof.InvalidProofTactic("Premise does not contain the union of the given formulas")
      }

    }
  }

  object GeneralizeToForall extends ProofTactic {
    def apply(using lib: Library, proof: lib.Proof)(phi: K.Formula, t: K.VariableLabel*)(prem: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      val sequent = proof.getSequent(prem)
      if (sequent.right.contains(phi)) {
        val emptyProof = SCProof(IndexedSeq(), IndexedSeq(sequent))
        val j = proof.ValidProofTactic(IndexedSeq(K.Restate(sequent, proof.length - 1)), Seq[proof.Fact]())

        val res = t.foldRight(emptyProof: SCProof, phi: K.Formula, j: proof.ProofTacticJudgement) { case (x1, (p1: SCProof, phi1, j1)) =>
          j1 match {
            case proof.InvalidProofTactic(_) => (p1, phi1, j1)
            case proof.ValidProofTactic(_, _) => {
              if (!p1.conclusion.right.contains(phi1))
                (p1, phi1, proof.InvalidProofTactic("Formula is not present in the lass sequent"))

              val proofStep = K.RightForall(p1.conclusion ->> phi1 +>> forall(x1, phi1), p1.length - 1, phi1, x1)
              (
                p1 appended proofStep,
                forall(x1, phi1),
                j1
              )
            }
          }
        }

        res._3 match {
          case proof.InvalidProofTactic(_) => res._3
          case proof.ValidProofTactic(_, _) => proof.ValidProofTactic((res._1.steps appended K.Restate(bot, res._1.length - 1)), Seq(prem))
        }

      } else proof.InvalidProofTactic("RHS of premise sequent contains not phi")

    }
  }

  object GeneralizeToForallNoForm extends ProofTactic {
    def apply(using lib: Library, proof: lib.Proof)(t: K.VariableLabel*)(prem: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      if (proof.getSequent(prem).right.tail.isEmpty)
        GeneralizeToForall.apply(using lib, proof)(proof.getSequent(prem).right.head, t*)(prem)(bot): proof.ProofTacticJudgement
      else
        proof.InvalidProofTactic("RHS of premise sequent is not a singleton.")
    }

  }

  object ByCase extends ProofTactic {
    def apply(using lib: Library, proof: lib.Proof)(phi: K.Formula)(prem1: proof.Fact, prem2: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      val nphi = !phi

      val pa = proof.getSequent(prem1)
      val pb = proof.getSequent(prem2)
      val (leftAphi, leftBnphi) = (pa.left.find(K.isSame(_, phi)), pb.left.find(K.isSame(_, nphi)))
      if (leftAphi.nonEmpty && leftBnphi.nonEmpty) {
        val p2 = K.RightNot(pa -<< leftAphi.get +>> nphi, -1, phi)
        val p3 = K.Cut(pa -<< leftAphi.get ++ (pb -<< leftBnphi.get), 0, -2, nphi)
        val p4 = K.Restate(bot, 1)
        proof.ValidProofTactic(IndexedSeq(p2, p3, p4), IndexedSeq(prem1, prem2)) // TODO: Check pa/pb orDer

      } else {
        proof.InvalidProofTactic("Premises have not the right syntax")
      }
    }
  }
   */
}
