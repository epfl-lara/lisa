package lisa.kernel.proof

import lisa.kernel.fol.FOL._
import lisa.kernel.proof.SCProofCheckerJudgement._
import lisa.kernel.proof.SequentCalculus._

object SCProofChecker {

  private def sortMismatch(
    expected: Sort,
    actual: Sort,
    step: SCProofStep
  ): SCInvalidProof = {
    val expectedString = expected match {
      case Prop => "a formula (of sort Prop)"
      case Ind => "a term (of sort Ind)"
      case s => s"an expression of sort ($s)"
    }
    SCInvalidProof(SCProof(step), Nil, s"Expected $expectedString, but found sort ($actual).")
  }

  private def error(step: SCProofStep, message: String): SCInvalidProof = {
    SCInvalidProof(SCProof(step), Nil, message)
  }

  private def variableIsFreeInSequent(sequent: Sequent, variable: Variable): Boolean = {
    (sequent.left union sequent.right).exists(_.freeVariables.contains(variable))
  }


  /**
   * This function verifies that a single SCProofStep is correctly applied. It verifies that the step only refers to sequents with a lower number,
   * and that the type, premises and parameters of the proof step correspond to the claimed conclusion.
   *
   * @param no         The number of the given proof step. Needed to verify that the proof step doesn't refer to steps occuring later in the proof.
   * @param step       The proof step (object) whose correctness needs to be checked.
   * @param references A function that associates sequents to a range of positive and negative integers that the proof step may refer to. Typically,
   *                   a proof's [[SCProof.getSequent]] function.
   * @return           A Judgement about the correctness of the proof step.
   */
  def checkSingleSCStep(no: Int, step: SCProofStep, references: Int => Sequent, importsSize: Int): SCProofCheckerJudgement = {
    val ref = references
    val false_premise = step.premises.find(i => i >= no)
    val false_premise2 = step.premises.find(i => i < -importsSize)

    val r: SCProofCheckerJudgement =
      if (false_premise.nonEmpty)
        SCInvalidProof(SCProof(step), Nil, s"Step #$no can't refer to a higher number #${false_premise.get} as a premise.")
      else if (false_premise2.nonEmpty)
        SCInvalidProof(SCProof(step), Nil, s"A step can't refer to step #${false_premise2.get}, imports only contains ${importsSize} elements.")
      else
        step match {
          /*
           *    Γ |- Δ
           * ------------
           *    Γ |- Δ
           */
          case Restate(s, t1) =>
            if (isSameSequent(ref(t1), s)) SCValidProof(SCProof(step)) else SCInvalidProof(SCProof(step), Nil, s"The premise does not trivially imply the conclusion.")

          /*
           *
           * ------------
           *    Γ |- Γ
           */
          case RestateTrue(s) =>
            val truth = Sequent(Set(), Set(top))
            if (isSameSequent(s, truth)) SCValidProof(SCProof(step)) else SCInvalidProof(SCProof(step), Nil, s"The desired conclusion is not a trivial tautology")
          /*
           *
           * --------------
           *   Γ, φ |- φ, Δ
           */
          case Hypothesis(Sequent(left, right), phi) =>
            // sort check
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            // logical checks
            else if (contains(left, phi))
              if (contains(right, phi)) SCValidProof(SCProof(step))
              else SCInvalidProof(SCProof(step), Nil, s"Right-hand side does not contain formula φ")
            else SCInvalidProof(SCProof(step), Nil, s"Left-hand side does not contain formula φ")

          /*
           *  Γ |- Δ, φ    φ, Σ |- Π
           * ------------------------
           *       Γ, Σ |- Δ, Π
           */
          case Cut(b, t1, t2, phi) =>
            // sort check
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            // logical checks
            else {
              val prem1 = ref(t1)
              val prem2 = ref(t2)

              if (!prem1.right.contains(phi)) 
                error(step, s"First premise does not contain the cut pivot on the right-hand side.")
              else if (!prem2.left.contains(phi))
                error(step, s"Second premise does not contain the cut pivot on the left-hand side.")
              else if (b.left + phi != (prem1.left union prem2.left))
                error(step, s"Left-hand side of conclusion + cut pivot is not the union of the left-hand sides of the premises.")
              else if (b.right + phi != (prem1.right union prem2.right))
                error(step, s"Right-hand side of conclusion + cut pivot is not the union of the right-hand sides of the premises.")
              else {
                SCValidProof(SCProof(step))
              }
            }

          // Left rules
          /*
           *   Γ, φ |- Δ                 Γ, φ, ψ |- Δ
           * --------------     or     -------------
           *  Γ, φ∧ψ |- Δ               Γ, φ∧ψ |- Δ
           */
          case LeftAnd(b, t1, phi, psi) =>
            // sort checks
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            else if (psi.sort != Prop)
              sortMismatch(Prop, psi.sort, step)
            // logical checks
            else {
              val prem1 = ref(t1)
              val phiAndPsi = and(phi)(psi)
              if (prem1.right != b.right) {
                error(step, "Right-hand sides of the premise and the conclusion are not the same.")
              }
              else {
                val targetSet = prem1.left + phiAndPsi
                if (!(targetSet == b.left + phi || targetSet == b.left + psi || targetSet == b.left + phiAndPsi)) {
                  error(step, "Left-hand side of conclusion + the conjunction φ ∧ ψ must be same as left-hand side of premise + either φ, ψ, or both.")
                }
                else {
                  SCValidProof(SCProof(step))
                }
              }
            }
          /*
           *  Γ, φ |- Δ    Σ, ψ |- Π
           * ------------------------
           *    Γ, Σ, φ∨ψ |- Δ, Π
           */
          case LeftOr(b, ts, disjuncts) =>
            // sort checks
            if (disjuncts.exists(phi => phi.sort != Prop)) {
              val culprit = disjuncts.find(phi => phi.sort != Prop).get
              sortMismatch(Prop, culprit.sort, step)
            }
            else if  (ts.size != disjuncts.size) {
              error(step, s"Number of premises (${ts.size}) is not the same as number of disjuncts (${disjuncts.size}).")
            }
            // logical checks
            else {
              val prems = ts.map(ref(_))
              val premsLefts = prems.map(_.left).reduce(_ union _)
              val premsRights = prems.map(_.right).reduce(_ union _)
              val newDisjunct = disjuncts.reduce(or(_)(_))

              // a disjunct which is NOT in the claimed premise
              lazy val violatingDisjunct = prems.zipWithIndex.find({ case (prem, i) =>
                val disjunct = disjuncts(i)
                !prem.left.contains(disjunct)
              }).map(_._2)

              // a premise which is NOT contained in the conclusion
              lazy val violatingSet = prems.zipWithIndex.find({ case (prem, i) =>
                val disjunct = disjuncts(i)
                !prem.left.subsetOf(b.left + disjunct)
              }).map(_._2)

              if (premsRights != b.right) {
                error(step, "Right-hand side of conclusion is not the union of the right-hand sides of the premises.")
              }
              else if (violatingDisjunct.nonEmpty) {
                val idx = violatingDisjunct.get
                error(step, s"Premise #$idx does not contain the corresponding disjunct on the left-hand side.")
              }
              else if (violatingSet.nonEmpty) {
                val idx = violatingSet.get
                error(step, s"Premise #$idx left-hand side is not a subset of the conclusion left-hand side + the corresponding disjunct.")
              }
              else if (b.left.subsetOf(premsLefts + newDisjunct)) {
                error(step, "Left-hand side of conclusion + disjuncts is not a subset of the union of the left-hand sides of the premises.")
              }
              else {
                SCValidProof(SCProof(step))
              }
            }
          /*
           *  Γ |- φ, Δ    Σ, ψ |- Π
           * ------------------------
           *    Γ, Σ, φ⇒ψ |- Δ, Π
           */
          case LeftImplies(b, t1, t2, phi, psi) =>
            // sort checks
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            else if (psi.sort != Prop)
              sortMismatch(Prop, psi.sort, step)
            // logical checks
            else {
              val prem1 = ref(t1)
              val prem2 = ref(t2)
              val phiImpPsi = implies(phi)(psi)

              if ((prem1.right union prem2.right) != (b.right + phi)) {
                error(step, "Right-hand side of conclusion + φ is not the same as the union of the right-hand sides of the premises.")
              }
              else if ((prem1.left union prem2.left) + phiImpPsi != (b.left + psi)) {
                error(step, "Left-hand side of conclusion + ψ is not the same as union of left-hand sides of premises + φ⇒ψ.")
              }
              else {
                SCValidProof(SCProof(step))
              }
            }

          /*
           *  Γ, φ⇒ψ |- Δ               Γ, φ⇒ψ, ψ⇒φ |- Δ
           * --------------    or     ---------------
           *  Γ, φ⇔ψ |- Δ              Γ, φ⇔ψ |- Δ
           */
          case LeftIff(b, t1, phi, psi) =>
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            else if (psi.sort != Prop)
              sortMismatch(Prop, psi.sort, step)
            else {
              val prem1 = ref(t1)
              val phiImpPsi = implies(phi)(psi)
              val psiImpPhi = implies(psi)(phi)
              val phiIffPsi = iff(phi)(psi)

              if (prem1.right != b.right)
                error(step, "Right-hand side of premise is not the same as right-hand side of conclusion.")
              else {
                val targetSet = prem1.left + phiIffPsi
                if (!(targetSet == b.left + phiImpPsi || targetSet == b.left + psiImpPhi || targetSet == b.left + phiImpPsi + psiImpPhi))
                  error(step, "Left-hand side of premise + φ⇔ψ is not the same as left-hand side of conclusion + either φ⇒ψ, ψ⇒φ, or both.")
                else
                  SCValidProof(SCProof(step))
              }
            }

          /*
           *   Γ |- φ, Δ
           * --------------
           *   Γ, ¬φ |- Δ
           */
          case LeftNot(b, t1, phi) =>
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            else {
              val prem1 = ref(t1)
              val nPhi = neg(phi)

              if (b.left != prem1.left + nPhi)
                error(step, "Left-hand side of conclusion is not the same as left-hand side of premise + ¬φ.")
              else if (b.right + phi != prem1.right)
                error(step, "Right-hand side of conclusion + φ is not the same as right-hand side of premise.")
              else
                SCValidProof(SCProof(step))
            }

          /*
           *   Γ, φ[t/x] |- Δ
           * -------------------
           *  Γ, ∀x. φ |- Δ
           */
          case LeftForall(b, t1, phi, x, t) =>
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            else if (x.sort != Ind)
              sortMismatch(Ind, x.sort, step)
            else if (t.sort != Ind)
              sortMismatch(Ind, t.sort, step)
            else {
              val prem1 = ref(t1)
              val quantified = forall(Lambda(x, phi))
              val instantiated = substituteVariables(phi, Map(x -> t))

              if (b.right != prem1.right)
                error(step, "Right-hand side of conclusion is not the same as right-hand side of premise.")
              else if (b.left + instantiated != prem1.left + quantified)
                error(step, "Left-hand side of conclusion + φ[t/x] is not the same as left-hand side of premise + ∀x. φ.")
              else
                SCValidProof(SCProof(step))
            }

          /*
           *    Γ, φ |- Δ
           * ------------------- if x is not free in the resulting sequent
           *  Γ, ∃x. φ |- Δ
           */
          case LeftExists(b, t1, phi, x) =>
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            else if (x.sort != Ind)
              sortMismatch(Ind, x.sort, step)
            else {
              val prem1 = ref(t1)
              val quantified = exists(Lambda(x, phi))

              if (b.right != prem1.right)
                error(step, "Right-hand side of conclusion is not the same as right-hand side of premise.")
              else if (b.left + phi != prem1.left + quantified)
                error(step, "Left-hand side of conclusion + φ is not the same as left-hand side of premise + ∃x. φ.")
              else if (variableIsFreeInSequent(b, x))
                error(step, "Variable x is free in the resulting sequent.")
              else
                SCValidProof(SCProof(step))
            }

          // Right rules
          /*
           *  Γ |- φ, Δ    Σ |- ψ, Π
           * ------------------------
           *    Γ, Σ |- φ∧ψ, Π, Δ
           */
          case RightAnd(b, ts, conjuncts) =>
            if (conjuncts.exists(_.sort != Prop)) {
              val culprit = conjuncts.find(_.sort != Prop).get
              sortMismatch(Prop, culprit.sort, step)
            } else if (ts.size != conjuncts.size) {
              error(step, s"Number of premises (${ts.size}) is not the same as number of conjuncts (${conjuncts.size}).")
            } else {
              val prems = ts.map(ref(_))
              val premiseLeftUnion = prems.map(_.left).reduce(_ union _)
              val premiseRightUnion = prems.map(_.right).reduce(_ union _)
              val conjunction = conjuncts.reduce(and(_)(_))

              // a conjunct which is NOT in the claimed premise
              lazy val violatingConjunct = prems.zipWithIndex.find { case (prem, i) =>
                val conjunct = conjuncts(i)
                !prem.right.contains(conjunct)
              }.map(_._2)

              // a premise which is NOT contained in the conclusion
              val violatingPremise = prems.zipWithIndex.find { case (prem, idx) =>
                !prem.right.subsetOf(b.right + conjuncts(idx))
              }

              if (b.left != premiseLeftUnion)
                error(step, "Left-hand side of conclusion is not the union of the left-hand sides of the premises.")
              else if (violatingConjunct.nonEmpty) {
                val idx = violatingConjunct.get
                error(step, s"Premise #$idx does not contain the corresponding conjunct on the right-hand side.")
              }
              else if (violatingPremise.nonEmpty) {
                val idx = violatingPremise.get._2
                error(step, s"Premise #$idx right-hand side is not a subset of conclusion right-hand side + the corresponding conjunct.")
              }
              else if (!b.right.subsetOf(premiseRightUnion + conjunction))
                error(step, "Right-hand side of conclusion is not a subset of the union of the right-hand sides of the premises + the conjunction.")
              else
                SCValidProof(SCProof(step))
            }
          /*
           *   Γ |- φ, Δ                Γ |- φ, ψ, Δ
           * --------------    or    ---------------
           *  Γ |- φ∨ψ, Δ              Γ |- φ∨ψ, Δ
           */
          case RightOr(b, t1, phi, psi) =>
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            else if (psi.sort != Prop)
              sortMismatch(Prop, psi.sort, step)
            else {
              val prem1 = ref(t1)
              val phiOrPsi = or(phi)(psi)

              if (prem1.left != b.left)
                error(step, "Left-hand side of premise is not the same as left-hand side of conclusion.")
              else {
                val targetSet = prem1.right + phiOrPsi
                if (!(targetSet == b.right + phi || targetSet == b.right + psi || targetSet == b.right + phi + psi))
                error(step, "Right-hand side of premise + φ∨ψ is not the same as right-hand side of conclusion + either φ, ψ, or both.")
                else
                  SCValidProof(SCProof(step))
              }
            }
          /*
           *  Γ, φ |- ψ, Δ
           * --------------
           *  Γ |- φ⇒ψ, Δ
           */
          case RightImplies(b, t1, phi, psi) =>
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            else if (psi.sort != Prop)
              sortMismatch(Prop, psi.sort, step)
            else {
              val prem1 = ref(t1)
              val phiImpPsi = implies(phi)(psi)

              if (b.left + phi != prem1.left)
                error(step, "Left-hand side of conclusion + φ is not the same as left-hand side of premise.")
              else if (b.right + psi != prem1.right + phiImpPsi)
                error(step, "Right-hand side of conclusion + ψ is not the same as right-hand side of premise + φ⇒ψ.")
              else
                SCValidProof(SCProof(step))
            }
          /*
           *  Γ |- φ⇒ψ, Δ    Σ |- ψ⇒φ, Π
           * ----------------------------
           *      Γ, Σ |- φ⇔ψ, Π, Δ
           */
          case RightIff(b, t1, t2, phi, psi) =>
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            else if (psi.sort != Prop)
              sortMismatch(Prop, psi.sort, step)
            else {
              val prem1 = ref(t1)
              val prem2 = ref(t2)
              val phiImpPsi = implies(phi)(psi)
              val psiImpPhi = implies(psi)(phi)
              val phiIffPsi = iff(phi)(psi)

              if (b.left != (prem1.left union prem2.left))
                error(step, "Left-hand side of conclusion is not the union of the left-hand sides of the premises.")
              else if (!prem1.right.subsetOf(b.right + phiImpPsi))
                error(step, "Right-hand side of first premise is not a subset of conclusion right-hand side + φ⇒ψ.")
              else if (!prem2.right.subsetOf(b.right + psiImpPhi))
                error(step, "Right-hand side of second premise is not a subset of conclusion right-hand side + ψ⇒φ.")
              else if (!b.right.subsetOf((prem1.right union prem2.right) + phiIffPsi))
                error(step, "Right-hand side of conclusion is not a subset of the union of the right-hand sides of the premises + φ⇔ψ.")
              else
                SCValidProof(SCProof(step))
            }
          /*
           *  Γ, φ |- Δ
           * --------------
           *   Γ |- ¬φ, Δ
           */
          case RightNot(b, t1, phi) =>
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            else {
              val prem1 = ref(t1)
              val nPhi = neg(phi)

              if (b.right != prem1.right + nPhi)
                error(step, "Right-hand side of conclusion is not the same as right-hand side of premise + ¬φ.")
              else if (b.left + phi != prem1.left)
                error(step, "Left-hand side of conclusion + φ is not the same as left-hand side of premise.")
              else
                SCValidProof(SCProof(step))
            }
          /*
           *    Γ |- φ, Δ
           * ------------------- if x is not free in the resulting sequent
           *  Γ |- ∀x. φ, Δ
           */
          case RightForall(b, t1, phi, x) =>
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            else if (x.sort != Ind)
              sortMismatch(Ind, x.sort, step)
            else {
              val prem1 = ref(t1)
              val quantified = forall(Lambda(x, phi))

              if (b.left != prem1.left)
                error(step, "Left-hand side of conclusion is not the same as left-hand side of premise.")
              else if (b.right + phi != prem1.right + quantified)
                error(step, "Right-hand side of conclusion + φ is not the same as right-hand side of premise + ∀x. φ.")
              else if (variableIsFreeInSequent(b, x))
                error(step, "Variable x is free in the resulting sequent.")
              else
                SCValidProof(SCProof(step))
            }
          /*
           *   Γ |- φ[t/x], Δ
           * -------------------
           *  Γ |- ∃x. φ, Δ
           */
          case RightExists(b, t1, phi, x, t) =>
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            else if (x.sort != Ind)
              sortMismatch(Ind, x.sort, step)
            else if (t.sort != Ind)
              sortMismatch(Ind, t.sort, step)
            else {
              val prem1 = ref(t1)
              val quantified = exists(Lambda(x, phi))
              val instantiated = substituteVariables(phi, Map(x -> t))

              if (b.left != prem1.left)
                error(step, "Left-hand side of conclusion is not the same as left-hand side of premise.")
              else if (b.right + instantiated != prem1.right + quantified)
                error(step, "Right-hand side of conclusion + φ[t/x] is not the same as right-hand side of premise + ∃x. φ.")
              else
                SCValidProof(SCProof(step))
            }

          /**
           * <pre>
           *       Γ |- φ[t/x], Δ
           * --------------------------
           *     Γ|- φ[(εx. φ)/x], Δ
           * </pre>
           */
          case RightEpsilon(b, t1, phi, x, t) =>
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            else if (x.sort != Ind)
              sortMismatch(Ind, x.sort, step)
            else if (t.sort != Ind)
              sortMismatch(Ind, t.sort, step)
            else {
              val prem1 = ref(t1)
              val epsilonTerm = epsilon(Lambda(x, phi))
              val expectedTop = substituteVariables(phi, Map(x -> t))
              val expectedBot = substituteVariables(phi, Map(x -> epsilonTerm))

              if (b.left != prem1.left)
                error(step, "Left-hand side of conclusion is not the same as left-hand side of premise.")
              else if (b.right + expectedTop != prem1.right + expectedBot)
                error(step, "Right-hand side of conclusion + φ[t/x] is not the same as right-hand side of premise + φ[(εx. φ)/x].")
              else
                SCValidProof(SCProof(step))
            }

          // Structural rules
          /*
           *     Γ |- Δ
           * --------------
           *   Γ, Σ |- Δ
           */
          case Weakening(b, t1) =>
            if (isImplyingSequent(ref(t1), b))
              SCValidProof(SCProof(step))
            else SCInvalidProof(SCProof(step), Nil, "Conclusion cannot be trivially derived from premise.")

          // Equality Rules
          /*
           *  Γ, s=s |- Δ
           * --------------
           *     Γ |- Δ
           */
          case LeftRefl(b, t1, phi) =>
            phi match {
              case equality(left, right) =>
                val prem1 = ref(t1)

                if (left != right)
                  error(step, "Given equality is not reflexive.")
                else if (b.right != prem1.right)
                  error(step, "Right-hand side of premise is not the same as right-hand side of conclusion.")
                else if (b.left + phi != prem1.left)
                  error(step, "Left-hand side of conclusion + given equality is not the same as left-hand side of premise.")
                else
                  SCValidProof(SCProof(step))
              case _ => error(step, "Given formula is not an equality.")
            }

          /*
           *
           * ---------------
           *   Γ |- s=s, Δ
           */
          case RightRefl(b, phi) =>
            phi match {
              case equality(left, right) =>
                if (left != right)
                  error(step, "Given equality is not reflexive.")
                else if (!b.right.contains(phi))
                  error(step, "Right-hand side of conclusion does not contain the reflexive equality.")
                else
                  SCValidProof(SCProof(step))
              case _ => error(step, "Given formula is not an equality.")
            }

          /**
           * <pre>
           *                     Γ, φ(s_) |- Δ
           * -----------------------------------------------------
           *   Γ, (∀x,...,z. (s x ... z)=(t x ... z))_, φ(t_) |- Δ
           * </pre>
           */
          case LeftSubstEq(b, t1, equals, lambdaPhi) =>
            val (s_es, t_es) = equals.unzip
            val (phi_args, phi_body) = lambdaPhi
            if (phi_args.size != s_es.size) // Not strictly necessary, but it's a good sanity check. To reactivate when tactics have been modified.
              SCInvalidProof(SCProof(step), Nil, "The number of arguments of φ must be the same as the number of equalities.")
            else if (equals.zip(phi_args).exists { case ((s, t), arg) => s.sort != arg.sort || t.sort != arg.sort || !(arg.sort.isFunctional || arg.sort.isPredicate) })
              SCInvalidProof(SCProof(step), Nil, "The arities of symbols in φ must be the same as the arities of equalities.")
            else {
              val phi_s_for_f = substituteVariables(phi_body, (phi_args zip s_es).toMap)
              val phi_t_for_f = substituteVariables(phi_body, (phi_args zip t_es).toMap)
              val sEqT_es = equals map { case (s, t) =>
                val no = ((s.freeVariables ++ t.freeVariables).view.map(_.id.no) ++ Seq(-1)).max + 1
                val vars = (no until no + s.sort.depth).map(i => Variable(Identifier("x", i), Ind))
                val inner1 = vars.foldLeft(s)(_(_))
                val inner2 = vars.foldLeft(t)(_(_))
                val base = if (inner1.sort == Prop) iff(inner1)(inner2) else equality(inner1)(inner2)
                vars.foldRight(base: Expression) { case (s_arg, acc) => forall(Lambda(s_arg, acc)) }
              }

              if (isSameSet(b.right, ref(t1).right))
                if (
                  isSameSet(b.left + phi_t_for_f, ref(t1).left ++ sEqT_es + phi_s_for_f) ||
                  isSameSet(b.left + phi_s_for_f, ref(t1).left ++ sEqT_es + phi_t_for_f)
                )
                  SCValidProof(SCProof(step))
                else
                  SCInvalidProof(
                    SCProof(step),
                    Nil,
                    "Left-hand sides of the conclusion + φ(s_) must be the same as left-hand side of the premise + (s=t)_ + φ(t_) (or with s_ and t_ swapped)."
                  )
              else SCInvalidProof(SCProof(step), Nil, "Right-hand sides of the premise and the conclusion aren't the same.")
            }

          /*
           *  Γ |- φ(s), Δ     Σ |- s=t, Π
           * ---------------------------------
           *         Γ, Σ |- φ(t), Δ, Π
           */
          case RightSubstEq(b, t1, equals, lambdaPhi) =>
            val (s_es, t_es) = equals.unzip
            val (phi_args, phi_body) = lambdaPhi
            if (phi_args.size != s_es.size) // Not strictly necessary, but it's a good sanity check. To reactivate when tactics have been modified.
              SCInvalidProof(SCProof(step), Nil, "The number of arguments of φ must be the same as the number of equalities.")
            else if (equals.zip(phi_args).exists { case ((s, t), arg) => s.sort != arg.sort || t.sort != arg.sort })
              SCInvalidProof(SCProof(step), Nil, "The arities of symbols in φ must be the same as the arities of equalities.")
            else {
              val phi_s_for_f = substituteVariables(phi_body, (phi_args zip s_es).toMap)
              val phi_t_for_f = substituteVariables(phi_body, (phi_args zip t_es).toMap)
              val sEqT_es = equals map { case (s, t) =>
                val no = ((s.freeVariables ++ t.freeVariables).view.map(_.id.no) ++ Seq(0)).max + 1
                val vars = (no until no + s.sort.depth).map(i => Variable(Identifier("x", i), Ind))
                val inner1 = vars.foldLeft(s)(_(_))
                val inner2 = vars.foldLeft(t)(_(_))
                val base = if (inner1.sort == Prop) iff(inner1)(inner2) else equality(inner1)(inner2)
                vars.foldRight(base: Expression) { case (s_arg, acc) => forall(Lambda(s_arg, acc)) }
              }
              if (isSameSet(b.left, ref(t1).left ++ sEqT_es))
                if (
                  isSameSet(b.right + phi_t_for_f, ref(t1).right + phi_s_for_f) ||
                  isSameSet(b.right + phi_s_for_f, ref(t1).right + phi_t_for_f)
                ) {
                  SCValidProof(SCProof(step))
                } else {

                  SCInvalidProof(
                    SCProof(step),
                    Nil,
                    "Right-hand side of the premise and the conclusion should be the same with each containing one of φ(s_) φ(t_), but it isn't the case."
                  )
                }
              else SCInvalidProof(SCProof(step), Nil, "Left-hand sides of the premise + (s=t)_ must be the same as left-hand side of the premise.")
            }
          /**
           * <pre>
           * Γ |- Δ
           * --------------------------
           * Γ[ψ/?p] |- Δ[ψ/?p]
           * </pre>
           */
          case InstSchema(bot, t1, subst) =>
            val expected =
              (ref(t1).left.map(phi => substituteVariables(phi, subst)), ref(t1).right.map(phi => substituteVariables(phi, subst)))
            if (isSameSet(bot.left, expected._1))
              if (isSameSet(bot.right, expected._2))
                SCValidProof(SCProof(step))
              else SCInvalidProof(SCProof(step), Nil, "Right-hand side of premise instantiated with the given maps must be the same as right-hand side of conclusion.")
            else SCInvalidProof(SCProof(step), Nil, "Left-hand side of premise instantiated with the given maps must be the same as left-hand side of conclusion.")

          case SCSubproof(sp, premises) =>
            if (premises.size == sp.imports.size) {
              val invalid = premises.zipWithIndex.find { case (no, p) => !isSameSequent(ref(no), sp.imports(p)) }
              if (invalid.isEmpty) {
                checkSCProof(sp)
              } else
                SCInvalidProof(
                  SCProof(step),
                  Nil,
                  s"Premise number ${invalid.get._1} (refering to step ${invalid.get}) is not the same as import number ${invalid.get._1} of the subproof."
                )
            } else SCInvalidProof(SCProof(step), Nil, "Number of premises and imports don't match: " + premises.size + " " + sp.imports.size)

          /*
           *
           * --------------
           *     |- s=s
           */
          case Sorry(b) =>
            SCValidProof(SCProof(step), usesSorry = true)

        }
    r
  }

  /**
   * Verifies if a given pure SequentCalculus is conditionally correct, as the imported sequents are assumed.
   * If the proof is not correct, the function will report the faulty line and a brief explanation.
   *
   * @param proof A SC proof to check
   * @return SCValidProof(SCProof(step)) if the proof is correct, else SCInvalidProof with the path to the incorrect proof step
   *         and an explanation.
   */
  def checkSCProof(proof: SCProof): SCProofCheckerJudgement = {
    var isSorry = false
    val possibleError = proof.steps.view.zipWithIndex
      .map { case (step, no) =>
        checkSingleSCStep(no, step, (i: Int) => proof.getSequent(i), proof.imports.size) match {
          case SCInvalidProof(_, path, message) => SCInvalidProof(proof, no +: path, message)
          case SCValidProof(_, sorry) =>
            isSorry = isSorry || sorry
            SCValidProof(proof, sorry)
        }
      }
      .find(j => !j.isValid)
    if (possibleError.isEmpty) SCValidProof(proof, isSorry)
    else possibleError.get
  }

}
