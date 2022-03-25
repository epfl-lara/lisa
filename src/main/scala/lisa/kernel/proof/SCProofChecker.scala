package lisa.kernel.proof

import lisa.kernel.Printer
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SequentCalculus.*
import lisa.kernel.proof.SCProofCheckerJudgement.*

object SCProofChecker {

    private object Set {
        def unapplySeq[T](s: Set[T]): Option[Seq[T]] = Some(s.toSeq)
    }


    /**
     * This function verifies that a single SCProofStep is correctly applied. It verify that the step only refers to sequents with a lower number, and that
     * the type and parameters of the proofstep correspond to the sequent claimed sequent.
     *
     * @param no The number of the given proof step. Needed to vewrify that the proof step doesn't refer to posterior sequents.
     * @param step The proof step whose correctness needs to be checked
     * @param references A function that associates sequents to a range of positive and negative integers that the proof step may refer to. Typically,
     *                   a proof's [[SCProof.getSequent]] function.
     * @return
     */
    def checkSingleSCStep(no:Int, step: SCProofStep, references : Int => Sequent, importsSize: Option[Int]=None): SCProofCheckerJudgement = {
        val ref = references
        val false_premise = step.premises.find(i => i >= no)
        val false_premise2 = if (importsSize.nonEmpty) step.premises.find(i => i< -importsSize.get) else None

        val r: SCProofCheckerJudgement =
            if (false_premise.nonEmpty)
                SCInvalidProof(Nil, s"Step no $no can't refer to higher number ${false_premise.get} as a premise.")
            else if (false_premise2.nonEmpty)
                SCInvalidProof(Nil, s"A step can't refer to step ${false_premise2.get}, imports only contains ${importsSize.get} elements.")
            else step match {
                /*
                 *    Γ |- Δ
                 * ------------
                 *    Γ |- Δ
                 */
                case Rewrite(s, t1) =>
                    if (isSameSequent(s, ref(t1))) SCValidProof else SCInvalidProof(Nil, s"The premise and the conclusion are not trivially equivalent.")
                /*
                 *
                 * --------------
                 *   Γ, φ |- φ, Δ
                 */
                case Hypothesis(Sequent(left, right), phi) =>
                    if (contains(left, phi))
                        if (contains(right, phi)) SCValidProof

                        else SCInvalidProof(Nil, s"Right-hand side does not contain formula φ")
                    else SCInvalidProof(Nil, s"Left-hand side does not contain formula φ")
                /*
                 *  Γ |- Δ, φ    φ, Σ |- Π
                 * ------------------------
                 *       Γ, Σ |-Δ, Π
                 */
                case Cut(b, t1, t2, phi) =>
                        if (isSameSet(b.left + phi, ref(t1).left union ref(t2).left))
                            if (isSameSet(b.right + phi, ref(t2).right union ref(t1).right))
                                if (contains(ref(t2).left, phi))
                                    if (contains(ref(t1).right, phi))
                                        SCValidProof
                                    else SCInvalidProof(Nil, s"Right-hand side of first premise does not contain φ as claimed.")
                                else SCInvalidProof(Nil, s"Left-hand side of second premise does not contain φ as claimed.")
                            else SCInvalidProof(Nil, s"Right-hand side of conclusion + φ is not the union of the right-hand sides of the premises.")
                        else SCInvalidProof(Nil, s"Left-hand side of conclusion + φ is not the union of the left-hand sides of the premises.")

                // Left rules
                /*
                 *   Γ, φ |- Δ                 Γ, φ, ψ |- Δ
                 * --------------     or     -------------
                 *  Γ, φ∧ψ |- Δ               Γ, φ∧ψ |- Δ
                 */
                case LeftAnd(b, t1, phi, psi) =>
                    if (isSameSet(ref(t1).right, b.right))
                        val phiAndPsi = ConnectorFormula(And, Seq(phi, psi))
                        if (isSameSet(b.left + phi, ref(t1).left + phiAndPsi) ||
                            isSameSet(b.left + psi, ref(t1).left + phiAndPsi) ||
                            isSameSet(b.left + phi + psi, ref(t1).left + phiAndPsi))
                            SCValidProof
                        else SCInvalidProof(Nil, "Left-hand side of conclusion + φ∧ψ must be same as left-hand side of premise + either φ, ψ or both.")
                    else SCInvalidProof(Nil, "Right-hand sides of the premise and the conclusion must be the same.")
                /*
                 *  Γ, φ |- Δ    Σ, ψ |- Π
                 * ------------------------
                 *    Γ, Σ, φ∨ψ |- Δ, Π
                 */
                case LeftOr(b, t, disjuncts) =>
                    if (isSameSet(b.right, t.map(ref(_).right).reduce(_ union _)) )
                        val phiOrPsi = ConnectorFormula(Or, disjuncts)
                        if (isSameSet(disjuncts.foldLeft(b.left)(_ + _), t.map(ref(_).left).reduce(_ union _) + phiOrPsi))
                            SCValidProof
                        else SCInvalidProof(Nil, s"Left-hand side of conclusion + disjuncts is not the same as the union of the left-hand sides of the premises + φ∨ψ.")
                    else SCInvalidProof(Nil, s"Right-hand side of conclusion is not the union of the right-hand sides of the premises.")
                /*
                 *  Γ |- φ, Δ    Σ, ψ |- Π
                 * ------------------------
                 *    Γ, Σ, φ→ψ |- Δ, Π
                 */
                case LeftImplies(b, t1, t2, phi, psi) =>
                    val phiImpPsi = ConnectorFormula(Implies, Seq(phi, psi))
                    if (isSameSet(b.right + phi, ref(t1).right union ref(t2).right))
                        if (isSameSet(b.left + psi, ref(t1).left union ref(t2).left + phiImpPsi))
                            SCValidProof
                        else SCInvalidProof(Nil, s"Left-hand side of conclusion + ψ must be identical to union of left-hand sides of premisces + φ→ψ.")
                    else SCInvalidProof(Nil, s"Right-hand side of conclusion + φ must be identical to union of right-hand sides of premisces.")
                /*
                 *  Γ, φ→ψ |- Δ               Γ, φ→ψ, ψ→φ |- Δ
                 * --------------    or     ---------------
                 *  Γ, φ↔ψ |- Δ              Γ, φ↔ψ |- Δ
                 */
                case LeftIff(b, t1, phi, psi) =>
                    val phiImpPsi = ConnectorFormula(Implies, Seq(phi, psi))
                    val psiImpPhi = ConnectorFormula(Implies, Seq(psi, phi))
                    val phiIffPsi = ConnectorFormula(Iff, Seq(phi, psi))
                    if (isSameSet(ref(t1).right, b.right))
                        if (isSameSet(b.left + phiImpPsi , ref(t1).left + phiIffPsi) ||
                            isSameSet(b.left + psiImpPhi , ref(t1).left + phiIffPsi) ||
                            isSameSet(b.left + phiImpPsi + psiImpPhi , ref(t1).left + phiIffPsi))
                            SCValidProof
                        else SCInvalidProof(Nil, "Left-hand side of conclusion + φ↔ψ must be same as left-hand side of premise + either φ→ψ, ψ→φ or both.")
                    else SCInvalidProof(Nil, "Right-hand sides of premise and conclusion must be the same.")

                /*
                 *   Γ |- φ, Δ
                 * --------------
                 *   Γ, ¬φ |- Δ
                 */
                case LeftNot(b, t1, phi) =>
                    val nPhi = ConnectorFormula(Neg, Seq(phi))
                    if (isSameSet(b.left, ref(t1).left + nPhi))
                        if (isSameSet(b.right + phi, ref(t1).right))
                            SCValidProof
                        else SCInvalidProof(Nil, "Right-hand side of conclusion + φ must be the same as right-hand side of premise")
                    else SCInvalidProof(Nil, "Left-hand side of conclusion must be the same as left-hand side of premise + ¬φ")

                /*
                 *   Γ, φ[t/x] |- Δ
                 * -------------------
                 *  Γ, ∀x. φ |- Δ
                 */
                case LeftForall(b, t1, phi, x, t) =>
                    if (isSameSet(b.right, ref(t1).right))
                        if (isSameSet(b.left + substituteVariable(phi, x, t), ref(t1).left + BinderFormula(Forall, x, phi)))
                            SCValidProof
                        else SCInvalidProof(Nil, "Left-hand side of conclusion + φ[t/x] must be the same as left-hand side of premise + ∀x. φ")
                    else SCInvalidProof(Nil, "Right-hand side of conclusion must be the same as right-hand side of premise")

                /*
                 *    Γ, φ |- Δ
                 * ------------------- if x is not free in the resulting sequent
                 *  Γ, ∃x. φ|- Δ
                 */
                case LeftExists(b, t1, phi, x) =>
                    if (isSameSet(b.right, ref(t1).right))
                        if (isSameSet(b.left + phi, ref(t1).left + BinderFormula(Exists, x, phi)))
                            if ((b.left union b.right).forall(f => !f.freeVariables.contains(x)))
                                SCValidProof
                            else SCInvalidProof(Nil, "The variable x must not be free in the resulting sequent.")
                        else SCInvalidProof(Nil, "Left-hand side of conclusion + φ must be the same as left-hand side of premise + ∃x. φ")
                    else SCInvalidProof(Nil, "Right-hand side of conclusion must be the same as right-hand side of premise")

                /*
                 *  Γ, ∃y.∀x. (x=y) ↔ φ |-  Δ
                 * ---------------------------- if y is not free in φ
                 *      Γ, ∃!x. φ |- Δ
                 */
                case LeftExistsOne(b, t1, phi, x) =>
                    val y = VariableLabel(freshId(phi.freeVariables.map(_.id) + x.id, "y"))
                    val temp = BinderFormula(Exists, y, BinderFormula(Forall, x, ConnectorFormula(Iff, List(PredicateFormula(equality, List(VariableTerm(x), VariableTerm(y))), phi))))
                    if (isSameSet(b.right, ref(t1).right))
                        if (isSameSet(b.left + temp, ref(t1).left + BinderFormula(ExistsOne, x, phi)))
                            SCValidProof
                        else SCInvalidProof(Nil, "Left-hand side of conclusion + ∃y.∀x. (x=y) ↔ φ must be the same as left-hand side of premise + ∃!x. φ")
                    else SCInvalidProof(Nil, "Right-hand side of conclusion must be the same as right-hand side of premise")

                // Right rules
                /*
                 *  Γ |- φ, Δ    Σ |- ψ, Π
                 * ------------------------
                 *    Γ, Σ |- φ∧ψ, Π, Δ
                 */
                case RightAnd(b, t, cunjuncts) =>
                    val phiAndPsi = ConnectorFormula(And, cunjuncts)
                    if (isSameSet(b.left, t.map(ref(_).left).reduce(_ union _)))
                        if (isSameSet(cunjuncts.foldLeft(b.right)(_ + _), t.map(ref(_).right).reduce(_ union _) + phiAndPsi))
                                SCValidProof
                        else SCInvalidProof(Nil, s"Right-hand side of conclusion + φ + ψ is not the same as the union of the right-hand sides of the premises φ∧ψ.")
                    else SCInvalidProof(Nil, s"Left-hand side of conclusion is not the union of the left-hand sides of the premises.")
                /*
                 *   Γ |- φ, Δ                Γ |- φ, ψ, Δ
                 * --------------    or    ---------------
                 *  Γ |- φ∨ψ, Δ              Γ |- φ∨ψ, Δ
                 */
                case RightOr(b, t1, phi, psi) =>
                    val phiOrPsi = ConnectorFormula(Or, Seq(phi, psi))
                    if (isSameSet(ref(t1).left, b.left))
                        if (isSameSet(b.right + phi, ref(t1).right + phiOrPsi) ||
                            isSameSet(b.right + psi, ref(t1).right + phiOrPsi) ||
                            isSameSet(b.right + phi + psi, ref(t1).right + phiOrPsi))
                            SCValidProof
                        else  SCInvalidProof(Nil, "Right-hand side of conclusion + φ∧ψ must be same as right-hand side of premise + either φ, ψ or both.")
                    else SCInvalidProof(Nil, "Left-hand sides of the premise and the conclusion must be the same.")
                /*
                 *  Γ, φ |- ψ, Δ
                 * --------------
                 *  Γ |- φ→ψ, Δ
                 */
                case RightImplies(b, t1, phi, psi) =>
                    val phiImpPsi = ConnectorFormula(Implies, Seq(phi, psi))
                    if (isSameSet(ref(t1).left, b.left + phi))
                        if (isSameSet(b.right + psi, ref(t1).right + phiImpPsi))
                            SCValidProof
                        else SCInvalidProof(Nil, "Right-hand side of conclusion + ψ must be same as right-hand side of premise + φ→ψ.")
                    else SCInvalidProof(Nil, "Left-hand side of conclusion + psi must be same as left-hand side of premise.")
                /*
                 *  Γ |- a→ψ, Δ    Σ |- ψ→φ, Π
                 * ----------------------------
                 *      Γ, Σ |- φ↔b, Π, Δ
                 */
                case RightIff(b, t1, t2, phi, psi) =>
                    val phiImpPsi = ConnectorFormula(Implies, Seq(phi, psi))
                    val psiImpPhi = ConnectorFormula(Implies, Seq(psi, phi))
                    val phiIffPsi = ConnectorFormula(Iff, Seq(phi, psi))
                    if (isSameSet(b.left, ref(t1).left union ref(t2).left))
                        if (isSameSet(b.right + phiImpPsi + psiImpPhi, ref(t1).right union ref(t2).right + phiIffPsi))
                            SCValidProof
                        else SCInvalidProof(Nil, s"Right-hand side of conclusion + a→ψ + ψ→φ is not the same as the union of the right-hand sides of the premises φ↔b.")
                    else SCInvalidProof(Nil, s"Left-hand side of conclusion is not the union of the left-hand sides of the premises.")
                /*
                 *  Γ, φ |- Δ
                 * --------------
                 *   Γ |- ¬φ, Δ
                 */
                case RightNot(b, t1, phi) =>
                    val nPhi = ConnectorFormula(Neg, Seq(phi))
                    if (isSameSet(b.right, ref(t1).right + nPhi))
                        if (isSameSet(b.left + phi, ref(t1).left))
                            SCValidProof
                        else SCInvalidProof(Nil, "Left-hand side of conclusion + φ must be the same as left-hand side of premise")
                    else SCInvalidProof(Nil, "Right-hand side of conclusion must be the same as right-hand side of premise + ¬φ")
                /*
                 *    Γ |- φ, Δ
                 * ------------------- if x is not free in the resulting sequent
                 *  Γ |- ∀x. φ, Δ
                 */
                case RightForall(b, t1, phi, x) =>
                    if (isSameSet(b.left, ref(t1).left))
                        if (isSameSet(b.right + phi, ref(t1).right + BinderFormula(Forall, x ,phi)))
                            if ((b.left union b.right).forall(f => !f.freeVariables.contains(x)))
                                SCValidProof
                            else SCInvalidProof(Nil, "The variable x must not be free in the resulting sequent.")
                        else SCInvalidProof(Nil, "Right-hand side of conclusion + φ must be the same as right-hand side of premise + ∀x. φ")
                    else SCInvalidProof(Nil, "Left-hand sides of conclusion and premise must be the same.")
                /*
                 *   Γ |- φ[t/x], Δ
                 * -------------------
                 *  Γ |- ∃x. φ, Δ
                 */
                case RightExists(b, t1, phi, x, t) =>
                    if (isSameSet(b.left, ref(t1).left))
                        if (isSameSet(b.right + substituteVariable(phi, x, t), ref(t1).right + BinderFormula(Exists, x ,phi)))
                            SCValidProof
                        else SCInvalidProof(Nil, "Right-hand side of the conclusion + φ[t/x] must be the same as right-hand side of the premise + ∃x. φ")
                    else SCInvalidProof(Nil, "Left-hand sides or conclusion and premise must be the same.")

                /**
                 * <pre>
                 *  Γ |- ∃y.∀x. (x=y) ↔ φ, Δ
                 * ---------------------------- if y is not free in φ
                 *      Γ|- ∃!x. φ,  Δ
                 * </pre>
                 */
                case RightExistsOne(b, t1, phi, x) =>
                    val y = VariableLabel(freshId(phi.freeVariables.map(_.id), "x"))
                    val temp = BinderFormula(Exists, y, BinderFormula(Forall, x, ConnectorFormula(Iff, List(PredicateFormula(equality, List(VariableTerm(x), VariableTerm(y))), phi))))
                    if (isSameSet(b.left, ref(t1).left))
                        if (isSameSet(b.right + temp, ref(t1).right + BinderFormula(ExistsOne, x, phi)))
                            SCValidProof
                        else SCInvalidProof(Nil, "Right-hand side of conclusion + ∃y.∀x. (x=y) ↔ φ must be the same as right-hand side of premise + ∃!x. φ")
                    else SCInvalidProof(Nil, "Left-hand sides of conclusion and premise must be the same")


                // Structural rules
                /*
                 *     Γ |- Δ
                 * --------------
                 *   Γ, Σ |- Δ
                 */
                case Weakening(b, t1) =>
                    if (isSubset(ref(t1).left, b.left))
                        if (isSubset(ref(t1).right, b.right))
                            SCValidProof
                        else SCInvalidProof(Nil, "Right-hand side of premise must be a subset of right-hand side of conclusion")
                    else SCInvalidProof(Nil, "Left-hand side of premise must be a subset of left-hand side of conclusion")

                // Equality Rules
                /*
                 *  Γ, s=s |- Δ
                 * --------------
                 *     Γ |- Δ
                 */
                case LeftRefl(b, t1, phi) =>
                    phi match {
                        case PredicateFormula(`equality`, Seq(left, right)) =>
                            if (isSame(left, right))
                                if (isSameSet(b.right, ref(t1).right))
                                    if (isSameSet(b.left + phi, ref(t1).left))
                                        SCValidProof
                                    else SCInvalidProof(Nil, s"Left-hand sides of the conclusion + φ must be the same as left-hand side of the premise.")
                                else SCInvalidProof(Nil, s"Right-hand sides of the premise and the conclusion aren't the same.")
                            else SCInvalidProof(Nil, s"φ is not an instance of reflexivity.")
                        case _ => SCInvalidProof(Nil, "φ is not an equality")
                    }

                /*
                 *
                 * --------------
                 *     |- s=s
                 */
                case RightRefl(b, phi) =>
                    phi match {
                        case PredicateFormula(`equality`, Seq(left, right)) =>
                            if (isSame(left, right))
                                if (contains(b.right, phi))
                                    SCValidProof
                                else SCInvalidProof(Nil, s"Right-Hand side of conclusion does not contain φ")
                            else SCInvalidProof(Nil, s"φ is not an instance of reflexivity.")
                        case _ => SCInvalidProof(Nil, s"φ is not an equality.")
                    }

                /*
                 *    Γ, φ[s/?f] |- Δ
                 * ---------------------
                 *  Γ, s=t, φ[t/?f] |- Δ
                 */
                case LeftSubstEq(b, t1, s, t, phi, f) =>
                    val sEqT = PredicateFormula(equality, Seq(s, t))
                    val phi_s_for_f = instantiateFunctionSchema(phi, f, s, Nil)
                    val phi_t_for_f = instantiateFunctionSchema(phi, f, t, Nil)
                    if (f.arity == 0)
                        if (isSameSet(b.right, ref(t1).right))
                            if (isSameSet(b.left + phi_t_for_f, ref(t1).left + sEqT + phi_s_for_f) ||
                            isSameSet(b.left + phi_s_for_f, ref(t1).left + sEqT + phi_t_for_f))
                                SCValidProof
                            else SCInvalidProof(Nil, "Left-hand sides of the conclusion + φ[s/?f] must be the same as left-hand side of the premise + s=t + φ[t/?f] (or with s and t swapped).")
                        else SCInvalidProof(Nil, "Right-hand sides of the premise and the conclusion aren't the same.")
                    else SCInvalidProof(Nil, "Function schema ?f must have arity 0")


                /*
                 *    Γ |- φ[s/?f], Δ
                 * ---------------------
                 *  Γ, s=t |- φ[t/?f], Δ
                 */
                case RightSubstEq(b, t1, s, t, phi, f) =>
                    val sEqt = PredicateFormula(equality, Seq(s, t))
                    if (f.arity == 0)
                        if (isSameSet(ref(t1).left + sEqt, b.left))
                            val phi_s_for_f = instantiateFunctionSchema(phi, f, s, Nil)
                            val phi_t_for_f = instantiateFunctionSchema(phi, f, t, Nil)
                            if (isSameSet(b.right + phi_s_for_f, ref(t1).right + phi_t_for_f) ||
                                isSameSet(b.right + phi_t_for_f, ref(t1).right + phi_s_for_f))
                                SCValidProof
                            else SCInvalidProof(Nil, s"Right-hand side of the premise and the conclusion should be the same with each containing one of φ[s/?f]  φ[t/?f], but it isn't the case." )
                        else SCInvalidProof(Nil, "Left-hand sides of the premise + s=t must be the same as left-hand side of the premise.")
                    else SCInvalidProof(Nil, "Function schema ?f must have arity 0.")
                /*
                 *    Γ, φ[ψ/?q] |- Δ
                 * ---------------------
                 *  Γ, ψ↔τ, φ[τ/?q] |- Δ
                 */
                case LeftSubstIff(b, t1, psi, tau, phi, q) =>
                    val psiIffTau = ConnectorFormula(Iff, Seq(psi, tau))
                    val phi_tau_for_q = instantiatePredicateSchema(phi, q, tau, Nil)
                    val phi_psi_for_q = instantiatePredicateSchema(phi, q, psi, Nil)
                    if (q.arity == 0)
                        if (isSameSet(b.right, ref(t1).right))
                            if (isSameSet(ref(t1).left + psiIffTau + phi_tau_for_q, b.left + phi_psi_for_q) ||
                                isSameSet(ref(t1).left + psiIffTau + phi_psi_for_q, b.left + phi_tau_for_q))
                                SCValidProof
                            else SCInvalidProof(Nil, "Left-hand sides of the conclusion + φ[ψ/?q] must be the same as left-hand side of the premise + ψ↔τ + φ[τ/?q] (or with ψ and τ swapped).")
                        else  SCInvalidProof(Nil, "Right-hand sides of the premise and the conclusion aren't the same.")
                    else SCInvalidProof(Nil, "Predicate schema ?q must have arity 0.")

                /*
                 *    Γ |- φ[ψ/?p], Δ
                 * ---------------------
                 *  Γ, ψ↔τ |- φ[τ/?p], Δ
                 */
                case RightSubstIff(b, t1, psi, tau, phi, q) =>
                    val psiIffTau = ConnectorFormula(Iff, Seq(psi, tau))
                    val phi_tau_for_q = instantiatePredicateSchema(phi, q, tau, Nil)
                    val phi_psi_for_q = instantiatePredicateSchema(phi, q, psi, Nil)
                    if (q.arity == 0)
                        if (isSameSet(ref(t1).left + psiIffTau, b.left))
                            if (isSameSet(b.right + phi_tau_for_q, ref(t1).right + phi_psi_for_q) ||
                                isSameSet(b.right + phi_psi_for_q, ref(t1).right + phi_tau_for_q))
                                SCValidProof
                            else SCInvalidProof(Nil, s"Right-hand side of the premise and the conclusion should be the same with each containing one of φ[τ/?q] and φ[ψ/?q], but it isn't the case." )
                        else SCInvalidProof(Nil, "Left-hand sides of the premise + ψ↔τ must be the same as left-hand side of the premise.")
                    else SCInvalidProof(Nil, "Predicate schema ?q must have arity 0.")
                /**
                 * <pre>
                 *           Γ |- Δ
                 * --------------------------
                 *  Γ[r(a)/?f] |- Δ[r(a)/?f]
                 * </pre>
                 */
                case InstFunSchema(bot, t1, f, r, a) =>
                    val expected = (ref(t1).left.map(phi => instantiateFunctionSchema(phi, f, r, a)), ref(t1).right.map(phi => instantiateFunctionSchema(phi, f, r, a)))
                    if (isSameSet(bot.left, expected._1))
                        if (isSameSet(bot.right, expected._2))
                            SCValidProof
                        else SCInvalidProof(Nil, "Right-hand side of premise instantiated with [?f/r(a)] must be the same as right-hand side of conclusion.")
                    else  SCInvalidProof(Nil, "Left-hand side of premise instantiated with [?f/r(a)] must be the same as left-hand side of conclusion.")

                /**
                 * <pre>
                 *           Γ |- Δ
                 * --------------------------
                 *  Γ[ψ(a)/?p] |- Δ[ψ(a)/?p]
                 * </pre>
                 */
                case InstPredSchema(bot, t1, p, psi, a) =>
                    val expected = (ref(t1).left.map(phi => instantiatePredicateSchema(phi, p, psi, a)), ref(t1).right.map(phi => instantiatePredicateSchema(phi, p, psi, a)))
                    if (isSameSet(bot.left, expected._1))
                        if (isSameSet(bot.right, expected._2))
                            SCValidProof
                        else
                            SCInvalidProof(Nil, "Right-hand side of premise instantiated with [?p/ψ(a)] must be the same as right-hand side of conclusion.")
                    else  SCInvalidProof(Nil, "Left-hand side of premise instantiated with [?p/ψ(a)] must be the same as left-hand side of conclusion.")

                case SCSubproof(sp, premises, _) =>
                    if (premises.size == sp.imports.size){
                        val invalid = premises.zipWithIndex.find((no, p) => !isSameSequent(ref(no), sp.imports(p)) )
                        if (invalid.isEmpty){
                            checkSCProof(sp)
                        } else SCInvalidProof(Nil, s"Premise number ${invalid.get._1} (refering to step ${invalid.get}) is not the same as import number ${invalid.get._1} of the subproof.")
                    } else SCInvalidProof(Nil, "Number of premises and imports don't match: "+premises.size+" "+sp.imports.size)

            }
        r
    }

    /**
     * Verifies if a given pure SequentCalculus is conditionally correct, as the imported sequents are assumed.
     * If the proof is not correct, the functrion will report the faulty line and a brief explanation.
     * @param proof A SC proof to check
     * @return SCValidProof if the proof is correct, else SCInvalidProof with the path to the incorrect proof step
     *         and an explanation.
     */
    def checkSCProof(proof: SCProof): SCProofCheckerJudgement = {
        val possibleError = proof.steps.view.zipWithIndex.map((step, no) =>
            checkSingleSCStep(no, step, (i: Int) => proof.getSequent(i), Some(proof.imports.size)) match {
                case SCInvalidProof(path, message) => SCInvalidProof(no +: path, message)
                case SCValidProof => SCValidProof
            }
        ).find(j => !j.isValid)
        if (possibleError.isEmpty) SCValidProof
        else possibleError.get
    }

}
