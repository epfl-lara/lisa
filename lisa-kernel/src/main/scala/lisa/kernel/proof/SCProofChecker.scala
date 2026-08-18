package lisa.kernel.proof

import lisa.kernel.fol.FOL._
import lisa.kernel.proof.SCProofCheckerJudgement._
import lisa.kernel.proof.SequentCalculus._

object SCProofChecker {

  /**
   * This function verifies that a single SCProofStep is correctly applied. It verifies that the step only refers to sequents with a lower number,
   * and that the type, premises and parameters of the proof step correspond to the claimed conclusion.
   *
   * @param no         The number of the given proof step. Needed to vewrify that the proof step doesn't refer to posterior sequents.
   * @param step       The proof step whose correctness needs to be checked
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
        SCInvalidProof(SCProof(step), Nil, s"Step no $no can't refer to higher number ${false_premise.get} as a premise.")
      else if (false_premise2.nonEmpty)
        SCInvalidProof(SCProof(step), Nil, s"A step can't refer to step ${false_premise2.get}, imports only contains ${importsSize} elements.")
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
            if (phi.sort != Prop)
              SCInvalidProof(SCProof(step), Nil, "φ must be a formula, but it is a " + phi.sort)
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
            if (phi.sort != Prop)
              SCInvalidProof(SCProof(step), Nil, "φ must be a formula, but it is a " + phi.sort)
            else if (isSameSet(b.left + phi, ref(t1).left union ref(t2).left) && (!contains(ref(t1).left, phi) || contains(b.left, phi)))
              if (isSameSet(b.right + phi, ref(t2).right union ref(t1).right) && (!contains(ref(t2).right, phi) || contains(b.right, phi)))
                if (contains(ref(t2).left, phi))
                  if (contains(ref(t1).right, phi))
                    SCValidProof(SCProof(step))
                  else SCInvalidProof(SCProof(step), Nil, s"Right-hand side of first premise does not contain φ as claimed.")
                else SCInvalidProof(SCProof(step), Nil, s"Left-hand side of second premise does not contain φ as claimed.")
              else SCInvalidProof(SCProof(step), Nil, s"Right-hand side of conclusion + φ is not the union of the right-hand sides of the premises.")
            else SCInvalidProof(SCProof(step), Nil, s"Left-hand side of conclusion + φ is not the union of the left-hand sides of the premises.")

          // Left rules
          /*
           *   Γ, φ |- Δ                 Γ, φ, ψ |- Δ
           * --------------     or     -------------
           *  Γ, φ∧ψ |- Δ               Γ, φ∧ψ |- Δ
           */
          case LeftAnd(b, t1, phi, psi) =>
            if (phi.sort != Prop)
              SCInvalidProof(SCProof(step), Nil, "φ must be a formula, but it is a " + phi.sort)
            else if (psi.sort != Prop)
              SCInvalidProof(SCProof(step), Nil, "ψ must be a formula, but it is a " + phi.sort)
            else if (isSameSet(ref(t1).right, b.right)) {
              val phiAndPsi = and(phi)(psi)
              if (
                isSameSet(b.left + phi, ref(t1).left + phiAndPsi) ||
                isSameSet(b.left + psi, ref(t1).left + phiAndPsi) ||
                isSameSet(b.left + phi + psi, ref(t1).left + phiAndPsi)
              )
                SCValidProof(SCProof(step))
              else SCInvalidProof(SCProof(step), Nil, "Left-hand side of conclusion + φ∧ψ must be same as left-hand side of premise + either φ, ψ or both.")
            } else SCInvalidProof(SCProof(step), Nil, "Right-hand sides of the premise and the conclusion must be the same.")
          /*
           *  Γ, φ |- Δ    Σ, ψ |- Π
           * ------------------------
           *    Γ, Σ, φ∨ψ |- Δ, Π
           */
          case LeftOr(b, t, disjuncts) =>
            if (disjuncts.exists(phi => phi.sort != Prop)) {
              val culprit = disjuncts.find(phi => phi.sort != Prop).get
              SCInvalidProof(SCProof(step), Nil, "all φs must be a formula, but " + culprit + " is a " + culprit.sort)
            } else if (isSameSet(b.right, t.map(ref(_).right).fold(Set.empty)(_ union _))) {
              val phiOrPsi = disjuncts.reduceLeft(or(_)(_))
              if (
                t.zip(disjuncts).forall { case (s, phi) => isSubset(ref(s).left, b.left + phi) } &&
                isSubset(b.left, t.map(ref(_).left).fold(Set.empty)(_ union _) + phiOrPsi)
              )
                SCValidProof(SCProof(step))
              else SCInvalidProof(SCProof(step), Nil, s"Left-hand side of conclusion + disjuncts is not the same as the union of the left-hand sides of the premises + φ∨ψ.")
            } else SCInvalidProof(SCProof(step), Nil, s"Right-hand side of conclusion is not the union of the right-hand sides of the premises.")
          /*
           *  Γ |- φ, Δ    Σ, ψ |- Π
           * ------------------------
           *    Γ, Σ, φ⇒ψ |- Δ, Π
           */
          case LeftImplies(b, t1, t2, phi, psi) =>
            if (phi.sort != Prop)
              SCInvalidProof(SCProof(step), Nil, "φ must be a formula, but it is a " + phi.sort)
            else if (psi.sort != Prop)
              SCInvalidProof(SCProof(step), Nil, "ψ must be a formula, but it is a " + phi.sort)
            else {
              val phiImpPsi = implies(phi)(psi)
              if (isSameSet(b.right + phi, ref(t1).right union ref(t2).right))
                if (isSameSet(b.left + psi, ref(t1).left union ref(t2).left + phiImpPsi))
                  SCValidProof(SCProof(step))
                else SCInvalidProof(SCProof(step), Nil, s"Left-hand side of conclusion + ψ must be identical to union of left-hand sides of premisces + φ⇒ψ.")
              else SCInvalidProof(SCProof(step), Nil, s"Right-hand side of conclusion + φ must be identical to union of right-hand sides of premisces.")
            }
          /*
           *  Γ, φ⇒ψ |- Δ               Γ, φ⇒ψ, ψ⇒φ |- Δ
           * --------------    or     ---------------
           *  Γ, φ⇔ψ |- Δ              Γ, φ⇔ψ |- Δ
           */
          case LeftIff(b, t1, phi, psi) =>
            if (phi.sort != Prop)
              SCInvalidProof(SCProof(step), Nil, "φ must be a formula, but it is a " + phi.sort)
            else if (psi.sort != Prop)
              SCInvalidProof(SCProof(step), Nil, "ψ must be a formula, but it is a " + phi.sort)
            else {
              val phiImpPsi = implies(phi)(psi)
              val psiImpPhi = implies(psi)(phi)
              val phiIffPsi = iff(phi)(psi)
              if (isSameSet(ref(t1).right, b.right))
                if (
                  isSameSet(b.left + phiImpPsi, ref(t1).left + phiIffPsi) ||
                  isSameSet(b.left + psiImpPhi, ref(t1).left + phiIffPsi) ||
                  isSameSet(b.left + phiImpPsi + psiImpPhi, ref(t1).left + phiIffPsi)
                )
                  SCValidProof(SCProof(step))
                else SCInvalidProof(SCProof(step), Nil, "Left-hand side of conclusion + φ⇔ψ must be same as left-hand side of premise + either φ⇒ψ, ψ⇒φ or both.")
              else SCInvalidProof(SCProof(step), Nil, "Right-hand sides of premise and conclusion must be the same.")
            }

          /*
           *   Γ |- φ, Δ
           * --------------
           *   Γ, ¬φ |- Δ
           */
          case LeftNot(b, t1, phi) =>
            if (phi.sort != Prop)
              SCInvalidProof(SCProof(step), Nil, "φ must be a formula, but it is a " + phi.sort)
            else {
              val nPhi = neg(phi)
              if (isSameSet(b.left, ref(t1).left + nPhi))
                if (isSameSet(b.right + phi, ref(t1).right))
                  SCValidProof(SCProof(step))
                else SCInvalidProof(SCProof(step), Nil, "Right-hand side of conclusion + φ must be the same as right-hand side of premise")
              else SCInvalidProof(SCProof(step), Nil, "Left-hand side of conclusion must be the same as left-hand side of premise + ¬φ")
            }

          /*
           *   Γ, φ[t/x] |- Δ
           * -------------------
           *  Γ, ∀x. φ |- Δ
           */
          case LeftForall(b, t1, phi, x, t) =>
            if (phi.sort != Prop)
              SCInvalidProof(SCProof(step), Nil, "φ must be a formula, but it is a " + phi.sort)
            else if (x.sort != Ind)
              SCInvalidProof(SCProof(step), Nil, "x must be a term variable, but it is a " + x.sort)
            else if (t.sort != Ind)
              SCInvalidProof(SCProof(step), Nil, "t must be a term , but it is a " + t.sort)
            else if (isSameSet(b.right, ref(t1).right))
              if (isSameSet(b.left + substituteVariables(phi, Map(x -> t)), ref(t1).left + forall(Lambda(x, phi))))
                SCValidProof(SCProof(step))
              else SCInvalidProof(SCProof(step), Nil, "Left-hand side of conclusion + φ[t/x] must be the same as left-hand side of premise + ∀x. φ")
            else SCInvalidProof(SCProof(step), Nil, "Right-hand side of conclusion must be the same as right-hand side of premise")

          /*
           *    Γ, φ |- Δ
           * ------------------- if x is not free in the resulting sequent
           *  Γ, ∃x. φ|- Δ
           */
          case LeftExists(b, t1, phi, x) =>
            if (phi.sort != Prop)
              SCInvalidProof(SCProof(step), Nil, "φ must be a formula, but it is a " + phi.sort)
            else if (x.sort != Ind)
              SCInvalidProof(SCProof(step), Nil, "x must be a term variable, but it is a " + x.sort)
            else if (isSameSet(b.right, ref(t1).right))
              if (isSameSet(b.left + phi, ref(t1).left + exists(Lambda(x, phi))))
                if ((b.left union b.right).forall(f => !f.freeVariables.contains(x)))
                  SCValidProof(SCProof(step))
                else SCInvalidProof(SCProof(step), Nil, "The variable x must not be free in the resulting sequent.")
              else SCInvalidProof(SCProof(step), Nil, "Left-hand side of conclusion + φ must be the same as left-hand side of premise + ∃x. φ")
            else SCInvalidProof(SCProof(step), Nil, "Right-hand side of conclusion must be the same as right-hand side of premise")

          // Right rules
          /*
           *  Γ |- φ, Δ    Σ |- ψ, Π
           * ------------------------
           *    Γ, Σ |- φ∧ψ, Π, Δ
           */
          case RightAnd(b, t, cunjuncts) =>
            if (cunjuncts.exists(phi => phi.sort != Prop)) {
              val culprit = cunjuncts.find(phi => phi.sort != Prop).get
              SCInvalidProof(SCProof(step), Nil, "all φs must be a formula, but " + culprit + " is a " + culprit.sort)
            } else {
              val phiAndPsi = cunjuncts.reduce(and(_)(_))
              if (isSameSet(b.left, t.map(ref(_).left).fold(Set.empty)(_ union _)))
                if (
                  t.zip(cunjuncts).forall { case (s, phi) => isSubset(ref(s).right, b.right + phi) } &&
                  isSubset(b.right, t.map(ref(_).right).fold(Set.empty)(_ union _) + phiAndPsi)
                  // isSameSet(cunjuncts.foldLeft(b.right)(_ + _), t.map(ref(_).right).fold(Set.empty)(_ union _) + phiAndPsi)
                )
                  SCValidProof(SCProof(step))
                else SCInvalidProof(SCProof(step), Nil, s"Right-hand side of conclusion + φ + ψ is not the same as the union of the right-hand sides of the premises φ∧ψ.")
              else SCInvalidProof(SCProof(step), Nil, s"Left-hand side of conclusion is not the union of the left-hand sides of the premises.")
            }
          /*
           *   Γ |- φ, Δ                Γ |- φ, ψ, Δ
           * --------------    or    ---------------
           *  Γ |- φ∨ψ, Δ              Γ |- φ∨ψ, Δ
           */
          case RightOr(b, t1, phi, psi) =>
            if (phi.sort != Prop)
              SCInvalidProof(SCProof(step), Nil, "φ must be a formula, but it is a " + phi.sort)
            else if (psi.sort != Prop)
              SCInvalidProof(SCProof(step), Nil, "ψ must be a formula, but it is a " + phi.sort)
            else {
              val phiOrPsi = or(phi)(psi)
              if (isSameSet(ref(t1).left, b.left))
                if (
                  isSameSet(b.right + phi, ref(t1).right + phiOrPsi) ||
                  isSameSet(b.right + psi, ref(t1).right + phiOrPsi) ||
                  isSameSet(b.right + phi + psi, ref(t1).right + phiOrPsi)
                )
                  SCValidProof(SCProof(step))
                else SCInvalidProof(SCProof(step), Nil, "Right-hand side of conclusion + φ∧ψ must be same as right-hand side of premise + either φ, ψ or both.")
              else SCInvalidProof(SCProof(step), Nil, "Left-hand sides of the premise and the conclusion must be the same.")
            }
          /*
           *  Γ, φ |- ψ, Δ
           * --------------
           *  Γ |- φ⇒ψ, Δ
           */
          case RightImplies(b, t1, phi, psi) =>
            if (phi.sort != Prop)
              SCInvalidProof(SCProof(step), Nil, "φ must be a formula, but it is a " + phi.sort)
            else if (psi.sort != Prop)
              SCInvalidProof(SCProof(step), Nil, "ψ must be a formula, but it is a " + phi.sort)
            else {
              val phiImpPsi = implies(phi)(psi)
              if (isSameSet(ref(t1).left, b.left + phi))
                if (isSameSet(b.right + psi, ref(t1).right + phiImpPsi))
                  SCValidProof(SCProof(step))
                else SCInvalidProof(SCProof(step), Nil, "Right-hand side of conclusion + ψ must be same as right-hand side of premise + φ⇒ψ.")
              else SCInvalidProof(SCProof(step), Nil, "Left-hand side of conclusion + psi must be same as left-hand side of premise.")
            }
          /*
           *  Γ |- φ⇒ψ, Δ    Σ |- ψ⇒φ, Π
           * ----------------------------
           *      Γ, Σ |- φ⇔ψ, Π, Δ
           */
          case RightIff(b, t1, t2, phi, psi) =>
            if (phi.sort != Prop)
              SCInvalidProof(SCProof(step), Nil, "φ must be a formula, but it is a " + phi.sort)
            else if (psi.sort != Prop)
              SCInvalidProof(SCProof(step), Nil, "ψ must be a formula, but it is a " + phi.sort)
            else {
              val phiImpPsi = implies(phi)(psi)
              val psiImpPhi = implies(psi)(phi)
              val phiIffPsi = iff(phi)(psi)
              if (isSameSet(b.left, ref(t1).left union ref(t2).left))
                if (
                  isSubset(ref(t1).right, b.right + phiImpPsi) &&
                  isSubset(ref(t2).right, b.right + psiImpPhi) &&
                  isSubset(b.right, ref(t1).right union ref(t2).right + phiIffPsi)
                )
                  SCValidProof(SCProof(step))
                else SCInvalidProof(SCProof(step), Nil, s"Right-hand side of conclusion + a⇒ψ + ψ⇒φ is not the same as the union of the right-hand sides of the premises φ⇔b.")
              else SCInvalidProof(SCProof(step), Nil, s"Left-hand side of conclusion is not the union of the left-hand sides of the premises.")
            }
          /*
           *  Γ, φ |- Δ
           * --------------
           *   Γ |- ¬φ, Δ
           */
          case RightNot(b, t1, phi) =>
            if (phi.sort != Prop)
              SCInvalidProof(SCProof(step), Nil, "φ must be a formula, but it is a " + phi.sort)
            else {
              val nPhi = neg(phi)
              if (isSameSet(b.right, ref(t1).right + nPhi))
                if (isSameSet(b.left + phi, ref(t1).left))
                  SCValidProof(SCProof(step))
                else SCInvalidProof(SCProof(step), Nil, "Left-hand side of conclusion + φ must be the same as left-hand side of premise")
              else SCInvalidProof(SCProof(step), Nil, "Right-hand side of conclusion must be the same as right-hand side of premise + ¬φ")
            }
          /*
           *    Γ |- φ, Δ
           * ------------------- if x is not free in the resulting sequent
           *  Γ |- ∀x. φ, Δ
           */
          case RightForall(b, t1, phi, x) =>
            if (phi.sort != Prop)
              SCInvalidProof(SCProof(step), Nil, "φ must be a formula, but it is a " + phi.sort)
            else if (x.sort != Ind)
              SCInvalidProof(SCProof(step), Nil, "x must be a term variable, but it is a " + x.sort)
            else if (isSameSet(b.left, ref(t1).left))
              if (isSameSet(b.right + phi, ref(t1).right + forall(Lambda(x, phi))))
                if ((b.left union b.right).forall(f => !f.freeVariables.contains(x)))
                  SCValidProof(SCProof(step))
                else SCInvalidProof(SCProof(step), Nil, "The variable x must not be free in the resulting sequent.")
              else SCInvalidProof(SCProof(step), Nil, "Right-hand side of conclusion + φ must be the same as right-hand side of premise + ∀x. φ")
            else SCInvalidProof(SCProof(step), Nil, "Left-hand sides of conclusion and premise must be the same.")
          /*
           *   Γ |- φ[t/x], Δ
           * -------------------
           *  Γ |- ∃x. φ, Δ
           */
          case RightExists(b, t1, phi, x, t) =>
            if (phi.sort != Prop)
              SCInvalidProof(SCProof(step), Nil, "φ must be a formula, but it is a " + phi.sort)
            else if (x.sort != Ind)
              SCInvalidProof(SCProof(step), Nil, "x must be a term variable, but it is a " + x.sort)
            else if (t.sort != Ind)
              SCInvalidProof(SCProof(step), Nil, "t must be a term , but it is a " + t.sort)
            else if (isSameSet(b.left, ref(t1).left))
              if (isSameSet(b.right + substituteVariables(phi, Map(x -> t)), ref(t1).right + exists(Lambda(x, phi))))
                SCValidProof(SCProof(step))
              else SCInvalidProof(SCProof(step), Nil, "Right-hand side of the conclusion + φ[t/x] must be the same as right-hand side of the premise + ∃x. φ")
            else SCInvalidProof(SCProof(step), Nil, "Left-hand sides or conclusion and premise must be the same.")

          /**
           * <pre>
           *       Γ |- φ[t/x], Δ
           * --------------------------
           *     Γ|- φ[(εx. φ)/x], Δ
           * </pre>
           */
          case RightEpsilon(b, t1, phi, x, t) =>
            if (phi.sort != Prop)
              SCInvalidProof(SCProof(step), Nil, "φ must be a formula, but it is a " + phi.sort)
            else if (x.sort != Ind)
              SCInvalidProof(SCProof(step), Nil, "x must be a term variable, but it is a " + x.sort)
            else if (t.sort != Ind)
              SCInvalidProof(SCProof(step), Nil, "t must be a term , but it is a " + t.sort)
            else if (isSameSet(b.left, ref(t1).left)) {
              val expected_top = substituteVariables(phi, Map(x -> t))
              val expected_bot = substituteVariables(phi, Map(x -> epsilon(Lambda(x, phi))))
              if (isSameSet(b.right + expected_top, ref(t1).right + expected_bot))
                SCValidProof(SCProof(step))
              else SCInvalidProof(SCProof(step), Nil, "Right-hand side of the conclusion + φ[t/x] must be the same as right-hand side of the premise + ∃x. φ")
            } else SCInvalidProof(SCProof(step), Nil, "Left-hand sides or conclusion and premise must be the same.")

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
                if (isSame(left, right))
                  if (isSameSet(b.right, ref(t1).right))
                    if (isSameSet(b.left + phi, ref(t1).left))
                      SCValidProof(SCProof(step))
                    else SCInvalidProof(SCProof(step), Nil, s"Left-hand sides of the conclusion + φ must be the same as left-hand side of the premise.")
                  else SCInvalidProof(SCProof(step), Nil, s"Right-hand sides of the premise and the conclusion aren't the same.")
                else SCInvalidProof(SCProof(step), Nil, s"φ is not an instance of reflexivity.")
              case _ => SCInvalidProof(SCProof(step), Nil, "φ is not an equality")
            }

          /*
           *
           * --------------
           *     |- s=s
           */
          case RightRefl(b, phi) =>
            phi match {
              case equality(left, right) =>
                if (isSame(left, right))
                  if (contains(b.right, phi))
                    SCValidProof(SCProof(step))
                  else SCInvalidProof(SCProof(step), Nil, s"Right-Hand side of conclusion does not contain φ")
                else SCInvalidProof(SCProof(step), Nil, s"φ is not an instance of reflexivity.")
              case _ => SCInvalidProof(SCProof(step), Nil, s"φ is not an equality.")
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

          /*
          /*
           *    Γ |- φ[ψ/?p], Δ
           * ---------------------
           *  Γ, ψ⇔τ |- φ[τ/?p], Δ
           */
          case RightSubstIff(b, t1, t2, psi, tau, vars, lambdaPhi) =>
            val (phi_arg, phi_body) = lambdaPhi
            if (psi.sort != phi_arg.sort || tau.sort != phi_arg.sort)
              SCInvalidProof(SCProof(step), Nil, "The types of the variable of φ must be the same as the types of ψ and τ.")
            else if (!psi.sort.isPredicate)
              SCInvalidProof(SCProof(step), Nil, "Can only substitute predicate-like terms (with type Ind -> ... -> Ind -> Prop)")
            else {
              val phi_s_for_f = substituteVariables(phi_body, Map(phi_arg -> psi))
              val phi_t_for_f = substituteVariables(phi_body, Map(phi_arg -> tau))

              val inner1 = vars.foldLeft(psi)(_(_))
              val inner2 = vars.foldLeft(tau)(_(_))
              val sEqt = iff(inner1)(inner2)
              val varss = vars.toSet

              if (
                isSubset(ref(t1).right, b.right + phi_s_for_f) &&
                isSubset(ref(t2).right, b.right + sEqt) &&
                isSubset(b.right, ref(t1).right union ref(t2).right + phi_t_for_f)
              ) {
                if (isSameSet(b.left, ref(t1).left union ref(t2).left)) {
                  if (
                    ref(t2).left.exists(f => f.freeVariables.intersect(varss).nonEmpty) ||
                    ref(t2).right.exists(f => !isSame(f, sEqt) && f.freeVariables.intersect(varss).nonEmpty)
                  ) {
                    SCInvalidProof(SCProof(step), Nil, "The variable x1...xn must not be free in the second premise other than as parameters of the equality.")
                  } else SCValidProof(SCProof(step))
                }
                else SCInvalidProof(SCProof(step), Nil, "Left-hand sides of the conclusion + φ(s_) must be the same as left-hand side of the premise + (s=t)_ + φ(t_).")
              }
              else SCInvalidProof(SCProof(step), Nil, "Right-hand sides of the premise and the conclusion aren't the same.")
            }

                                  /*
           *   Γ, φ(ψ) |- Δ     Σ |- a⇔b, Π
           * --------------------------------
           *        Γ, Σ φ(b) |- Δ, Π
           */
          case LeftSubstIff(b, t1, t2, psi, tau, vars, lambdaPhi) =>
            val (phi_arg, phi_body) = lambdaPhi
            if (psi.sort != phi_arg.sort || tau.sort != phi_arg.sort)
              SCInvalidProof(SCProof(step), Nil, "The types of the variable of φ must be the same as the types of ψ and τ.")
            else /*if (!psi.sort.isPredicate)
              SCInvalidProof(SCProof(step), Nil, "Can only substitute predicate-like terms (with type Ind -> ... -> Ind -> Prop)")
            else */{
              val phi_s_for_f = substituteVariables(phi_body, Map(phi_arg -> psi))
              val phi_t_for_f = substituteVariables(phi_body, Map(phi_arg -> tau))

              val inner1 = vars.foldLeft(psi)(_(_))
              val inner2 = vars.foldLeft(tau)(_(_))
              val sEqt = iff(inner1)(inner2)
              val varss = vars.toSet

              if (
                isSubset(ref(t1).right, b.right) &&
                isSubset(ref(t2).right, b.right + sEqt) &&
                isSubset(b.right, ref(t1).right union ref(t2).right)
              ) {
                if (
                  isSubset(ref(t1).left, b.left + phi_s_for_f) &&
                  isSubset(ref(t2).left, b.left) &&
                  isSubset(b.left, ref(t1).left union ref(t2).left + phi_t_for_f)
                ) {
                  if (
                    ref(t2).left.exists(f => f.freeVariables.intersect(varss).nonEmpty) ||
                    ref(t2).right.exists(f => !isSame(f, sEqt) && f.freeVariables.intersect(varss).nonEmpty)
                  ) {
                    SCInvalidProof(SCProof(step), Nil, "The variable x1...xn must not be free in the second premise other than as parameters of the equality.")
                  } else SCValidProof(SCProof(step))
                }
                else SCInvalidProof(SCProof(step), Nil, "Left-hand sides of the conclusion + φ(s_) must be the same as left-hand side of the premise + (s=t)_ + φ(t_).")
              }
              else SCInvalidProof(SCProof(step), Nil, "Right-hand sides of the premise and the conclusion aren't the same.")
            }
           */

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
