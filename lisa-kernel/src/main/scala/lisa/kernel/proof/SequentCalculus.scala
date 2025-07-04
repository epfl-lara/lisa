package lisa.kernel.proof

import lisa.kernel.fol.FOL._

/**
 * The concrete implementation of sequent calculus (with equality).
 * This file specifies the sequents and the allowed operations on them, the deduction rules of sequent calculus.
 * It contains typical sequent calculus rules for FOL with equality as can be found in a text book, as well as a couple more for
 * non-elementary symbols (⇔, ∃!) and rules for substituting equal terms or equivalent formulas. I also contains two structural rules,
 * subproof and a dummy rewrite step.
 * Further mathematical steps, such as introducing or using definitions, axioms or theorems are not part of the basic sequent calculus.
 */
object SequentCalculus {

  /**
   * A sequent is an object that can contain two sets of formulas, [[left]] and [[right]].
   * The intended semantic is for the [[left]] formulas to be interpreted as a conjunction, while the [[right]] ones as a disjunction.
   * Traditionally, sequents are represented by two lists of formulas.
   * Since sequent calculus includes rules for permuting and weakening, it is in essence equivalent to sets.
   * Seqs make verifying proof steps much easier, but proof construction much more verbose and proofs longer.
   * @param left the left side of the sequent
   * @param right the right side of the sequent
   */
  case class Sequent(left: Set[Expression], right: Set[Expression]){
    require(left.forall(_.sort == Formula) && right.forall(_.sort == Formula), "Sequent can only contain formulas")
  }

  /**
   * Simple method that transforms a sequent to a logically equivalent formula.
   */
  def sequentToFormula(s: Sequent): Expression = {
    val left = {
      if  (s.left.isEmpty) top
      else if (s.left.size == 1) s.left.head
      else s.left.reduce(and(_)(_))
    }
    val right ={
      if  (s.right.isEmpty) bot
      else if (s.right.size == 1) s.right.head
      else s.right.reduce(or(_)(_))
    }
    implies(left)(right)
  }

  /**
   * Checks whether two sequents are equivalent, with respect to [[isSameTerm]].
   *
   * @param l the first sequent
   * @param r the second sequent
   * @return see [[isSameTerm]]
   */
  def isSameSequent(l: Sequent, r: Sequent): Boolean = isSame(sequentToFormula(l), sequentToFormula(r))

  /**
   * Checks whether a given sequent implies another, with respect to [[latticeLEQ]].
   *
   * @param l the first sequent
   * @param r the second sequent
   * @return see [[latticeLEQ]]
   */
  def isImplyingSequent(l: Sequent, r: Sequent): Boolean = isImplying(sequentToFormula(l), sequentToFormula(r))

  /**
   * The parent of all proof steps types.
   * A proof step is a deduction rule of sequent calculus, with the sequents forming the prerequisite and conclusion.
   * For easier linearisation of the proof, the prerequisite are represented with numbers showing the place in the proof of the sequent used.
   */

  /**
   * The parent of all sequent calculus rules.
   */
  sealed trait SCProofStep {
    val bot: Sequent
    val premises: Seq[Int]
  }

  /**
   * <pre>
   *    Γ |- Δ
   * ------------
   *    Γ |- Δ  (OL rewrite)
   * </pre>
   */
  case class Restate(bot: Sequent, t1: Int) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *
   * ------------
   *    Γ |- Γ  (OL tautology)
   * </pre>
   */
  case class RestateTrue(bot: Sequent) extends SCProofStep { val premises = Seq() }

  /**
   * <pre>
   *
   * --------------
   *   Γ, φ |- φ, Δ
   * </pre>
   */
  case class Hypothesis(bot: Sequent, phi: Expression) extends SCProofStep { val premises = Seq() }

  /**
   * <pre>
   *  Γ |- Δ, φ    φ, Σ |- Π
   * ------------------------
   *       Γ, Σ |-Δ, Π
   * </pre>
   */
  case class Cut(bot: Sequent, t1: Int, t2: Int, phi: Expression) extends SCProofStep { val premises = Seq(t1, t2) }

  // Left rules
  /**
   * <pre>
   *   Γ, φ |- Δ                Γ, φ, ψ |- Δ
   * --------------     or     --------------
   *  Γ, φ∧ψ |- Δ               Γ, φ∧ψ |- Δ
   * </pre>
   */
  case class LeftAnd(bot: Sequent, t1: Int, phi: Expression, psi: Expression) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *  Γ, φ |- Δ    Σ, ψ |- Π    ...
   * --------------------------------
   *    Γ, Σ, φ∨ψ∨... |- Δ, Π
   * </pre>
   */
  case class LeftOr(bot: Sequent, t: Seq[Int], disjuncts: Seq[Expression]) extends SCProofStep { val premises = t }

  /**
   * <pre>
   *  Γ |- φ, Δ    Σ, ψ |- Π
   * ------------------------
   *    Γ, Σ, φ⇒ψ |- Δ, Π
   * </pre>
   */
  case class LeftImplies(bot: Sequent, t1: Int, t2: Int, phi: Expression, psi: Expression) extends SCProofStep { val premises = Seq(t1, t2) }

  /**
   * <pre>
   *  Γ, φ⇒ψ |- Δ               Γ, φ⇒ψ, ψ⇒φ |- Δ
   * --------------    or     --------------------
   *  Γ, φ⇔ψ |- Δ                 Γ, φ⇔ψ |- Δ
   * </pre>
   */
  case class LeftIff(bot: Sequent, t1: Int, phi: Expression, psi: Expression) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *   Γ |- φ, Δ
   * --------------
   *   Γ, ¬φ |- Δ
   * </pre>
   */
  case class LeftNot(bot: Sequent, t1: Int, phi: Expression) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *   Γ, φ[t/x] |- Δ
   * -------------------
   *  Γ, ∀ φ |- Δ
   *
   * </pre>
   */
  case class LeftForall(bot: Sequent, t1: Int, phi: Expression, x: Variable, t: Expression) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *    Γ, φ |- Δ
   * ------------------- if x is not free in the resulting sequent
   *  Γ, ∃x φ|- Δ
   *
   * </pre>
   */
  case class LeftExists(bot: Sequent, t1: Int, phi: Expression, x: Variable) extends SCProofStep { val premises = Seq(t1) }

  // Right rules
  /**
   * <pre>
   *  Γ |- φ, Δ    Σ |- ψ, Π     ...
   * ------------------------------------
   *    Γ, Σ |- φ∧ψ∧..., Π, Δ
   * </pre>
   */
  case class RightAnd(bot: Sequent, t: Seq[Int], cunjuncts: Seq[Expression]) extends SCProofStep { val premises = t }

  /**
   * <pre>
   *   Γ |- φ, Δ                Γ |- φ, ψ, Δ
   * --------------    or    ---------------
   *  Γ |- φ∨ψ, Δ              Γ |- φ∨ψ, Δ
   * </pre>
   */
  case class RightOr(bot: Sequent, t1: Int, phi: Expression, psi: Expression) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *  Γ, φ |- ψ, Δ
   * --------------
   *  Γ |- φ⇒ψ, Δ
   * </pre>
   */
  case class RightImplies(bot: Sequent, t1: Int, phi: Expression, psi: Expression) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *  Γ |- a⇒ψ, Δ    Σ |- ψ⇒φ, Π
   * ----------------------------
   *      Γ, Σ |- φ⇔ψ, Π, Δ
   * </pre>
   */
  case class RightIff(bot: Sequent, t1: Int, t2: Int, phi: Expression, psi: Expression) extends SCProofStep { val premises = Seq(t1, t2) }

  /**
   * <pre>
   *  Γ, φ |- Δ
   * --------------
   *   Γ |- ¬φ, Δ
   * </pre>
   */
  case class RightNot(bot: Sequent, t1: Int, phi: Expression) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *    Γ |- φ, Δ
   * ------------------- if x is not free in the resulting sequent
   *  Γ |- ∀x. φ, Δ
   * </pre>
   */
  case class RightForall(bot: Sequent, t1: Int, phi: Expression, x: Variable) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *   Γ |- φ[t/x], Δ
   * -------------------
   *  Γ |- ∃x. φ, Δ
   *
   * (ln-x stands for locally nameless x)
   * </pre>
   */
  case class RightExists(bot: Sequent, t1: Int, phi: Expression, x: Variable, t: Expression) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *       Γ |- φ[t/x], Δ
   * -------------------------- if y is not free in φ
   *    Γ|- φ[(εx. φ)/x],  Δ
   * </pre>
   */
  case class RightEpsilon(bot: Sequent, t1: Int, phi: Expression, x: Variable, t: Expression) extends SCProofStep { val premises = Seq(t1) }

  // Structural rule
  /**
   * <pre>
   *     Γ |- Δ
   * --------------
   *   Γ, Σ |- Δ, Π
   * </pre>
   */
  case class Weakening(bot: Sequent, t1: Int) extends SCProofStep { val premises = Seq(t1) }


  /**
   * <pre>
   *    Γ |- φ[(λy. e)t/x], Δ
   * ---------------------------
   *     Γ |- φ[e[t/y]/x], Δ
   * </pre>
   */
  case class Beta(bot: Sequent, t1: Int) extends SCProofStep { val premises = Seq(t1) }



  // Equality Rules
  /**
   * <pre>
   *  Γ, s=s |- Δ
   * --------------
   *     Γ |- Δ
   * </pre>
   */
  case class LeftRefl(bot: Sequent, t1: Int, fa: Expression) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *
   * --------------
   *     |- s=s
   * </pre>
   */
  case class RightRefl(bot: Sequent, fa: Expression) extends SCProofStep { val premises = Seq() }

  /**
   * <pre>
   *  Γ, φ(s) |- Δ     Σ1 |- s=t, Π     
   * ----------------------------------------
   *             Γ, Σ φ(t) |- Δ, Π
   * </pre>
   * equals elements must have type ... -> ... -> Term
   */
  //case class LeftSubstEq(bot: Sequent, t1: Int, equals: List[(LambdaTermTerm, LambdaTermTerm)], lambdaPhi: (Seq[SchematicTermLabel], Formula)) extends SCProofStep { val premises = Seq(t1) }
  case class LeftSubstEq(bot: Sequent, t1: Int, t2: Int, s: Expression, t: Expression, vars: Seq[Variable], lambdaPhi: (Variable, Expression)) extends SCProofStep { val premises = Seq(t1, t2) }

  /**
   * <pre>
   *  Γ |- φ(s), Δ     Σ1 |- s=t, Π
   * ---------------------------------
   *         Γ, Σ |- φ(t), Δ, Π
   * </pre>
   * equals elements must have type ... -> ... -> Term
   */
  case class RightSubstEq(bot: Sequent, t1: Int, t2: Int, s: Expression, t: Expression, vars: Seq[Variable], lambdaPhi: (Variable, Expression)) extends SCProofStep { val premises = Seq(t1, t2) }

  /**
   * <pre>
   *   Γ, φ(ψ) |- Δ     Σ |- ψ⇔τ, Π     
   * --------------------------------
   *        Γ, Σ φ(τ) |- Δ, Π
   * </pre>
   * equals elements must have type ... -> ... -> Formula
   */
  case class LeftSubstIff(bot: Sequent, t1: Int, t2: Int, psi: Expression, tau: Expression, vars: Seq[Variable], lambdaPhi: (Variable, Expression)) extends SCProofStep { val premises = Seq(t1, t2) }

  /**
   * <pre>
   *   Γ |- φ(ψ), Δ     Σ |- ψ⇔τ, Π     
   * --------------------------------
   *        Γ, Σ |- φ(τ), Δ, Π
   * </pre>
   * equals elements must have type ... -> ... -> Formula
   */
  case class RightSubstIff(bot: Sequent, t1: Int, t2: Int, psi: Expression, tau: Expression, vars: Seq[Variable], lambdaPhi: (Variable, Expression)) extends SCProofStep { val premises = Seq(t1, t2) }

  // Rule for schemas

  case class InstSchema(
      bot: Sequent,
      t1: Int,
      subst: Map[Variable, Expression]
  ) extends SCProofStep { val premises = Seq(t1) }

  // Proof Organisation rules

  /**
   * Encapsulate a proof into a single step. The imports of the subproof correspond to the premisces of the step.
   * @param sp The encapsulated subproof.
   * @param premises The indices of steps on the outside proof that are equivalent to the import of the subproof.
   * @param display A boolean value indicating whether the subproof needs to be expanded when printed. Should probably go and
   *                be replaced by encapsulation.
   */
  case class SCSubproof(sp: SCProof, premises: Seq[Int] = Seq.empty) extends SCProofStep {
    // premises is a list of ints similar to t1, t2... that verifies that imports of the subproof sp are justified by previous steps.
    val bot: Sequent = sp.conclusion
  }

  /**
   * <pre>
   *
   * --------------
   *   Γ  |- Δ
   * </pre>
   */
  case class Sorry(bot: Sequent) extends SCProofStep { val premises = Seq() }

}