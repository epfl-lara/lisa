package lisa.kernel.proof

import lisa.kernel.fol.FOL._

/**
 * The concrete implementation of sequent calculus (with equality).
 * This file specifies the sequents and the allowed operations on them, the deduction rules of sequent calculus.
 * It contains typical sequent calculus rules for FOL with equality as can be found in a text book, as well as a couple more for
 * non-elementary symbols (↔, ∃!) and rules for substituting equal terms or equivalent formulas. I also contains two structural rules,
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
  case class Sequent(left: Set[Formula], right: Set[Formula])

  /**
   * Simple method that transforms a sequent to a logically equivalent formula.
   */
  def sequentToFormula(s: Sequent): Formula = ConnectorFormula(Implies, List(ConnectorFormula(And, s.left.toSeq), ConnectorFormula(Or, s.right.toSeq)))

  /**
   * Checks whether two sequents are equivalent, with respect to [[isSame]].
   * @param l the first sequent
   * @param r the second sequent
   * @return see [[isSame]]
   */
  def isSameSequent(l: Sequent, r: Sequent): Boolean = isSame(sequentToFormula(l), sequentToFormula(r))

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
   *    Γ |- Δ
   * </pre>
   */
  case class Rewrite(bot: Sequent, t1: Int) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *
   * --------------
   *   Γ, φ |- φ, Δ
   * </pre>
   */
  case class Hypothesis(bot: Sequent, phi: Formula) extends SCProofStep { val premises = Seq() }

  /**
   * <pre>
   *  Γ |- Δ, φ    φ, Σ |- Π
   * ------------------------
   *       Γ, Σ |-Δ, Π
   * </pre>
   */
  case class Cut(bot: Sequent, t1: Int, t2: Int, phi: Formula) extends SCProofStep { val premises = Seq(t1, t2) }

  // Left rules
  /**
   * <pre>
   *   Γ, φ |- Δ                Γ, φ, ψ |- Δ
   * --------------     or     --------------
   *  Γ, φ∧ψ |- Δ               Γ, φ∧ψ |- Δ
   * </pre>
   */
  case class LeftAnd(bot: Sequent, t1: Int, phi: Formula, psi: Formula) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *  Γ, φ |- Δ    Σ, ψ |- Π    ...
   * --------------------------------
   *    Γ, Σ, φ∨ψ∨... |- Δ, Π
   * </pre>
   */
  case class LeftOr(bot: Sequent, t: Seq[Int], disjuncts: Seq[Formula]) extends SCProofStep { val premises = t }

  /**
   * <pre>
   *  Γ |- φ, Δ    Σ, ψ |- Π
   * ------------------------
   *    Γ, Σ, φ→ψ |- Δ, Π
   * </pre>
   */
  case class LeftImplies(bot: Sequent, t1: Int, t2: Int, phi: Formula, psi: Formula) extends SCProofStep { val premises = Seq(t1, t2) }

  /**
   * <pre>
   *  Γ, φ→ψ |- Δ               Γ, φ→ψ, ψ→φ |- Δ
   * --------------    or     --------------------
   *  Γ, φ↔ψ |- Δ                 Γ, φ↔ψ |- Δ
   * </pre>
   */
  case class LeftIff(bot: Sequent, t1: Int, phi: Formula, psi: Formula) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *   Γ |- φ, Δ
   * --------------
   *   Γ, ¬φ |- Δ
   * </pre>
   */
  case class LeftNot(bot: Sequent, t1: Int, phi: Formula) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *   Γ, φ[t/x] |- Δ
   * -------------------
   *  Γ, ∀ φ |- Δ
   *
   * </pre>
   */
  case class LeftForall(bot: Sequent, t1: Int, phi: Formula, x: VariableLabel, t: Term) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *    Γ, φ |- Δ
   * ------------------- if x is not free in the resulting sequent
   *  Γ, ∃x φ|- Δ
   *
   * </pre>
   */
  case class LeftExists(bot: Sequent, t1: Int, phi: Formula, x: VariableLabel) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *  Γ, ∃y.∀x. (x=y) ↔ φ |-  Δ
   * ---------------------------- if y is not free in φ
   *      Γ, ∃!x. φ |- Δ
   * </pre>
   */
  case class LeftExistsOne(bot: Sequent, t1: Int, phi: Formula, x: VariableLabel) extends SCProofStep { val premises = Seq(t1) }

  // Right rules
  /**
   * <pre>
   *  Γ |- φ, Δ    Σ |- ψ, Π     ...
   * ------------------------------------
   *    Γ, Σ |- φ∧ψ∧..., Π, Δ
   * </pre>
   */
  case class RightAnd(bot: Sequent, t: Seq[Int], cunjuncts: Seq[Formula]) extends SCProofStep { val premises = t }

  /**
   * <pre>
   *   Γ |- φ, Δ                Γ |- φ, ψ, Δ
   * --------------    or    ---------------
   *  Γ |- φ∨ψ, Δ              Γ |- φ∨ψ, Δ
   * </pre>
   */
  case class RightOr(bot: Sequent, t1: Int, phi: Formula, psi: Formula) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *  Γ, φ |- ψ, Δ
   * --------------
   *  Γ |- φ→ψ, Δ
   * </pre>
   */
  case class RightImplies(bot: Sequent, t1: Int, phi: Formula, psi: Formula) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *  Γ |- a→ψ, Δ    Σ |- ψ→φ, Π
   * ----------------------------
   *      Γ, Σ |- φ↔ψ, Π, Δ
   * </pre>
   */
  case class RightIff(bot: Sequent, t1: Int, t2: Int, phi: Formula, psi: Formula) extends SCProofStep { val premises = Seq(t1, t2) }

  /**
   * <pre>
   *  Γ, φ |- Δ
   * --------------
   *   Γ |- ¬φ, Δ
   * </pre>
   */
  case class RightNot(bot: Sequent, t1: Int, phi: Formula) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *    Γ |- φ, Δ
   * ------------------- if x is not free in the resulting sequent
   *  Γ |- ∀x. φ, Δ
   * </pre>
   */
  case class RightForall(bot: Sequent, t1: Int, phi: Formula, x: VariableLabel) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *   Γ |- φ[t/x], Δ
   * -------------------
   *  Γ |- ∃x. φ, Δ
   *
   * (ln-x stands for locally nameless x)
   * </pre>
   */
  case class RightExists(bot: Sequent, t1: Int, phi: Formula, x: VariableLabel, t: Term) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *  Γ |- ∃y.∀x. (x=y) ↔ φ, Δ
   * ---------------------------- if y is not free in φ
   *      Γ|- ∃!x. φ,  Δ
   * </pre>
   */
  case class RightExistsOne(bot: Sequent, t1: Int, phi: Formula, x: VariableLabel) extends SCProofStep { val premises = Seq(t1) }

  // Structural rules
  /**
   * <pre>
   *     Γ |- Δ
   * --------------
   *   Γ, Σ |- Δ, Π
   * </pre>
   */
  case class Weakening(bot: Sequent, t1: Int) extends SCProofStep { val premises = Seq(t1) }

  // Equality Rules
  /**
   * <pre>
   *  Γ, s=s |- Δ
   * --------------
   *     Γ |- Δ
   * </pre>
   */
  case class LeftRefl(bot: Sequent, t1: Int, fa: Formula) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *
   * --------------
   *     |- s=s
   * </pre>
   */
  case class RightRefl(bot: Sequent, fa: Formula) extends SCProofStep { val premises = Seq() }

  /**
   * <pre>
   *    Γ, φ(s1,...,sn) |- Δ
   * ---------------------
   *  Γ, s1=t1, ..., sn=tn, φ(t1,...tn) |- Δ
   * </pre>
   */
  case class LeftSubstEq(bot: Sequent, t1: Int, equals: List[(Term, Term)], lambdaPhi: LambdaTermFormula) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *    Γ |- φ(s1,...,sn), Δ
   * ---------------------
   *  Γ, s1=t1, ..., sn=tn |- φ(t1,...tn), Δ
   * </pre>
   */
  case class RightSubstEq(bot: Sequent, t1: Int, equals: List[(Term, Term)], lambdaPhi: LambdaTermFormula) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *    Γ, φ(a1,...an) |- Δ
   * ---------------------
   *  Γ, a1↔b1, ..., an↔bn, φ(b1,...bn) |- Δ
   * </pre>
   */
  case class LeftSubstIff(bot: Sequent, t1: Int, equals: List[(Formula, Formula)], lambdaPhi: LambdaFormulaFormula) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *    Γ |- φ(a1,...an), Δ
   * ---------------------
   *  Γ, a1↔b1, ..., an↔bn |- φ(b1,...bn), Δ
   * </pre>
   */
  case class RightSubstIff(bot: Sequent, t1: Int, equals: List[(Formula, Formula)], lambdaPhi: LambdaFormulaFormula) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *           Γ |- Δ
   * --------------------------
   *  Γ[r(a)/?f] |- Δ[r(a)/?f]
   * </pre>
   */
  case class InstFunSchema(bot: Sequent, t1: Int, insts: Map[SchematicTermLabel, LambdaTermTerm]) extends SCProofStep { val premises = Seq(t1) }

  /**
   * <pre>
   *           Γ |- Δ
   * --------------------------
   *  Γ[ψ(a)/?p] |- Δ[ψ(a)/?p]
   * </pre>
   */
  case class InstPredSchema(bot: Sequent, t1: Int, insts: Map[SchematicVarOrPredLabel, LambdaTermFormula]) extends SCProofStep { val premises = Seq(t1) }

  // Proof Organisation rules
  case class SCSubproof(sp: SCProof, premises: Seq[Int] = Seq.empty, display: Boolean = true) extends SCProofStep {
    // premises is a list of ints similar to t1, t2... that verifies that imports of the subproof sp are justified by previous steps.
    val bot: Sequent = sp.conclusion
  }

}
