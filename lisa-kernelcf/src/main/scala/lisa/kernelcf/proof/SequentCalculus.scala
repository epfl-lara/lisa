package lisa.kernelcf.proof

import lisa.kernelcf.fol.FOL._

/** Sequents and their OL-aware comparison helpers. */
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
  case class Sequent(left: Set[Expression], right: Set[Expression]) {
    require(left.forall(_.sort == Prop) && right.forall(_.sort == Prop), "Sequent can only contain formulas")
  }

  /**
   * Simple method that transforms a sequent to a logically equivalent formula.
   */
  def sequentToFormula(s: Sequent): Expression = {
    val left = {
      if (s.left.isEmpty) top
      else if (s.left.size == 1) s.left.head
      else s.left.reduce(and(_)(_))
    }
    val right = {
      if (s.right.isEmpty) bot
      else if (s.right.size == 1) s.right.head
      else s.right.reduce(or(_)(_))
    }
    if (s.left.isEmpty) right
    else implies(left)(right)
  }

  /**
   * Checks whether two sequents are equivalent, with respect to [[isSame]].
   *
   * @param l the first sequent
   * @param r the second sequent
   * @return see [[isSame]]
   */
  def isSameSequent(l: Sequent, r: Sequent): Boolean = isSame(sequentToFormula(l), sequentToFormula(r))

  /**
   * Checks whether a given sequent implies another, with respect to [[isImplying]].
   *
   * @param l the first sequent
   * @param r the second sequent
   * @return see [[isImplying]]
   */
  def isImplyingSequent(l: Sequent, r: Sequent): Boolean = isImplying(sequentToFormula(l), sequentToFormula(r))

}
