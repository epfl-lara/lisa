package lisa.utils.fol

import lisa.utils.K
import lisa.utils.prooflib.BasicStepTactic
import lisa.utils.prooflib.Library
import lisa.utils.prooflib.ProofTacticLib.ProofTactic

import scala.annotation.showAsInfix

trait Sequents extends Predef {

  /**
   * Tactic witness for instantiating free variables in a sequent.
   */
  object SequentInstantiationRule extends ProofTactic
  given ProofTactic = SequentInstantiationRule

  /**
   * Represents a sequent in the sequent calculus.
   *
   * The left side are assumptions, and the right side are the (alternative) conclusions.
   * Corresponds to [[K.Sequent]] in the kernel.
   *
   * @param left Formulas on the left side of the sequent
   * @param right Formulas on the right side of the sequent
   */
  case class Sequent(left: Set[Expr[Prop]], right: Set[Expr[Prop]]) extends LisaObject {

    /**
     * The underlying kernel sequent.
     */
    def underlying: lisa.kernel.proof.SequentCalculus.Sequent = K.Sequent(left.map(_.underlying), right.map(_.underlying))

    def substituteUnsafe(m: Map[Variable[?], Expr[?]]): Sequent = Sequent(left.map(_.substituteUnsafe(m)), right.map(_.substituteUnsafe(m)))
    override def substituteWithCheck(m: Map[Variable[?], Expr[?]]): Sequent =
      super.substituteWithCheck(m).asInstanceOf[Sequent]
    override def substitute(pairs: SubstPair*): Sequent =
      super.substitute(pairs*).asInstanceOf[Sequent]

    def freeVars: Set[Variable[?]] = left.flatMap(_.freeVars) ++ right.flatMap(_.freeVars)
    def freeTermVars: Set[Variable[Ind]] = left.flatMap(_.freeTermVars) ++ right.flatMap(_.freeTermVars)
    def constants: Set[Constant[?]] = left.flatMap(_.constants) ++ right.flatMap(_.constants)

    /**
     * Instantiate schematic symbols inside this, and produces a kernel proof.
     * Namely, if "that" is the result of the substitution, the proof should conclude with "that.underlying",
     * using the assumption "this.underlying" at step index -1.
     *
     * @param map The substitution map
     * @return The sequent after substitution and the proof of the substitution
     */
    def instantiateWithProof(map: Map[Variable[?], Expr[?]], index: Int): (Sequent, Seq[K.SCProofStep]) = {
      (substituteUnsafe(map), instantiateWithProofLikeKernel(map, index))

    }

    /**
     * Instantiate the quantified variables in the conclusion of the sequent with the given terms.
     * The sequent must have a single universally quantified formula on the right side.
     */
    def instantiateForallWithProof(args: Seq[Expr[Ind]], index: Int): (Sequent, Seq[K.SCProofStep]) = {
      if this.right.size != 1 then throw new IllegalArgumentException("Right side of sequent must be a single universally quantified formula")
      this.right.head match {
        case r @ App(forall, Abs(x: Variable[Ind], f: Expr[Prop])) =>
          val t = args.head
          val newf = f.substitute(x := t)
          val s0 = K.Hypothesis((newf |- newf).underlying, newf.underlying)
          val s1 = K.LeftForall((r |- newf).underlying, index + 1, f.underlying, x.underlying, t.underlying)
          val s2 = K.Cut((this.left |- newf).underlying, index, index + 2, r.underlying)
          if args.tail.isEmpty then (this.left |- newf, Seq(s0, s1, s2))
          else
            (this.left |- newf).instantiateForallWithProof(args.tail, index + 3) match {
              case (s, p) => (s, Seq(s0, s1, s2) ++ p)
            }

        case _ => throw new IllegalArgumentException("Right side of sequent must be a single universally quantified formula")
      }

    }

    /**
     * Given 3 substitution maps like the kernel accepts, i.e. Substitution of Predicate Connector and Ind schemas, do the substitution
     * and produce the (one-step) kernel proof that the result is provable from the original sequent
     *
     * @param mCon The substitution of connector schemas
     * @param mPred The substitution of predicate schemas
     * @param mTerm The substitution of function schemas
     * @return
     */
    def instantiateWithProofLikeKernel(
        map: Map[Variable[?], Expr[?]],
        index: Int
    ): Seq[K.SCProofStep] = {
      val premiseSequent = this.underlying
      val mapK = map.map((v, e) => (v.underlying, e.underlying))
      val botK = lisa.utils.KernelHelpers.substituteVariablesInSequent(premiseSequent, mapK)
      Seq(K.InstSchema(botK, index, mapK))
    }

    /**
     * Add a formula to the left side of the sequent.
     */
    infix def +<<(f: Expr[Prop]): Sequent = this.copy(left = this.left + f)

    /**
     * Remove a formula from the left side of the sequent.
     */
    infix def -<<(f: Expr[Prop]): Sequent = this.copy(left = this.left - f)

    /**
     * Add a formula to the right side of the sequent.
     */
    infix def +>>(f: Expr[Prop]): Sequent = this.copy(right = this.right + f)

    /**
     * Remove a formula from the right side of the sequent.
     */
    infix def ->>(f: Expr[Prop]): Sequent = this.copy(right = this.right - f)

    /**
     *  Add all formulas from the left side of the given sequent to the left side of this sequent.
     */
    infix def ++<<(s1: Sequent): Sequent = this.copy(left = this.left ++ s1.left)

    /**
     * Remove all formulas from the left side of the given sequent from the left side of this sequent.
     */
    infix def --<<(s1: Sequent): Sequent = this.copy(left = this.left -- s1.left)

    /**
     * Add all formulas from the right side of the given sequent to the right side of this sequent.
     */
    infix def ++>>(s1: Sequent): Sequent = this.copy(right = this.right ++ s1.right)

    /**
     * Remove all formulas from the right side of the given sequent from the right side of this sequent.
     */
    infix def -->>(s1: Sequent): Sequent = this.copy(right = this.right -- s1.right)

    /**
     * Add all formulas on the left (and right) of the given sequent to the left (and right) of this sequent.
     */
    infix def ++(s1: Sequent): Sequent = this.copy(left = this.left ++ s1.left, right = this.right ++ s1.right)

    /**
     * Remove all formulas on the left (and right) of the given sequent from the left (and right) of this sequent.
     */
    infix def --(s1: Sequent): Sequent = this.copy(left = this.left -- s1.left, right = this.right -- s1.right)

    /**
     * Remove all formulas OL-same to the given formula from the left side of the sequent.
     */
    infix def removeLeft(f: Expr[Prop]): Sequent = this.copy(left = this.left.filterNot(isSame(_, f)))

    /**
     * Remove all formulas OL-same to the given formula from the right side of the sequent.
     */
    infix def removeRight(f: Expr[Prop]): Sequent = this.copy(right = this.right.filterNot(isSame(_, f)))

    /**
     * Remove all formulas OL-same to one of the formulas on the left side of the given sequent from the left side of the sequent.
     */
    infix def removeAllLeft(s1: Sequent): Sequent = this.copy(left = this.left.filterNot(e1 => s1.left.exists(e2 => isSame(e1, e2))))

    /**
     * Remove all formulas OL-same to one of the given formulas from the left side of the sequent.
     */
    infix def removeAllLeft(s1: Set[Expr[Prop]]): Sequent = this.copy(left = this.left.filterNot(e1 => s1.exists(e2 => isSame(e1, e2))))

    /**
     * Remove all formulas OL-same to one of the formulas on the right side of the given sequent from the right side of the sequent.
     */
    infix def removeAllRight(s1: Sequent): Sequent = this.copy(right = this.right.filterNot(e1 => s1.right.exists(e2 => isSame(e1, e2))))

    /**
     * Remove all formulas OL-same to one of the given formulas from the right side of the sequent.
     */
    infix def removeAllRight(s1: Set[Expr[Prop]]): Sequent = this.copy(right = this.right.filterNot(e1 => s1.exists(e2 => isSame(e1, e2))))

    /**
     * Remove all formulas OL-same to one of the formulas on the left (and right) side of the given sequent from the left (and right) side of the sequent.
     */
    infix def removeAll(s1: Sequent): Sequent =
      this.copy(left = this.left.filterNot(e1 => s1.left.exists(e2 => isSame(e1, e2))), right = this.right.filterNot(e1 => s1.right.exists(e2 => isSame(e1, e2))))

    /**
     * Add a formula to the left side of the sequent if there is not already a formula OL-same to it.
     */
    infix def addLeftIfNotExists(f: Expr[Prop]): Sequent = if (this.left.exists(isSame(_, f))) this else (this +<< f)

    /**
     * Add a formula to the right side of the sequent if there is not already a formula OL-same to it.
     */
    infix def addRightIfNotExists(f: Expr[Prop]): Sequent = if (this.right.exists(isSame(_, f))) this else (this +>> f)

    /**
     * Add all formulas from the left side of the given sequent to the left side of this sequent if there is not already a formula OL-same to it.
     */
    infix def addAllLeftIfNotExists(s1: Sequent): Sequent = this ++<< s1.copy(left = s1.left.filterNot(e1 => this.left.exists(isSame(_, e1))))

    /**
     * Add all formulas from the right side of the given sequent to the right side of this sequent if there is not already a formula OL-same to it.
     */
    infix def addAllRightIfNotExists(s1: Sequent): Sequent = this ++>> s1.copy(right = s1.right.filterNot(e1 => this.right.exists(isSame(_, e1))))

    /**
     * Add all formulas on the left (and right) of the given sequent to the left (and right) of this sequent if there is not already a formula OL-same to it.
     */
    infix def addAllIfNotExists(s1: Sequent): Sequent =
      this ++ s1.copy(left = s1.left.filterNot(e1 => this.left.exists(isSame(_, e1))), right = s1.right.filterNot(e1 => this.right.exists(isSame(_, e1))))

    // OL shorthands
    /**
     * Add a formula to the left side of the sequent if there is not already a formula OL-same to it.
     */
    infix def +<?(f: Expr[Prop]): Sequent = this addLeftIfNotExists f

    /**
     * Remove a formula from the left side of the sequent if there is a formula OL-same to it.
     */
    infix def -<?(f: Expr[Prop]): Sequent = this removeLeft f

    /**
     * Add a formula to the right side of the sequent if there is not already a formula OL-same to it.
     */
    infix def +>?(f: Expr[Prop]): Sequent = this addRightIfNotExists f

    /**
     * Remove a formula from the right side of the sequent if there is a formula OL-same to it.
     */
    infix def ->?(f: Expr[Prop]): Sequent = this removeRight f

    /**
     * Add all formulas from the left side of the given sequent to the left side of this sequent if there is not already a formula OL-same to it.
     */
    infix def ++<?(s1: Sequent): Sequent = this addAllLeftIfNotExists s1

    /**
     * Remove all formulas from the left side of the given sequent from the left side of this sequent.
     */
    infix def --<?(s1: Sequent): Sequent = this removeAllLeft s1

    /**
     * Add all formulas from the right side of the given sequent to the right side of this sequent if there is not already a formula OL-same to it.
     */
    infix def ++>?(s1: Sequent): Sequent = this addAllRightIfNotExists s1

    /**
     * Remove all formulas from the right side of the given sequent from the right side of this sequent.
     */
    infix def -->?(s1: Sequent): Sequent = this removeAllRight s1

    /**
     * Add all formulas on the left (and right) of the given sequent to the left (and right) of this sequent if there is not already a formula OL-same to it.
     */
    infix def --?(s1: Sequent): Sequent = this removeAll s1

    /**
     * Add all formulas on the left (and right) of the given sequent to the left (and right) of this sequent if there is not already a formula OL-same to it.
     */
    infix def ++?(s1: Sequent): Sequent = this addAllIfNotExists s1

    override def toString =
      (if left.size == 0 then "" else if left.size == 1 then left.head.toString else "( " + left.mkString(", ") + " )") +
        " ⊢ " +
        (if right.size == 0 then "" else if right.size == 1 then right.head.toString else "( " + right.mkString(", ") + " )")

  }

  /**
   * A sequent with empty left and right sides. Logically false.
   */
  val emptySeq: Sequent = Sequent(Set.empty, Set.empty)

  given Conversion[Expr[Prop], Sequent] = f => Sequent(Set.empty, Set(f))

  /**
   * Returns true if the two expressions are OL-same.
   */
  def isSame(e1: Expr[?], e2: Expr[?]): Boolean = {
    e1.sort == e2.sort && K.isSame(e1.underlying, e2.underlying)
  }

  /**
   * Returns true if the two sequents are OL-same.
   */
  def isSameSequent(sequent1: Sequent, sequent2: Sequent): Boolean = {
    K.isSameSequent(sequent1.underlying, sequent2.underlying)
  }

  /**
   * Returns true if the first expression OL-implies the second expression.
   */
  def isImplying[S: Sort](e1: Expr[Prop], e2: Expr[Prop]): Boolean = {
    K.isImplying(e1.underlying, e2.underlying)
  }

  /**
   * Returns true if the first sequent OL-implies the second sequent.
   */
  def isImplyingSequent(sequent1: Sequent, sequent2: Sequent): Boolean = {
    K.isImplyingSequent(sequent1.underlying, sequent2.underlying)
  }

  /**
   * Returns true if for all formulas on `s1`, there is a formula OL-same to it in `s2`.
   */
  def isSubset[A, B](s1: Set[Expr[A]], s2: Set[Expr[B]]): Boolean = {
    K.isSubset(s1.map(_.underlying), s2.map(_.underlying))
  }

  /**
   * Returns true if the two sets are OL-same.
   */
  def isSameSet[A, B](s1: Set[Expr[A]], s2: Set[Expr[B]]): Boolean =
    K.isSameSet(s1.map(_.underlying), s2.map(_.underlying))

  /**
   * Returns true if `s` contains a formula OL-same to `f`.
   */
  def contains[A, B](s: Set[Expr[A]], f: Expr[B]): Boolean = {
    K.contains(s.map(_.underlying), f.underlying)
  }

  /**
   * Represents a converter of some object into a set of formulas.
   * @tparam T The type to convert from
   */
  trait FormulaSetConverter[-T] {
    def apply(t: T): Set[Expr[Prop]]
  }

  def toFormulaSet[T](x: T)(using converter: FormulaSetConverter[T]): Set[Expr[Prop]] = converter(x)

  given FormulaSetConverter[Unit] = _ => Set()
  given FormulaSetConverter[EmptyTuple] = _ => Set()

  given [H, T <: Tuple](using FormulaSetConverter[H], FormulaSetConverter[T]): FormulaSetConverter[H *: T] =
    t => toFormulaSet(t.head) ++ toFormulaSet(t.tail)

  given FormulaSetConverter[Expr[Prop]] = Set(_)
  given FormulaSetConverter[Iterable[Expr[Prop]]] = _.toSet

  extension [L](left: L)(using FormulaSetConverter[L]) {

    /**
     * Infix shorthand for constructing a [[Sequent]].
     */
    infix def |-[R](right: R)(using FormulaSetConverter[R]): Sequent = Sequent(toFormulaSet(left), toFormulaSet(right))
  }

}
