package lisa.utils.fol

import lisa.utils.prooflib.BasicStepTactic
import lisa.utils.prooflib.Library
import lisa.utils.prooflib.ProofTacticLib.ProofTactic

import lisa.utils.K

import scala.annotation.showAsInfix

trait Sequents extends Predef {
  
  
  object SequentInstantiationRule extends ProofTactic
  given ProofTactic = SequentInstantiationRule

  case class Sequent(left: Set[Expr[Prop]], right: Set[Expr[Prop]]) extends LisaObject{
    def underlying: lisa.kernel.proof.SequentCalculus.Sequent = K.Sequent(left.map(_.underlying), right.map(_.underlying))

    def substituteUnsafe(m: Map[Variable[?], Expr[?]]): Sequent = Sequent(left.map(_.substituteUnsafe(m)), right.map(_.substituteUnsafe(m)))
    override def substituteWithCheck(m: Map[Variable[?], Expr[?]]): Sequent =
      super.substituteWithCheck(m).asInstanceOf[Sequent]
    override def substitute(pairs: SubstPair*): Sequent =
      super.substitute(pairs*).asInstanceOf[Sequent]

    def freeVars: Set[Variable[?]] = left.flatMap(_.freeVars) ++ right.flatMap(_.freeVars)
    def freeTermVars: Set[Variable[Ind]] = left.flatMap(_.freeTermVars) ++ right.flatMap(_.freeTermVars)
    def constants: Set[Constant[?]] = left.flatMap(_.constants) ++ right.flatMap(_.constants)



    
    
    /*Ok for now but what when we have more*/
    /**
     * Substitute schematic symbols inside this, and produces a kernel proof.
     * Namely, if "that" is the result of the substitution, the proof should conclude with "that.underlying",
     * using the assumption "this.underlying" at step index -1.
     *
     * @param map
     * @return
     */
    def instantiateWithProof(map: Map[Variable[?], Expr[?]], index: Int): (Sequent, Seq[K.SCProofStep]) = {
      (substituteUnsafe(map), instantiateWithProofLikeKernel(map, index))

    }

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


    infix def +<<(f: Expr[Prop]): Sequent = this.copy(left = this.left + f)
    infix def -<<(f: Expr[Prop]): Sequent = this.copy(left = this.left - f)
    infix def +>>(f: Expr[Prop]): Sequent = this.copy(right = this.right + f)
    infix def ->>(f: Expr[Prop]): Sequent = this.copy(right = this.right - f)
    infix def ++<<(s1: Sequent): Sequent = this.copy(left = this.left ++ s1.left)
    infix def --<<(s1: Sequent): Sequent = this.copy(left = this.left -- s1.left)
    infix def ++>>(s1: Sequent): Sequent = this.copy(right = this.right ++ s1.right)
    infix def -->>(s1: Sequent): Sequent = this.copy(right = this.right -- s1.right)
    infix def ++(s1: Sequent): Sequent = this.copy(left = this.left ++ s1.left, right = this.right ++ s1.right)
    infix def --(s1: Sequent): Sequent = this.copy(left = this.left -- s1.left, right = this.right -- s1.right)

    infix def removeLeft(f: Expr[Prop]): Sequent = this.copy(left = this.left.filterNot(isSame(_, f)))
    infix def removeRight(f: Expr[Prop]): Sequent = this.copy(right = this.right.filterNot(isSame(_, f)))
    infix def removeAllLeft(s1: Sequent): Sequent = this.copy(left = this.left.filterNot(e1 => s1.left.exists(e2 => isSame(e1, e2))))
    infix def removeAllLeft(s1: Set[Expr[Prop]]): Sequent = this.copy(left = this.left.filterNot(e1 => s1.exists(e2 => isSame(e1, e2))))
    infix def removeAllRight(s1: Sequent): Sequent = this.copy(right = this.right.filterNot(e1 => s1.right.exists(e2 => isSame(e1, e2))))
    infix def removeAllRight(s1: Set[Expr[Prop]]): Sequent = this.copy(right = this.right.filterNot(e1 => s1.exists(e2 => isSame(e1, e2))))
    infix def removeAll(s1: Sequent): Sequent =
      this.copy(left = this.left.filterNot(e1 => s1.left.exists(e2 => isSame(e1, e2))), right = this.right.filterNot(e1 => s1.right.exists(e2 => isSame(e1, e2))))

    infix def addLeftIfNotExists(f: Expr[Prop]): Sequent = if (this.left.exists(isSame(_, f))) this else (this +<< f)
    infix def addRightIfNotExists(f: Expr[Prop]): Sequent = if (this.right.exists(isSame(_, f))) this else (this +>> f)
    infix def addAllLeftIfNotExists(s1: Sequent): Sequent = this ++<< s1.copy(left = s1.left.filterNot(e1 => this.left.exists(isSame(_, e1))))
    infix def addAllRightIfNotExists(s1: Sequent): Sequent = this ++>> s1.copy(right = s1.right.filterNot(e1 => this.right.exists(isSame(_, e1))))
    infix def addAllIfNotExists(s1: Sequent): Sequent =
      this ++ s1.copy(left = s1.left.filterNot(e1 => this.left.exists(isSame(_, e1))), right = s1.right.filterNot(e1 => this.right.exists(isSame(_, e1))))

    // OL shorthands
    infix def +<?(f: Expr[Prop]): Sequent = this addLeftIfNotExists f
    infix def -<?(f: Expr[Prop]): Sequent = this removeLeft f
    infix def +>?(f: Expr[Prop]): Sequent = this addRightIfNotExists f
    infix def ->?(f: Expr[Prop]): Sequent = this removeRight f
    infix def ++<?(s1: Sequent): Sequent = this addAllLeftIfNotExists s1
    infix def --<?(s1: Sequent): Sequent = this removeAllLeft s1
    infix def ++>?(s1: Sequent): Sequent = this addAllRightIfNotExists s1
    infix def -->?(s1: Sequent): Sequent = this removeAllRight s1
    infix def --?(s1: Sequent): Sequent = this removeAll s1
    infix def ++?(s1: Sequent): Sequent = this addAllIfNotExists s1

    override def toString =
      (if left.size == 0 then "" else if left.size == 1 then left.head.toString else "( " + left.mkString(", ") + " )") +
        " ⊢ " +
        (if right.size == 0 then "" else if right.size == 1 then right.head.toString else "( " + right.mkString(", ") + " )")

  }

  val emptySeq: Sequent = Sequent(Set.empty, Set.empty)

  given Conversion[Expr[Prop], Sequent] = f => Sequent(Set.empty, Set(f))

  def isSame(e1: Expr[?], e2: Expr[?]): Boolean = {
    e1.sort == e2.sort && K.isSame(e1.underlying, e2.underlying)
  }

  def isSameSequent(sequent1: Sequent, sequent2: Sequent): Boolean = {
    K.isSameSequent(sequent1.underlying, sequent2.underlying)
  }

  /**
   * returns true if the first argument implies the second by the laws of ortholattices.
   */
  def isImplying[S: Sort](e1: Expr[Prop], e2: Expr[Prop]): Boolean = {
    K.isImplying(e1.underlying, e2.underlying)
  }
  def isImplyingSequent(sequent1: Sequent, sequent2: Sequent): Boolean = {
    K.isImplyingSequent(sequent1.underlying, sequent2.underlying)
  }

  def isSubset[A, B](s1: Set[Expr[A]], s2: Set[Expr[B]]): Boolean = {
    K.isSubset(s1.map(_.underlying), s2.map(_.underlying))
  }
  def isSameSet[A, B](s1: Set[Expr[A]], s2: Set[Expr[B]]): Boolean =
    K.isSameSet(s1.map(_.underlying), s2.map(_.underlying))

  def contains[A, B](s: Set[Expr[A]], f: Expr[B]): Boolean = {
    K.contains(s.map(_.underlying), f.underlying)
  }

  /**
   * Represents a converter of some object into a set.
   * @tparam S The type of elements in that set
   * @tparam T The type to convert from
   */
  trait FormulaSetConverter[T] {
    def apply(t: T): Set[Expr[Prop]]
  }

  given FormulaSetConverter[Unit] with {
    override def apply(u: Unit): Set[Expr[Prop]] = Set.empty
  }

  given FormulaSetConverter[EmptyTuple] with {
    override def apply(t: EmptyTuple): Set[Expr[Prop]] = Set.empty
  }

  given [H <: Expr[Prop], T <: Tuple](using c: FormulaSetConverter[T]): FormulaSetConverter[H *: T] with {
    override def apply(t: H *: T): Set[Expr[Prop]] = c.apply(t.tail) + t.head
  }

  given formula_to_set[T <: Expr[Prop]]: FormulaSetConverter[T] with {
    override def apply(f: T): Set[Expr[Prop]] = Set(f)
  }

  given iterable_to_set[T <: Expr[Prop], I <: Iterable[T]]: FormulaSetConverter[I] with {
    override def apply(s: I): Set[Expr[Prop]] = s.toSet
  }

  private def any2set[A, T <: A](any: T)(using c: FormulaSetConverter[T]): Set[Expr[Prop]] = c.apply(any)

  extension [A, T1 <: A](left: T1)(using FormulaSetConverter[T1]) {
    infix def |-[B, T2 <: B](right: T2)(using FormulaSetConverter[T2]): Sequent = Sequent(any2set(left), any2set(right))
    infix def ⊢[B, T2 <: B](right: T2)(using FormulaSetConverter[T2]): Sequent = Sequent(any2set(left), any2set(right))
  }

}
