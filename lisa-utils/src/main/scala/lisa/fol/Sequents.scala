package lisa.fol

//import lisa.kernel.proof.SequentCalculus.Sequent

import lisa.fol.FOLHelpers.*
import lisa.prooflib.BasicStepTactic
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib.ProofTactic
import lisa.utils.K

import scala.annotation.showAsInfix

trait Sequents extends Common with lisa.fol.Lambdas {
  object SequentInstantiationRule extends ProofTactic
  given ProofTactic = SequentInstantiationRule

  case class Sequent(left: Set[Formula], right: Set[Formula]) extends LisaObject[Sequent] with Absolute {
    def underlying: lisa.kernel.proof.SequentCalculus.Sequent = K.Sequent(left.map(_.underlying), right.map(_.underlying))

    def allSchematicLabels: Set[SchematicLabel[?]] = left.flatMap(_.allSchematicLabels)
    def freeSchematicLabels: Set[SchematicLabel[?]] = left.flatMap(_.freeSchematicLabels)
    def substituteUnsafe(map: Map[SchematicLabel[?], ? <: LisaObject[?]]): Sequent = Sequent(left.map(_.substituteUnsafe(map)), right.map(_.substituteUnsafe(map)))

    /*Ok for now but what when we have more*/
    /**
     * Substitute schematic symbols inside this, and produces a kernel proof.
     * Namely, if "that" is the result of the substitution, the proof should conclude with "that.underlying",
     * using the assumption "this.underlying" at step index -1.
     *
     * @param map
     * @return
     */
    def substituteWithProof(map: Map[SchematicLabel[_], _ <: LisaObject[_]]): (Sequent, Seq[K.SCProofStep]) = {

      val mTerm: Map[SchematicFunctionLabel[?] | Variable, LambdaExpression[Term, Term, ?]] =
        map.collect[SchematicFunctionLabel[?] | Variable, LambdaExpression[Term, Term, ?]](p =>
          p._1 match {
            case sl: Variable => (sl, LambdaExpression[Term, Term, 0](Seq(), p._2.asInstanceOf[Term], 0))
            case sl: SchematicFunctionLabel[?] =>
              p._2 match {
                case l: LambdaExpression[Term, Term, ?] @unchecked if (l.bounds.isEmpty || l.bounds.head.isInstanceOf[Variable]) & l.body.isInstanceOf[Term] =>
                  (p._1.asInstanceOf, l)
                case s: TermLabel =>
                  val vars = nFreshId(Seq(s.id), s.arity).map(id => Variable(id))
                  (sl, LambdaExpression(vars, s(vars), s.arity))
              }
          }
        )
      val mPred: Map[SchematicPredicateLabel[?] | VariableFormula, LambdaExpression[Term, Formula, ?]] =
        map.collect[SchematicPredicateLabel[?] | VariableFormula, LambdaExpression[Term, Formula, ?]](p =>
          p._1 match {
            case sl: VariableFormula => (sl, LambdaExpression[Term, Formula, 0](Seq(), p._2.asInstanceOf[Formula], 0))
            case sl: SchematicPredicateLabel[?] =>
              p._2 match {
                case l: LambdaExpression[Term, Formula, ?] @unchecked if (l.bounds.isEmpty || l.bounds.head.isInstanceOf[Variable]) & l.body.isInstanceOf[Formula] => (sl, l)
                case s: PredicateLabel =>
                  val vars = nFreshId(Seq(s.id), s.arity).map(id => Variable(id))
                  (sl, LambdaExpression(vars, s(vars), s.arity))
              }
          }
        )
      val mConn = map.collect[SchematicConnectorLabel[?], LambdaExpression[Formula, Formula, ?]](p =>
        p._1 match {
          case sl: SchematicConnectorLabel[?] =>
            p._2 match {
              case l: LambdaExpression[Formula, Formula, ?] @unchecked if (l.bounds.isEmpty || l.bounds.head.isInstanceOf[VariableFormula]) & l.body.isInstanceOf[Formula] => (sl, l)
              case s: ConnectorLabel =>
                val vars = nFreshId(Seq(s.id), s.arity).map(VariableFormula.apply)
                (sl, LambdaExpression(vars, s(vars), s.arity))
            }
        }
      )
      (substituteUnsafe(map), substituteWithProofLikeKernel(mConn, mPred, mTerm))

    }

    /**
     * Given 3 substitution maps like the kernel accepts, i.e. Substitution of Predicate Connector and Term schemas, do the substitution
     * and produce the (one-step) kernel proof that the result is provable from the original sequent
     *
     * @param mCon The substitution of connector schemas
     * @param mPred The substitution of predicate schemas
     * @param mTerm The substitution of function schemas
     * @return
     */
    def substituteWithProofLikeKernel(
        mCon: Map[SchematicConnectorLabel[?], LambdaExpression[Formula, Formula, ?]],
        mPred: Map[SchematicPredicateLabel[?] | VariableFormula, LambdaExpression[Term, Formula, ?]],
        mTerm: Map[SchematicFunctionLabel[?] | Variable, LambdaExpression[Term, Term, ?]]
    ): Seq[K.SCProofStep] = {
      val premiseSequent = this.underlying
      val mConK = mCon.map((sl, le) => (sl.underlyingLabel, underlyingLFF(le)))
      val mPredK = mPred.map((sl, le) =>
        sl match {
          case v: VariableFormula => (v.underlyingLabel, underlyingLTF(le))
          case spl: SchematicPredicateLabel[?] => (spl.underlyingLabel, underlyingLTF(le))
        }
      )
      val mTermK = mTerm.map((sl, le) =>
        sl match {
          case v: Variable => (v.underlyingLabel, underlyingLTT(le))
          case sfl: SchematicFunctionLabel[?] => (sfl.underlyingLabel, underlyingLTT(le))
        }
      )
      val botK = lisa.utils.KernelHelpers.instantiateSchemaInSequent(premiseSequent, mConK, mPredK, mTermK)
      val smap = Map[SchematicLabel[?], LisaObject[?]]() ++ mCon ++ mPred ++ mTerm
      Seq(K.InstSchema(botK, -1, mConK, mPredK, mTermK))
    }

    infix def +<<(f: Formula): Sequent = this.copy(left = this.left + f)
    infix def -<<(f: Formula): Sequent = this.copy(left = this.left - f)
    infix def +>>(f: Formula): Sequent = this.copy(right = this.right + f)
    infix def ->>(f: Formula): Sequent = this.copy(right = this.right - f)
    infix def ++<<(s1: Sequent): Sequent = this.copy(left = this.left ++ s1.left)
    infix def --<<(s1: Sequent): Sequent = this.copy(left = this.left -- s1.left)
    infix def ++>>(s1: Sequent): Sequent = this.copy(right = this.right ++ s1.right)
    infix def -->>(s1: Sequent): Sequent = this.copy(right = this.right -- s1.right)
    infix def ++(s1: Sequent): Sequent = this.copy(left = this.left ++ s1.left, right = this.right ++ s1.right)
    infix def --(s1: Sequent): Sequent = this.copy(left = this.left -- s1.left, right = this.right -- s1.right)

    infix def removeLeft(f: Formula): Sequent = this.copy(left = this.left.filterNot(isSame(_, f)))
    infix def removeRight(f: Formula): Sequent = this.copy(right = this.right.filterNot(isSame(_, f)))
    infix def removeAllLeft(s1: Sequent): Sequent = this.copy(left = this.left.filterNot(e1 => s1.left.exists(e2 => isSame(e1, e2))))
    infix def removeAllLeft(s1: Set[Formula]): Sequent = this.copy(left = this.left.filterNot(e1 => s1.exists(e2 => isSame(e1, e2))))
    infix def removeAllRight(s1: Sequent): Sequent = this.copy(right = this.right.filterNot(e1 => s1.right.exists(e2 => isSame(e1, e2))))
    infix def removeAllRight(s1: Set[Formula]): Sequent = this.copy(right = this.right.filterNot(e1 => s1.exists(e2 => isSame(e1, e2))))
    infix def removeAll(s1: Sequent): Sequent =
      this.copy(left = this.left.filterNot(e1 => s1.left.exists(e2 => isSame(e1, e2))), right = this.right.filterNot(e1 => s1.right.exists(e2 => isSame(e1, e2))))

    infix def addLeftIfNotExists(f: Formula): Sequent = if (this.left.exists(isSame(_, f))) this else (this +<< f)
    infix def addRightIfNotExists(f: Formula): Sequent = if (this.right.exists(isSame(_, f))) this else (this +>> f)
    infix def addAllLeftIfNotExists(s1: Sequent): Sequent = this ++<< s1.copy(left = s1.left.filterNot(e1 => this.left.exists(isSame(_, e1))))
    infix def addAllRightIfNotExists(s1: Sequent): Sequent = this ++>> s1.copy(right = s1.right.filterNot(e1 => this.right.exists(isSame(_, e1))))
    infix def addAllIfNotExists(s1: Sequent): Sequent =
      this ++ s1.copy(left = s1.left.filterNot(e1 => this.left.exists(isSame(_, e1))), right = s1.right.filterNot(e1 => this.right.exists(isSame(_, e1))))

    // OL shorthands
    infix def +<?(f: Formula): Sequent = this addLeftIfNotExists f
    infix def -<?(f: Formula): Sequent = this removeLeft f
    infix def +>?(f: Formula): Sequent = this addRightIfNotExists f
    infix def ->?(f: Formula): Sequent = this removeRight f
    infix def ++<?(s1: Sequent): Sequent = this addAllLeftIfNotExists s1
    infix def --<?(s1: Sequent): Sequent = this removeAllLeft s1
    infix def ++>?(s1: Sequent): Sequent = this addAllRightIfNotExists s1
    infix def -->?(s1: Sequent): Sequent = this removeAllRight s1
    infix def --?(s1: Sequent): Sequent = this removeAll s1
    infix def ++?(s1: Sequent): Sequent = this addAllIfNotExists s1

    override def toString = left.mkString("; ") + " ⊢ " + right.mkString("; ")

  }

  val emptySeq: Sequent = Sequent(Set.empty, Set.empty)

  given Conversion[Formula, Sequent] = f => Sequent(Set.empty, Set(f))

  def isSame(formula1: Formula, formula2: Formula): Boolean = {
    K.isSame(formula1.underlying, formula2.underlying)
  }

  def isSameTerm(term1: Term, term2: Term): Boolean = {
    K.isSameTerm(term1.underlying, term2.underlying)
  }

  def isSameSequent(sequent1: Sequent, sequent2: Sequent): Boolean = {
    K.isSameSequent(sequent1.underlying, sequent2.underlying)
  }

  /**
   * returns true if the first argument implies the second by the laws of ortholattices.
   */
  def isImplying(formula1: Formula, formula2: Formula): Boolean = {
    K.isImplying(formula1.underlying, formula2.underlying)
  }
  def isImplyingSequent(sequent1: Sequent, sequent2: Sequent): Boolean = {
    K.isImplyingSequent(sequent1.underlying, sequent2.underlying)
  }

  def isSubset(s1: Set[Formula], s2: Set[Formula]): Boolean = {
    K.isSubset(s1.map(_.underlying), s2.map(_.underlying))
  }
  def isSameSet(s1: Set[Formula], s2: Set[Formula]): Boolean =
    K.isSameSet(s1.map(_.underlying), s2.map(_.underlying))

  def contains(s: Set[Formula], f: Formula): Boolean = {
    K.contains(s.map(_.underlying), f.underlying)
  }

  /**
   * Represents a converter of some object into a set.
   * @tparam S The type of elements in that set
   * @tparam T The type to convert from
   */
  protected trait FormulaSetConverter[T] {
    def apply(t: T): Set[Formula]
  }

  given FormulaSetConverter[Unit] with {
    override def apply(u: Unit): Set[Formula] = Set.empty
  }

  given FormulaSetConverter[EmptyTuple] with {
    override def apply(t: EmptyTuple): Set[Formula] = Set.empty
  }

  given [H <: Formula, T <: Tuple](using c: FormulaSetConverter[T]): FormulaSetConverter[H *: T] with {
    override def apply(t: H *: T): Set[Formula] = c.apply(t.tail) + t.head
  }

  given formula_to_set[T <: Formula]: FormulaSetConverter[T] with {
    override def apply(f: T): Set[Formula] = Set(f)
  }

  given iterable_to_set[T <: Formula, I <: Iterable[T]]: FormulaSetConverter[I] with {
    override def apply(s: I): Set[Formula] = s.toSet
  }

  private def any2set[A, T <: A](any: T)(using c: FormulaSetConverter[T]): Set[Formula] = c.apply(any)

  extension [A, T1 <: A](left: T1)(using FormulaSetConverter[T1]) {
    infix def |-[B, T2 <: B](right: T2)(using FormulaSetConverter[T2]): Sequent = Sequent(any2set(left), any2set(right))
    infix def ⊢[B, T2 <: B](right: T2)(using FormulaSetConverter[T2]): Sequent = Sequent(any2set(left), any2set(right))
  }

}
