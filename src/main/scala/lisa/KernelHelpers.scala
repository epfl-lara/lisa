package lisa

/**
 * A helper file that provides various syntactic sugars for LISA.
 * Usage:
 * <pre>
 * import lisa.KernelHelpers.*
 * </pre>
 */
object KernelHelpers {

  import lisa.kernel.proof.SequentCalculus.Sequent
  import lisa.kernel.fol.FOL.*

  /* Prefix syntax */

  def neg(f: Formula): Formula = ConnectorFormula(Neg, Seq(f))
  def and(l: Formula, r: Formula): Formula = ConnectorFormula(And, Seq(l, r))
  def or(l: Formula, r: Formula): Formula = ConnectorFormula(Or, Seq(l, r))
  def implies(l: Formula, r: Formula): Formula = ConnectorFormula(Implies, Seq(l, r))
  def iff(l: Formula, r: Formula): Formula = ConnectorFormula(Iff, Seq(l, r))
  def forall(label: VariableLabel, body: Formula): Formula = BinderFormula(Forall, label, body)
  def exists(label: VariableLabel, body: Formula): Formula = BinderFormula(Exists, label, body)
  def existsOne(label: VariableLabel, body: Formula): Formula = BinderFormula(ExistsOne, label, body)
  def equ(l: Term, r: Term): Formula = PredicateFormula(equality, Seq(l, r))

  extension (label: PredicateLabel)
    def apply(args: Term*): Formula = PredicateFormula(label, args)

  extension (label: ConnectorLabel)
    def apply(args: Formula*): Formula = ConnectorFormula(label, args)

  extension (label: FunctionLabel)
    def apply(args: Term*): Term = FunctionTerm(label, args)

  extension (label: BinderLabel)
    def apply(bound: VariableLabel, inner: Formula): Formula = BinderFormula(label, bound, inner)

  /* Infix syntax */

  extension (f: Formula) {
    def unary_! : Formula = neg(f)
    infix def ==>(g: Formula): Formula = implies(f, g)
    infix def <=>(g: Formula): Formula = iff(f, g)
    infix def /\(g: Formula): Formula = and(f, g)
    infix def \/(g: Formula): Formula = or(f, g)
  }

  extension (t: Term)
    infix def ===(u: Term): Formula = PredicateFormula(equality, Seq(t, u))

  /* Pattern matching extractors */

  object ! {
    def unapply(f: Formula): Option[Formula] = f match {
      case ConnectorFormula(`Neg`, Seq(g)) => Some(g)
      case _ => None
    }
  }

  sealed abstract class UnapplyBinaryConnector(label: ConnectorLabel) {
    def unapply(f: Formula): Option[(Formula, Formula)] = f match {
      case ConnectorFormula(`label`, Seq(a, b)) => Some((a, b))
      case _ => None
    }
  }
  object ==> extends UnapplyBinaryConnector(Implies)
  object <=> extends UnapplyBinaryConnector(Iff)
  object /\ extends UnapplyBinaryConnector(And)
  object \/ extends UnapplyBinaryConnector(Or)

  sealed abstract class UnapplyBinaryPredicate(label: PredicateLabel) {
    def unapply(f: Formula): Option[(Term, Term)] = f match {
      case PredicateFormula(`label`, Seq(a, b)) => Some((a, b))
      case _ => None
    }
  }
  object === extends UnapplyBinaryPredicate(equality)

  /* Conversions */

  given Conversion[VariableLabel, VariableTerm] = VariableTerm.apply
  given Conversion[VariableTerm, VariableLabel] = _.label

  given Conversion[PredicateFormula, PredicateLabel] = _.label

  given Conversion[FunctionTerm, FunctionLabel] = _.label

  // given Conversion[Tuple, List[Union[_.type]]] = _.toList

  given Conversion[(Boolean, List[Int], String), Option[(List[Int], String)]] = tr => if (tr._1) None else Some(tr._2, tr._3)

  /* Sequents */

  val emptySeq: Sequent = Sequent(Set.empty, Set.empty)

  extension (s: Sequent) {
    infix def +<(f: Formula): Sequent = s.copy(left = s.left + f)
    infix def -<(f: Formula): Sequent = s.copy(left = s.left - f)
    infix def +>(f: Formula): Sequent = s.copy(right = s.right + f)
    infix def ->(f: Formula): Sequent = s.copy(right = s.right - f)
    infix def ++<(s1: Sequent): Sequent = s.copy(left = s.left ++ s1.left)
    infix def --<(s1: Sequent): Sequent = s.copy(left = s.left -- s1.left)
    infix def ++>(s1: Sequent): Sequent = s.copy(right = s.right ++ s1.right)
    infix def -->(s1: Sequent): Sequent = s.copy(right = s.right -- s1.right)
    infix def ++(s1: Sequent): Sequent = s.copy(left = s.left ++ s1.left, right = s.right ++ s1.right)
    infix def --(s1: Sequent): Sequent = s.copy(left = s.left -- s1.left, right = s.right -- s1.right)
  }

  /**
   * Represents a converter of some object into a set.
   * @tparam S The type of elements in that set
   * @tparam T The type to convert from
   */
  protected trait SetConverter[S, T] {
    def apply(t: T): Set[S]
  }

  given [S]: SetConverter[S, Unit] with
    override def apply(u: Unit): Set[S] = Set.empty

  given [S]: SetConverter[S, EmptyTuple] with
    override def apply(t: EmptyTuple): Set[S] = Set.empty

  given [S, H <: S, T <: Tuple, C1](using SetConverter[S, T]): SetConverter[S, H *: T] with
    override def apply(t: H *: T): Set[S] = summon[SetConverter[S, T]].apply(t.tail) + t.head

  given [S, T <: S]: SetConverter[S, T] with
    override def apply(f: T): Set[S] = Set(f)

  given [S, I <: Iterable[S]]: SetConverter[S, I] with
    override def apply(s: I): Set[S] = s.toSet

  private def any2set[S, A, T <: A](any: T)(using SetConverter[S, T]): Set[S] = summon[SetConverter[S, T]].apply(any)

  extension [A, T1 <: A](left: T1)(using SetConverter[Formula, T1])
    infix def |-[B, T2 <: B](right: T2)(using SetConverter[Formula, T2]): Sequent = Sequent(any2set(left), any2set(right))

}
