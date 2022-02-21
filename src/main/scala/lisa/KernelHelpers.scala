package lisa

object KernelHelpers {

  import lisa.kernel.proof.SequentCalculus.Sequent
  import lisa.kernel.fol.FOL.*

  // Prefix
  def neg(f: Formula): Formula = ConnectorFormula(Neg, Seq(f))
  def and(l: Formula, r: Formula): Formula = ConnectorFormula(And, Seq(l, r))
  def or(l: Formula, r: Formula): Formula = ConnectorFormula(Or, Seq(l, r))
  def implies(l: Formula, r: Formula): Formula = ConnectorFormula(Implies, Seq(l, r))
  def iff(l: Formula, r: Formula): Formula = ConnectorFormula(Iff, Seq(l, r))
  def forall(label: VariableLabel, body: Formula): Formula = BinderFormula(Forall, label, body)
  def exists(label: VariableLabel, body: Formula): Formula = BinderFormula(Exists, label, body)
  def existsOne(label: VariableLabel, body: Formula): Formula = BinderFormula(ExistsOne, label, body)
  def equ(l: Term, r: Term): Formula = PredicateFormula(equality, Seq(l, r))

  extension (label: PredicateLabel) def apply(args: Term*): Formula = PredicateFormula(label, args)

  extension (label: ConnectorLabel) def apply(args: Formula*): Formula = ConnectorFormula(label, args)

  extension (label: FunctionLabel) def apply(args: Term*): Term = FunctionTerm(label, args)

  extension (label: BinderLabel) def apply(bound: VariableLabel, inner: Formula): Formula = BinderFormula(label, bound, inner)

  // Infix
  extension (f: Formula) {
    def unary_! : Formula = neg(f)
    infix def ==>(g: Formula): Formula = implies(f, g)
    infix def <=>(g: Formula): Formula = iff(f, g)
    infix def /\(g: Formula): Formula = and(f, g)
    infix def \/(g: Formula): Formula = or(f, g)
  }

  extension (t: Term) infix def ===(u: Term): Formula = PredicateFormula(equality, Seq(t, u))

  // Other
  given Conversion[VariableLabel, VariableTerm] = VariableTerm.apply
  given Conversion[VariableTerm, VariableLabel] = _.label

  val emptySeq = Sequent(Set.empty, Set.empty)

  extension (l: Unit)
    infix def |-(r: Iterable[Formula]): Sequent = Sequent(Set.empty, r.toSet)
    infix def |-(r: Formula): Sequent = Sequent(Set.empty, Set(r))
    infix def |-(r: Unit): Sequent = emptySeq
  extension (l: Iterable[Formula])
    infix def |-(r: Iterable[Formula]): Sequent = Sequent(l.toSet, r.toSet)
    infix def |-(r: Formula): Sequent = Sequent(l.toSet, Set(r))
    infix def |-(r: Unit): Sequent = Sequent(l.toSet, Set.empty)
  extension (l: Formula)
    infix def |-(r: Iterable[Formula]): Sequent = Sequent(Set(l), r.toSet)
    infix def |-(r: Formula): Sequent = Sequent(Set(l), Set(r))
    infix def |-(r: Unit): Sequent = Sequent(Set(l), Set.empty)

  // given Conversion[Tuple, List[Union[_.type]]] = _.toList

  given Conversion[(Boolean, List[Int], String), Option[(List[Int], String)]] = tr => if (tr._1) None else Some(tr._2, tr._3)

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
}
