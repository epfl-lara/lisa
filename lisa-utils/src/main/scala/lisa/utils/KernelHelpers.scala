package lisa.utils

import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.RunningTheoryJudgement
import lisa.kernel.proof.RunningTheoryJudgement.InvalidJustification
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SCProofCheckerJudgement.SCInvalidProof
import lisa.kernel.proof.SequentCalculus.*

/**
 * A helper file that provides various syntactic sugars for LISA's FOL and proofs. Best imported through utilities.Helpers
 * Usage:
 * <pre>
 * import utilities.Helpers.*
 * </pre>
 * or
 * <pre>
 * extends utilities.KernelHelpers.*
 * </pre>
 */
trait KernelHelpers {

  import lisa.kernel.fol.FOL.*
  import lisa.kernel.proof.SequentCalculus.Sequent

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

  extension (label: PredicateLabel) def apply(args: Term*): Formula = PredicateFormula(label, args)

  extension (label: ConnectorLabel) def apply(args: Formula*): Formula = ConnectorFormula(label, args)

  extension (label: TermLabel) def apply(args: Term*): Term = Term(label, args)

  extension (label: BinderLabel) def apply(bound: VariableLabel, inner: Formula): Formula = BinderFormula(label, bound, inner)

  /* Infix syntax */

  extension (f: Formula) {
    def unary_! : Formula = neg(f)
    infix def ==>(g: Formula): Formula = implies(f, g)
    infix def <=>(g: Formula): Formula = iff(f, g)
    infix def /\(g: Formula): Formula = and(f, g)
    infix def \/(g: Formula): Formula = or(f, g)
  }

  extension (t: Term) infix def ===(u: Term): Formula = PredicateFormula(equality, Seq(t, u))

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

  given Conversion[VariableLabel, Term] = Term(_, Seq())
  given Conversion[Term, TermLabel] = _.label

  given Conversion[PredicateFormula, PredicateLabel] = _.label
  given Conversion[PredicateLabel, Formula] = _.apply()
  given Conversion[VariableFormulaLabel, PredicateFormula] = PredicateFormula(_, Nil)
  given Conversion[(Boolean, List[Int], String), Option[(List[Int], String)]] = tr => if (tr._1) None else Some(tr._2, tr._3)
  given Conversion[Formula, Sequent] = () |- _

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

  given [S]: SetConverter[S, Unit] with {
    override def apply(u: Unit): Set[S] = Set.empty
  }

  given [S]: SetConverter[S, EmptyTuple] with {
    override def apply(t: EmptyTuple): Set[S] = Set.empty
  }

  given [S, H <: S, T <: Tuple](using SetConverter[S, T]): SetConverter[S, H *: T] with {
    override def apply(t: H *: T): Set[S] = summon[SetConverter[S, T]].apply(t.tail) + t.head
  }

  given [S, T <: S]: SetConverter[S, T] with {
    override def apply(f: T): Set[S] = Set(f)
  }

  given [S, I <: Iterable[S]]: SetConverter[S, I] with {
    override def apply(s: I): Set[S] = s.toSet
  }

  private def any2set[S, A, T <: A](any: T)(using SetConverter[S, T]): Set[S] = summon[SetConverter[S, T]].apply(any)

  extension [A, T1 <: A](left: T1)(using SetConverter[Formula, T1]) infix def |-[B, T2 <: B](right: T2)(using SetConverter[Formula, T2]): Sequent = Sequent(any2set(left), any2set(right))

  def instantiatePredicateSchemaInSequent(s: Sequent, m: Map[SchematicVarOrPredLabel, LambdaTermFormula]): Sequent = {
    s.left.map(phi => instantiatePredicateSchemas(phi, m)) |- s.right.map(phi => instantiatePredicateSchemas(phi, m))
  }
  def instantiateFunctionSchemaInSequent(s: Sequent, m: Map[SchematicTermLabel, LambdaTermTerm]): Sequent = {
    s.left.map(phi => instantiateTermSchemas(phi, m)) |- s.right.map(phi => instantiateTermSchemas(phi, m))
  }

  extension (sp: SCSubproof) {
    def followPath(path: Seq[Int]): SCProofStep = path match {
      case Nil => sp
      case n :: Nil => sp.sp(n)
      case n :: ns =>
        assert(sp.sp.steps(n).isInstanceOf[SCSubproof], s"Got $path but next step is not a subproof: ${sp.sp.steps(n).getClass}")
        sp.sp.steps(n).asInstanceOf[SCSubproof].followPath(ns)
    }
  }

  extension (p: SCProof) {
    def followPath(path: Seq[Int]): SCProofStep = SCSubproof(p, p.imports.indices).followPath(path)
  }

  extension (judgement: SCInvalidProof) {
    def errorMsg: String =
      s"""Failed to prove
         |${lisa.utils.Printer.prettySequent(judgement.proof.followPath(judgement.path).bot)}
         |(step ${judgement.path.mkString("->")}): ${judgement.message}""".stripMargin
  }

}
