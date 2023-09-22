package lisa.fol

import lisa.utils.K
import lisa.utils.UserLisaException

import scala.annotation.nowarn
import scala.annotation.showAsInfix
import scala.compiletime.ops.int.-
import scala.reflect.ClassTag
import scala.runtime.ScalaRunTime

import K.given_Conversion_Identifier_String

trait Common {

  ////////////////////////////////////////////////
  //////////////  Base Definitions  //////////////
  ////////////////////////////////////////////////

  export K.Identifier
  type Arity = Int & Singleton

  /**
   * Define the type of tuples of Arity N. If N=-1, T***N = List[T] (arbitrary arity).
   */
  @showAsInfix
  type ***[+T, N <: Arity] <: (Tuple | Seq[T]) & Matchable = N match {
    case -1 => Seq[T]
    case 0 => EmptyTuple
    case _ => T *: (T *** (N - 1))
  }

  /**
   * The union of the types of N-tuples and lists. Usually, filling a List for a T**N forfeits arity checking at compile time.
   */
  type **[+T, N <: Arity] = Seq[T] | ***[T, N]

  extension [T, N <: Arity](self: T ** N) {
    @nowarn("msg=checked at runtime")
    @nowarn("msg=match may not be exhaustive")
    def toSeq: Seq[T] = self match {
      case l: Seq[T] => l
      case tup: Tuple =>
        tup.productIterator.toSeq.asInstanceOf[Seq[T]]
    }
    @nowarn("msg=checked at runtime")
    @nowarn("msg=match may not be exhaustive")
    def map[U](f: T => U): U ** N = self match {
      case l: Seq[T] => l.map(f).asInstanceOf[(U ** (N))]
      case tup: Tuple => tup.map[[t] =>> U]([u] => (x: u) => f(x.asInstanceOf[T])).asInstanceOf
    }
    /*
    object ** {
      def unapply[T, N <: Arity](p: T**N): T***N = ValueOf[N] match {
        case n: -1 => Some(p)
        case n: 0  => if (p.size == 0) Some(EmptyTuple) else None
        case n: _  => if (p.size == n) p match {case Tuple => p; case Seq} else None
      }
    }
     */

  }

  trait WithArity[N <: Arity] {
    val arity: N
  }

  class BadArityException(msg: String)(using line: sourcecode.Line, file: sourcecode.File) extends UserLisaException(msg) {
    def showError: String = msg
  }

  def isLegalApplication(withArity: WithArity[?], args: Seq[?]): Boolean =
    withArity.arity == -1 || withArity.arity == args.size

  /**
   * A container for valid substitutions. For example, if X is a schematic variable and t a term, SubstPair(X, t) is valid.
   * If a is a formula, SubstPair(X, a) is not valid
   * If P is a schematic predicate of arity N, and L a Lambda of type Term**N |-> Formula, SubstPair(P, L) is valid.
   * Etc. SubstPair can be constructed with X := t.
   *
   * @param _1 The schematic label to substitute
   * @param _2 The value to replace it with
   */
  class SubstPair private (val _1: SchematicLabel[?], val _2: LisaObject[?]) {
    // def toTuple = (_1, _2)
  }
  object SubstPair {
    def apply[S <: LisaObject[S]](_1: SchematicLabel[S], _2: S) = new SubstPair(_1, _2)
  }

  given trsubst[S <: LisaObject[S]]: Conversion[(SchematicLabel[S], S), SubstPair] = s => SubstPair(s._1, s._2)

  /**
   * A LisaObject is the type for formulas, terms, lambdas. A child of LisaObject is supposed to be parametrized by itself.
   * It key property is to define substitution and computation of free scematic symbols.
   * The type T denotes the type that the object is guaranteed to keep after a substitution.
   * For example, Term <: LisaObject[Term], because a term with some substitution is still a term.
   * Similarly, Variable <: LisaObject[Term] because a variable is a term and still is after any substitution.
   * However, Variable <: LisaObject[Variable] does not hold because a variable after a substitution is not necessarily a variable anymore.
   */
  trait LisaObject[+T <: LisaObject[T]] {
    this: T =>

    def lift: T & this.type = this

    /**
     * Substitution in the LisaObject of schematics by values. It is not guaranteed by the type system that types of schematics and values match, and the substitution can fail if that is the case.
     * This is the substitution that should be implemented.
     */
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): T
    def substituteUnsafe2[A <: SchematicLabel[?], B <: LisaObject[B]](map: Map[A, B]): T = substituteUnsafe(map.asInstanceOf)

    /**
     * Substitution in the LisaObject of schematics by values, with guaranteed correspondance between the types of schematics and values.
     * This is the substitution that should be used when writing proofs.
     */
    def substitute(pairs: SubstPair*): T = {
      substituteUnsafe(Map(pairs.map(s => (s._1, (s._2: LisaObject[_])))*))
    }
    def substituteOne[S <: LisaObject[S]](v: SchematicLabel[S], arg: S): T = substituteUnsafe(Map(v -> arg))

    /**
     * Compute the free schematic symbols in the expression.
     */
    def freeSchematicLabels: Set[SchematicLabel[?]]
    def freeVariables: Set[Variable] = freeSchematicLabels.collect { case v: Variable => v }
    def freeVariableFormulas: Set[VariableFormula] = freeSchematicLabels.collect { case v: VariableFormula => v }

    /**
     * Compute the free and non-free schematic symbols in the expression.
     */
    def allSchematicLabels: Set[SchematicLabel[?]]
  }

  /**
   * Base types for LisaObjects: Terms and Formulas.
   */
  sealed trait TermOrFormula extends LisaObject[TermOrFormula] {}

  /**
   * Constructor types for LISA Objects: Functions into Terms and Formulas.
   */
  @showAsInfix
  infix trait |->[-I, +O <: LisaObject[O]] extends LisaObject[I |-> O] {
    def apply(arg: I): O

  }

  /**
   * A label is a [[LisaObject]] which is just a name. In general, constant symbols and schematic symbols.
   */
  trait Label[-A <: LisaObject[A]] {
    this: A & LisaObject[A] =>
    def liftLabel: LisaObject[?] = this
    def id: Identifier

    /**
     * Renames the symbol.
     */
    def rename(newid: Identifier): Label[A]

    /**
     * Renames the symbol with an identifier that is fresh for the given list.
     */
    def freshRename(taken: Iterable[Identifier]): Label[A]
  }

  /**
   * Schematic labels can be substituted by expressions (LisaObject) of the corresponding type
   */
  sealed trait SchematicLabel[-A <: LisaObject[A]] extends Label[A] {
    this: A & LisaObject[A] =>

    /**
     * The schematic label can be substituted by anything of an equivalent type. See [[SubstPair]], [[LisaObject]].
     */
    // type SubstitutionType <: A
    def rename(newid: Identifier): SchematicLabel[A]
    def freshRename(taken: Iterable[Identifier]): SchematicLabel[A]

    /**
     * Helper to build a [[SubstPair]]
     */
    def :=(replacement: A) = SubstPair(this, replacement)

  }

  /**
   * ConstantLabel represent constants in the theory and can't be freely substituted.
   */
  sealed trait ConstantLabel[-A <: LisaObject[A]] extends Label[A] with Matchable {
    this: A & LisaObject[A] =>
    def rename(newid: Identifier): ConstantLabel[A]
    def freshRename(taken: Iterable[Identifier]): ConstantLabel[A]
  }

  class TypeError extends Error

  /**
   * Can be thrown during an unsafe substitution when the type of a schematic symbol and its substituted value don't match.
   */
  class SubstitutionException extends Exception

  /**
   * Indicates LisaObjects corresponding directly to a Kernel member
   */
  trait Absolute

  ////////////////////////////////////
  //////////////  Term  //////////////
  ////////////////////////////////////

  /**
   * The type of terms, corresponding to [[K.Term]]. It can be either of a [[Variable]], a [[Constant]]
   * a [[ConstantFunctionLabel]] or a [[SchematicFunctionLabel]].
   */
  sealed trait Term extends TermOrFormula with LisaObject[Term] with (Term ** 0 |-> Term) {
    def apply(args: Term ** 0): Term = this
    val underlying: K.Term
    val label: TermLabel
    val args: Seq[Term]
    def toStringSeparated(): String = toString()
  }

  /**
   * A TermLabel is a [[LisaObject]] of type ((Term ** N) |-> Term), that is represented by a functional label.
   * It can be either a [[SchematicFunctionLabel]] or a [[ConstantFunctionLabel]]. It corresponds to [[K.TermLabel]]
   */
  sealed trait TermLabel extends (Seq[Term] |-> Term) with Absolute {
    val arity: Arity
    def id: Identifier
    val underlyingLabel: K.TermLabel
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): (Seq[Term] |-> Term)
    def rename(newid: Identifier): TermLabel
    def freshRename(taken: Iterable[Identifier]): TermLabel
    def mkString(args: Seq[Term]): String
    def mkStringSeparated(args: Seq[Term]): String = mkString(args)
    // def unapply(t:Term):Option[Seq[Term]]
  }

  /**
   * A constant [[TermLabel]], which can be either a [[Constant]] symbol or a [[ConstantFunctionSymbol]]. Corresponds to a [[K.ConstantFunctionLabel]]
   */
  sealed trait ConstantTermLabel extends TermLabel with ConstantLabel[Seq[Term] |-> Term] {
    val underlyingLabel: K.ConstantFunctionLabel
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): ConstantTermLabel
    override def rename(newid: Identifier): ConstantTermLabel
    def freshRename(taken: Iterable[Identifier]): ConstantTermLabel
  }
  object ConstantTermLabel {

    /**
     * Construct a ConstantTermLabel according to arity:
     * A [[Constant]] for arity 0, a [[ConstantFunctionLabel]] otherwise.
     * @param id The identifier of the new symbol
     * @param arity The arity of the new symbol
     * @return The new symbol
     */
    def apply[N <: Arity](id: Identifier, arity: N): ConstantFunctionLabelOfArity[N] = arity match {
      case a: 0 => Constant(id)
      case n: N => ConstantFunctionLabel[N](id, arity)
    }
  }

  /**
   * Types of constant term labels: [[Constant]] for if N = 0, [[ConstantFunctionLabel]] otherwise.
   */
  type ConstantFunctionLabelOfArity[N <: Arity] <: ConstantTermLabel = N match
    case 0 => Constant
    case N => ConstantFunctionLabel[N]
  object ConstantFunctionLabelOfArity {

    /**
     * Construct a ConstantTermLabel according to arity:
     * A [[Constant]] for arity 0, a [[ConstantFunctionLabel]] otherwise.
     * @param id The identifier of the new symbol
     * @param arity The arity of the new symbol
     * @return The new symbol
     */
    def apply[N <: Arity](id: Identifier, arity: N): ConstantFunctionLabelOfArity[N] = ConstantTermLabel[N](id, arity)
  }

  /**
   * A schematic [[TermLabel]], which can be either a [[Variable]] symbol or a [[SchematicFunctionSymbol]]. Corresponds to a [[K.SchematicFunctionLabel]]
   */
  sealed trait SchematicTermLabel extends TermLabel with SchematicLabel[Seq[Term] |-> Term] {
    val underlyingLabel: K.SchematicTermLabel
    override def rename(newid: Identifier): SchematicTermLabel
    def freshRename(taken: Iterable[Identifier]): SchematicTermLabel
    def mkString(args: Seq[Term]): String
  }
  object SchematicTermLabel { // Companion
    /**
     * Construct a SchematicTermLabel according to arity:
     * A [[Variable]] for arity 0, a [[SchematicFunctionLabel]] otherwise.
     * @param id The identifier of the new symbol
     * @param arity The arity of the new symbol
     * @return The new symbol
     */
    def apply[N <: Arity](id: Identifier, arity: N): SchematicFunctionLabelOfArity[N] = arity match {
      case a: 0 => new Variable(id)
      case n: N => new SchematicFunctionLabel[N](id, arity)
    }
  }
  type SchematicFunctionLabelOfArity[N <: Arity] <: SchematicTermLabel = N match
    case 0 => Variable
    case N => SchematicFunctionLabel[N]
  object SchematicFunctionLabelOfArity { // Companion
    /**
     * Construct a SchematicTermLabel according to arity:
     * A [[Variable]] for arity 0, a [[SchematicFunctionLabel]] otherwise.
     * @param id The identifier of the new symbol
     * @param arity The arity of the new symbol
     * @return The new symbol
     */
    def apply[N <: Arity](id: Identifier, arity: N): SchematicFunctionLabelOfArity[N] = SchematicTermLabel[N](id, arity)
  }

  /**
   * A Variable, corresponding to [[K.VariableLabel]], is a schematic symbol for terms.
   * It counts both as the label and as the term itself.
   */
  case class Variable(id: Identifier) extends SchematicTermLabel with Term with Absolute with SchematicLabel[Term] {
    val arity: 0 = 0
    val label: Variable = this
    val args: Seq[Nothing] = Seq.empty
    override val underlyingLabel: K.VariableLabel = K.VariableLabel(id)
    override val underlying = K.VariableTerm(underlyingLabel)
    override def apply(args: Term ** 0) = this
    def unapply(t: Variable): Option[Seq[Term]] = if (t == this) Some(Seq()) else None
    @nowarn("msg=Unreachable")
    override def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): Term = {
      map.get(this.asInstanceOf) match {
        case Some(subst) =>
          subst match {
            case s: Term => s
            case _ => throw SubstitutionException()
          }
        case None => this
      }
    }
    def freeSchematicLabels: Set[SchematicLabel[?]] = Set(this)
    def allSchematicLabels: Set[SchematicLabel[?]] = Set(this)
    override def rename(newid: Identifier): Variable = Variable(newid)
    def freshRename(taken: Iterable[Identifier]): Variable = rename(K.freshId(taken, id))
    override def toString(): String = id
    def mkString(args: Seq[Term]): String = if (args.size == 0) toString() else toString() + "(" + "illegal_arguments: " + args.mkString(", ") + ")"
  }

  /**
   * A Constant, corresponding to [[K.ConstantLabel]], is a label for terms.
   * It counts both as the label and as the term itself.
   */
  case class Constant(id: Identifier) extends ConstantTermLabel with Term with Absolute with ConstantLabel[Constant] with LisaObject[Constant] {
    val arity: 0 = 0
    val label: Constant = this
    val args: Seq[Nothing] = Seq.empty
    override val underlyingLabel: K.ConstantFunctionLabel = K.ConstantFunctionLabel(id, 0)
    override val underlying = K.Term(underlyingLabel, Seq())
    override def apply(args: Term ** 0) = this
    def unapply(t: Constant): Option[Term ** 0] = if (t == this) Some(Seq()) else None
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): Constant = this
    override def rename(newid: Identifier): Constant = Constant(newid)
    def freshRename(taken: Iterable[Identifier]): Constant = rename(K.freshId(taken, id))
    def freeSchematicLabels: Set[SchematicLabel[?]] = Set.empty
    def allSchematicLabels: Set[SchematicLabel[?]] = Set.empty
    override def toString(): String = id
    def mkString(args: Seq[Term]): String = if (args.size == 0) toString() else toString() + "(" + "illegal_arguments: " + args.mkString(", ") + ")"
  }

  /**
   * A schematic functional label (corresponding to [[K.SchematicFunctionLabel]]) is a functional label and also a schematic label.
   * It can be substituted by any expression of type (Term ** N) |-> Term
   */
  case class SchematicFunctionLabel[N <: Arity](val id: Identifier, val arity: N) extends SchematicTermLabel with SchematicLabel[(Term ** N) |-> Term] with ((Term ** N) |-> Term) {
    val underlyingLabel: K.SchematicTermLabel = K.SchematicFunctionLabel(id, arity)
    def apply(args: (Term ** N)): Term = AppliedTerm(this, args.toSeq)
    def unapply(t: AppliedTerm): Option[Term ** N] = t match { case AppliedTerm(label, args) if (label == this) => Some(args); case _ => None }
    @nowarn
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): ((Term ** N) |-> Term) = {
      map.get(this.asInstanceOf) match {
        case Some(subst) =>
          subst match {
            case s: ((Term ** N) |-> Term) => s
            case _ => throw SubstitutionException()
          }
        case None => this
      }
    }
    def freeSchematicLabels: Set[SchematicLabel[?]] = Set(this)
    def allSchematicLabels: Set[SchematicLabel[?]] = Set(this)
    def rename(newid: Identifier): SchematicFunctionLabel[N] = SchematicFunctionLabel(newid, arity)
    def freshRename(taken: Iterable[Identifier]): SchematicFunctionLabel[N] = rename(K.freshId(taken, id))
    override def toString(): String = id
    def mkString(args: Seq[Term]): String = toString() + "(" + args.mkString(", ") + ")"
    override def mkStringSeparated(args: Seq[Term]): String = mkString(args)
  }

  /**
   * A constant functional label of arity N.
   */
  case class ConstantFunctionLabel[N <: Arity](id: Identifier, arity: N) extends ConstantTermLabel with ConstantLabel[((Term ** N) |-> Term)] with ((Term ** N) |-> Term) {
    val underlyingLabel: K.ConstantFunctionLabel = K.ConstantFunctionLabel(id, arity)
    var infix: Boolean = false
    def apply(args: (Term ** N)): Term = AppliedTerm(this, args.toSeq)
    def unapply(t: AppliedTerm): Option[Term ** N] = t match { case AppliedTerm(label, args) if (label == this) => Some(args); case _ => None }
    inline def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): this.type =
      this
    def rename(newid: Identifier): ConstantFunctionLabel[N] = ConstantFunctionLabel(newid, arity)
    def freshRename(taken: Iterable[Identifier]): ConstantFunctionLabel[N] = rename(K.freshId(taken, id))
    def freeSchematicLabels: Set[SchematicLabel[?]] = Set.empty
    def allSchematicLabels: Set[SchematicLabel[?]] = Set.empty
    override def toString(): String = id
    def mkString(args: Seq[Term]): String = if (infix) (args(0).toString() + " " + toString() + " " + args(1).toString()) else toString() + "(" + args.mkString(", ") + ")"
    override def mkStringSeparated(args: Seq[Term]): String = if (infix) "(" + mkString(args) + ")" else mkString(args)
  }
  object ConstantFunctionLabel {
    def infix[N <: Arity](id: Identifier, arity: N): ConstantFunctionLabel[N] =
      val x = ConstantFunctionLabel[N](id, arity)
      x.infix = true
      x
  }

  /**
   * A term made from a functional label of arity N and N arguments
   */
  case class AppliedTerm(f: TermLabel, args: Seq[Term]) extends Term with Absolute {
    val label: TermLabel = f
    assert(f.arity != 0)
    override val underlying = K.Term(f.underlyingLabel, args.map(_.underlying))
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): Term = {
      f.substituteUnsafe(map)(
        args.map[Term]((x: Term) => x.substituteUnsafe(map))
      )
    }
    def freeSchematicLabels: Set[SchematicLabel[?]] = f.freeSchematicLabels ++ args.flatMap(_.freeSchematicLabels)
    def allSchematicLabels: Set[SchematicLabel[?]] = f.allSchematicLabels ++ args.flatMap(_.allSchematicLabels)
    override def toString: String = f.mkString(args)
    override def toStringSeparated(): String = f.mkString(args)
  }

  //////////////////////////////////////
  ////////////// Formulas //////////////
  //////////////////////////////////////

  /**
   * The type of formulas, corresponding to [[K.Formula]]
   */
  sealed trait Formula extends TermOrFormula with LisaObject[Formula] with ((Term ** 0) |-> Formula) {
    val arity: Arity = 0
    // val label:PredicateLabel|ConnectorLabel
    // val args:Seq[Term]|Seq[Formula]
    def apply(args: Term ** 0): Formula = this
    val underlying: K.Formula
    def toStringSeparated() = toString()
  }

  /////////////////////
  // Atomic Formulas //
  /////////////////////

  sealed trait AtomicFormula extends Formula {
    val label: PredicateLabel
    val args: Seq[Term]
  }

  /**
   * A PredicateLabel is a [[LisaObject]] of type ((Term ** N) |-> Formula), that is represented by a predicate label.
   * It can be either a [[SchematicPredicateLabel]] or a [[ConstantPredicateLabel]].
   */
  sealed trait PredicateLabel extends (Seq[Term] |-> Formula) with Absolute {
    val arity: Arity
    def id: Identifier
    val underlyingLabel: K.PredicateLabel
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): (Seq[Term] |-> Formula)
    def rename(newid: Identifier): PredicateLabel
    def freshRename(taken: Iterable[Identifier]): PredicateLabel
    def mkString(args: Seq[Term]): String
    def mkStringSeparated(args: Seq[Term]): String = mkString(args)
  }

  sealed trait ConstantConstOrPredLabel extends PredicateLabel with ConstantLabel[Seq[Term] |-> Formula] {
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): ConstantConstOrPredLabel
    override def rename(newid: Identifier): ConstantConstOrPredLabel
    def freshRename(taken: Iterable[Identifier]): ConstantConstOrPredLabel
  }
  type ConstantPredicateLabelOfArity[N <: Arity] <: ConstantConstOrPredLabel = N match {
    case 0 => ConstantFormula
    case N => ConstantPredicateLabel[N]
  }

  sealed trait SchematicVarOrPredLabel extends PredicateLabel with SchematicLabel[Seq[Term] |-> Formula] {
    override def rename(newid: Identifier): SchematicVarOrPredLabel
    def freshRename(taken: Iterable[Identifier]): SchematicVarOrPredLabel
  }
  type SchematicPredicateLabelOfArity[N <: Arity] <: SchematicVarOrPredLabel = N match {
    case 0 => VariableFormula
    case N => SchematicPredicateLabel[N]
  }

  /**
   * A Variable for formulas, corresponding to [[K.VariableFormulaLabel]], is a schematic symbol for formulas.
   * It counts both as the label and as the term itself.
   */
  case class VariableFormula(id: Identifier) extends SchematicVarOrPredLabel with AtomicFormula with Absolute with SchematicLabel[Formula] {
    override val arity: 0 = 0
    val label: VariableFormula = this
    val args: Seq[Nothing] = Seq()
    val underlyingLabel: K.VariableFormulaLabel = K.VariableFormulaLabel(id)
    val underlying = K.PredicateFormula(underlyingLabel, Seq())
    override def apply(args: Term ** 0): Formula = this
    def unapply(t: VariableFormula): Option[Term ** 0] = if (t == this) Some(EmptyTuple) else None
    @nowarn("msg=Unreachable")
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): Formula = {
      map.get(this.asInstanceOf) match {
        case Some(subst) =>
          subst match {
            case s: Formula => s
          }
        case None => this
      }
    }
    def freeSchematicLabels: Set[SchematicLabel[?]] = Set(this)
    def allSchematicLabels: Set[SchematicLabel[?]] = Set(this)
    def rename(newid: Identifier): VariableFormula = VariableFormula(newid)
    def freshRename(taken: Iterable[Identifier]): VariableFormula = rename(K.freshId(taken, id))
    override def toString(): String = id
    def mkString(args: Seq[Term]): String = if (args.size == 0) toString() else toString() + "(" + "illegal_arguments: " + args.mkString(", ") + ")"
  }

  /**
   * A Constant formula, corresponding to [[K.ConstantFormulaLabel]].
   * It counts both as the label and as the formula itself. Usually either True or False.
   */
  case class ConstantFormula(id: Identifier) extends ConstantConstOrPredLabel with AtomicFormula with Absolute with ConstantLabel[Formula] {
    override val arity: 0 = 0
    val label: ConstantFormula = this
    val args: Seq[Nothing] = Seq()
    val underlyingLabel: K.ConstantPredicateLabel = K.ConstantPredicateLabel(id, 0)
    val underlying = K.PredicateFormula(underlyingLabel, Seq())
    override def apply(args: Term ** 0): Formula = this
    def unapply(t: ConstantFormula): Option[Term ** 0] = if (t == this) Some(EmptyTuple) else None
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): this.type = this
    def freeSchematicLabels: Set[SchematicLabel[?]] = Set.empty
    def allSchematicLabels: Set[SchematicLabel[?]] = Set.empty
    def rename(newid: Identifier): ConstantFormula = ConstantFormula(newid)
    def freshRename(taken: Iterable[Identifier]): ConstantFormula = rename(K.freshId(taken, id))
    override def toString(): String = id
    def mkString(args: Seq[Term]): String = if (args.size == 0) toString() else toString() + "(" + "illegal_arguments: " + args.mkString(", ") + ")"
  }

  /**
   * A schematic predicate label (corresponding to [[K.SchematicPredicateLabel]]) is a [[PredicateLabel]] and also a [[SchematicLabel]].
   * It can be substituted by any expression of type (Term ** N) |-> Formula
   */
  case class SchematicPredicateLabel[N <: Arity](id: Identifier, arity: N) extends SchematicVarOrPredLabel with SchematicLabel[(Term ** N) |-> Formula] with ((Term ** N) |-> Formula) {
    val underlyingLabel: K.SchematicPredicateLabel = K.SchematicPredicateLabel(id, arity)
    def apply(args: (Term ** N)): Formula = PredicateFormula(this, args.toSeq)
    def unapply(t: PredicateFormula): Option[Term ** N] = t match { case PredicateFormula(label, args) if (label == this) => Some(args); case _ => None }
    @nowarn
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): |->[Term ** N, Formula] = {
      map.get(this.asInstanceOf) match {
        case Some(subst) =>
          subst match {
            case s: |->[Term ** N, Formula] => s
          }
        case None => this
      }
    }
    def freeSchematicLabels: Set[SchematicLabel[?]] = Set(this)
    def allSchematicLabels: Set[SchematicLabel[?]] = Set(this)
    def rename(newid: Identifier): SchematicPredicateLabel[N] = SchematicPredicateLabel(newid, arity)
    def freshRename(taken: Iterable[Identifier]): SchematicPredicateLabel[N] = rename(K.freshId(taken, id))
    override def toString(): String = id
    def mkString(args: Seq[Term]): String = toString() + "(" + args.mkString(", ") + ")"
    override def mkStringSeparated(args: Seq[Term]): String = mkString(args)

  }

  /**
   * A constant predicate label corresponding to [[K.ConstantPredicateLabel]].
   */
  case class ConstantPredicateLabel[N <: Arity](id: Identifier, arity: N) extends ConstantConstOrPredLabel with ConstantLabel[Term ** N |-> Formula] with ((Term ** N) |-> Formula) {
    val underlyingLabel: K.ConstantPredicateLabel = K.ConstantPredicateLabel(id, arity)
    private var infix = false
    def apply(args: (Term ** N)): Formula = PredicateFormula(this, args.toSeq)
    def unapply(t: PredicateFormula): Option[Term ** N] = t match { case PredicateFormula(label, args) if (label == this) => Some(args); case _ => None }
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): this.type = this
    def freeSchematicLabels: Set[SchematicLabel[?]] = Set.empty
    def allSchematicLabels: Set[SchematicLabel[?]] = Set.empty
    def rename(newid: Identifier): ConstantPredicateLabel[N] = ConstantPredicateLabel(newid, arity)
    def freshRename(taken: Iterable[Identifier]): ConstantPredicateLabel[N] = rename(K.freshId(taken, id))
    override def toString(): String = id
    def mkString(args: Seq[Term]): String = if (infix) (args(0).toString() + " " + toString() + " " + args(1).toString()) else toString() + "(" + args.mkString(", ") + ")"
    override def mkStringSeparated(args: Seq[Term]): String = if (infix) "(" + mkString(args) + ")" else mkString(args)
  }
  object ConstantPredicateLabel {
    def infix[N <: Arity](id: Identifier, arity: N): ConstantPredicateLabel[N] =
      val x = new ConstantPredicateLabel[N](id, arity)
      x.infix = true
      x
  }

  /**
   * A formula made from a predicate label of arity N and N arguments
   */
  case class PredicateFormula(p: PredicateLabel, args: Seq[Term]) extends AtomicFormula with Absolute {
    assert(p.arity != 0)
    val label: PredicateLabel = p
    override val underlying = K.PredicateFormula(p.underlyingLabel, args.map(_.underlying))
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): Formula =
      p.substituteUnsafe(map)(args.map[Term]((x: Term) => x.substituteUnsafe(map)))

    def freeSchematicLabels: Set[SchematicLabel[?]] = p.freeSchematicLabels ++ args.toSeq.flatMap(_.freeSchematicLabels)
    def allSchematicLabels: Set[SchematicLabel[?]] = p.allSchematicLabels ++ args.toSeq.flatMap(_.allSchematicLabels)

    override def toString: String = p.mkString(args)
    override def toStringSeparated(): String = p.mkString(args)
  }

  ////////////////
  // Connectors //
  ////////////////

  /**
   * A ConnectorLabel is a [[LisaObject]] of type ((Formula ** N) |-> Formula), that is represented by a connector label in the kernel.
   * It can be either a [[SchematicConnectorLabel]] or a [[ConstantConnectorLabel]].
   */
  sealed trait ConnectorLabel extends (Seq[Formula] |-> Formula) with Absolute {
    val arity: Arity
    def id: Identifier
    val underlyingLabel: K.ConnectorLabel
    def rename(newid: Identifier): ConnectorLabel
    def freshRename(taken: Iterable[Identifier]): ConnectorLabel
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): |->[Seq[Formula], Formula]
    def mkString(args: Seq[Formula]): String
    def mkStringSeparated(args: Seq[Formula]): String = mkString(args)

  }

  /**
   * A schematic predicate label (corresponding to [[K.SchematicPredicateLabel]]) is a [[ConnectorLabel]] and also a [[SchematicLabel]].
   * It can be substituted by any expression of type (Formula ** N) |-> Formula
   */
  case class SchematicConnectorLabel[N <: Arity](id: Identifier, arity: N) extends ConnectorLabel with SchematicLabel[Formula ** N |-> Formula] with ((Formula ** N) |-> Formula) {
    val underlyingLabel: K.SchematicConnectorLabel = K.SchematicConnectorLabel(id, arity)
    @nowarn
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): |->[Formula ** N, Formula] = {
      map.get(this.asInstanceOf) match {
        case Some(subst) =>
          subst match {
            case s: |->[Formula ** N, Formula] => s
          }
        case None => this
      }
    }
    // def apply(args: Seq[Formula]): Formula = apply(args)
    def apply(args: Formula ** N): Formula = ConnectorFormula(this, args.toSeq)
    def unapply(t: ConnectorFormula): Option[Seq[Formula]] = t match { case ConnectorFormula(label, args) if (label == this) => Some(args); case _ => None }
    def freeSchematicLabels: Set[SchematicLabel[?]] = Set(this)
    def allSchematicLabels: Set[SchematicLabel[?]] = Set(this)
    def rename(newid: Identifier): SchematicConnectorLabel[N] = SchematicConnectorLabel(newid, arity)
    def freshRename(taken: Iterable[Identifier]): SchematicConnectorLabel[N] = rename(K.freshId(taken, id))
    override def toString(): String = id
    def mkString(args: Seq[Formula]): String = toString() + "(" + args.mkString(", ") + ")"

  }

  /**
   * A constant connector label is a logical operator such as /\, \/, !, ==>, <=>.
   * It corresponds to a [[K.ConstantConnectorLabel]].
   */
  trait ConstantConnectorLabel[N <: Arity] extends ConnectorLabel with ConstantLabel[Formula ** N |-> Formula] with ((Formula ** N) |-> Formula) {
    val underlyingLabel: K.ConstantConnectorLabel
    def id: Identifier = underlyingLabel.id
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): this.type = this
    def apply(args: Formula ** N): Formula = ConnectorFormula(this, args.toSeq)
    def unapply(t: ConnectorFormula): Option[Seq[Formula]] = t match { case ConnectorFormula(label, args) if (label == this) => Some(args); case _ => None }
    def freeSchematicLabels: Set[SchematicLabel[?]] = Set.empty
    def allSchematicLabels: Set[SchematicLabel[?]] = Set.empty
    def rename(newid: Identifier): ConstantConnectorLabel[N] = throw new Error("Can't rename a constant connector label")
    def freshRename(taken: Iterable[Identifier]): ConstantConnectorLabel[N] = rename(K.freshId(taken, id))
    override def toString(): String = id
    def mkString(args: Seq[Formula]): String = if (args.length == 2) ("(" + args(0).toString() + " " + toString() + " " + args(1).toString()) + ")" else toString() + "(" + args.mkString(", ") + ")"
    override def mkStringSeparated(args: Seq[Formula]): String = if (args.length == 2) "(" + mkString(args) + ")" else mkString(args)

  }

  /**
   * A formula made from a connector label of arity N and N arguments
   */
  case class ConnectorFormula(p: ConnectorLabel, args: Seq[Formula]) extends Formula with Absolute {
    // assert(args.length == p.arity)
    val label: ConnectorLabel = p
    override val underlying = K.ConnectorFormula(p.underlyingLabel, args.map(_.underlying))
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): Formula = {
      val p2 = p.substituteUnsafe(map)
      p2 match {
        case p2: ConnectorLabel => ConnectorFormula(p2, args.map[Formula]((x: Formula) => x.substituteUnsafe(map)))
        case _ => p2(args.map[Formula]((x: Formula) => x.substituteUnsafe(map)))
      }
    }

    def freeSchematicLabels: Set[SchematicLabel[?]] = p.freeSchematicLabels ++ args.flatMap(_.freeSchematicLabels)
    def allSchematicLabels: Set[SchematicLabel[?]] = p.allSchematicLabels ++ args.flatMap(_.allSchematicLabels)
    // override def substituteUnsafe(v: Variable, subs: Term) = PredicateFormulaFormula[N](f, args.map(_.substituteUnsafe(v, subs)))

    override def toString: String = p.mkString(args)
    override def toStringSeparated(): String = p.mkString(args)
  }

  /////////////
  // Binders //
  /////////////

  /**
   * A binder for variables, for example \exists, \forall and \exists! but possibly others.
   */
  trait BinderLabel extends |->[(Variable, Formula), Formula] with Absolute {
    def id: Identifier
  }

  /**
   * A binder label that exactly correspond to a kernel binder, i.e. \exists, \forall and \exists!
   */
  trait BaseBinderLabel extends BinderLabel with Absolute {
    val underlyingLabel: K.BinderLabel

    def apply(arg: (Variable, Formula)): BinderFormula = BinderFormula(this, arg._1, arg._2)
    inline def freeSchematicLabels: Set[SchematicLabel[?]] = Set.empty
    inline def allSchematicLabels: Set[SchematicLabel[?]] = Set.empty
    inline def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): this.type = this
    override def toString() = id

  }

  /**
   * A quantified formula made of a [[BaseBinderLabel]] and an underlying formula, in a namefull representation.
   */
  case class BinderFormula(f: BaseBinderLabel, bound: Variable, body: Formula) extends Formula with Absolute {
    override val underlying = K.BinderFormula(f.underlyingLabel, bound.underlyingLabel, body.underlying)

    def allSchematicLabels: Set[Common.this.SchematicLabel[?]] = body.allSchematicLabels + bound
    def freeSchematicLabels: Set[Common.this.SchematicLabel[?]] = body.freeSchematicLabels - bound
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): Formula = {
      val newSubst = map - bound.asInstanceOf
      if (map.values.flatMap(_.freeSchematicLabels).toSet.contains(bound)) {
        val taken: Set[SchematicLabel[?]] = body.allSchematicLabels ++ map.keys
        val newBound: Variable = bound.rename(lisa.utils.KernelHelpers.freshId(taken.map(_.id), bound.id))
        val newBody = body.substituteOne(bound, newBound.lift)
        BinderFormula(f, newBound, newBody.substituteUnsafe(newSubst))
      } else {
        BinderFormula(f, bound, body.substituteUnsafe(newSubst))
      }
    }
    // override def toString():String = f.toString()+bound.toString()+". "+body.toString()
    override def toString(): String = f.toString() + "(" + bound.toString() + ", " + body.toString() + ")"

  }
  def instantiateBinder(f: BinderFormula, t: Term): Formula = f.body.substituteUnsafe(Map(f.bound -> t))

}
