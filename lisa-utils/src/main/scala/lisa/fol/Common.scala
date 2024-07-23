package lisa.fol

import lisa.utils.K
import lisa.utils.UserLisaException

import scala.annotation.nowarn
import scala.annotation.showAsInfix
import scala.annotation.targetName
import scala.compiletime.ops.int.-

import K.given_Conversion_Identifier_String

trait Common {

  ////////////////////////////////////////////////
  //////////////  Base Definitions  //////////////
  ////////////////////////////////////////////////

  export K.Identifier
  type Arity = Int & Singleton

  /**
   * Type of sequences of length N
   */
  opaque type **[+T, N <: Arity] >: Seq[T] = Seq[T]
  object ** {
    def apply[T, N <: Arity](args: T*): T ** N = args.toSeq
    def unapplySeq[T, N <: Arity](arg: T ** N): Option[Seq[T]] = Some(arg)
  }

  extension [T, N <: Arity](self: T ** N) {
    def toSeq: Seq[T] = self

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
     * Substitution in the LisaObject of schematics symbols by values. It is not guaranteed by the type system that types of schematics and values match, and the substitution can fail if that is the case.
     * This is the substitution function that should be implemented.
     */
    def substituteUnsafe(map: Map[SchematicLabel[?], LisaObject[?]]): T
    def substituteUnsafe2[A <: SchematicLabel[?], B <: LisaObject[B]](map: Map[A, B]): T = substituteUnsafe(map.asInstanceOf)

    /**
     * Substitution in the LisaObject of schematics by values, with guaranteed correspondance between the types of schematics and values.
     * This is the substitution that should be used when writing proofs.
     */
    def substitute(pairs: SubstPair*): T = {
      substituteUnsafe(Map(pairs.map(s => (s._1, (s._2: LisaObject[?])))*))
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
    def applyUnsafe(arg: I): O

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
  sealed trait ConstantLabel[-A <: LisaObject[A]] extends Label[A] {
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
  sealed trait Term extends TermOrFormula with LisaObject[Term] {
    val underlying: K.Term
    val label: TermLabel[?]
    val args: Seq[Term]
    def toStringSeparated(): String = toString()
  }

  /**
   * A TermLabel is a [[LisaObject]] of type ((Term ** N) |-> Term), that is represented by a functional label.
   * It can be either a [[SchematicFunctionLabel]] or a [[ConstantFunctionLabel]]. It corresponds to [[K.TermLabel]]
   */
  sealed trait TermLabel[A <: (Term | (Seq[Term] |-> Term)) & LisaObject[A]] extends Label[A] with Absolute {
    this: A & LisaObject[A] =>
    val arity: Arity
    def id: Identifier
    val underlyingLabel: K.TermLabel
    def applySeq(args: Seq[Term]): Term = this match
      case l: Variable => l.applyUnsafe(args)
      case l: Constant => l.applyUnsafe(args)
      case l: FunctionLabel[?] => l.applyUnsafe(args)
    def rename(newid: Identifier): TermLabel[A]
    def freshRename(taken: Iterable[Identifier]): TermLabel[A]
    def mkString(args: Seq[Term]): String
    def mkStringSeparated(args: Seq[Term]): String = mkString(args)
  }

  /**
   * A constant [[TermLabel]], which can be either a [[Constant]] symbol or a [[ConstantFunctionSymbol]]. Corresponds to a [[K.ConstantFunctionLabel]]
   */
  sealed trait ConstantTermLabel[A <: (Term | (Seq[Term] |-> Term)) & LisaObject[A]] extends TermLabel[A] with ConstantLabel[A] {
    this: A & LisaObject[A] =>
    val underlyingLabel: K.ConstantFunctionLabel
    def substituteUnsafe(map: Map[SchematicLabel[?], LisaObject[?]]): ConstantTermLabel[A]
    override def rename(newid: Identifier): ConstantTermLabel[A]
    def freshRename(taken: Iterable[Identifier]): ConstantTermLabel[A]
  }
  object ConstantTermLabel {

    /**
     * Construct a ConstantTermLabel according to arity:
     * A [[Constant]] for arity 0, a [[ConstantFunctionLabel]] otherwise.
     * @param id The identifier of the new symbol
     * @param arity The arity of the new symbol
     * @return The new symbol
     */
    def apply[N <: Arity](id: Identifier, arity: N): ConstantTermLabelOfArity[N] = arity match {
      case a: 0 => Constant(id)
      case n: N => ConstantFunctionLabel[N](id, arity)
    }
  }

  /**
   * Types of constant term labels: [[Constant]] for if N = 0, [[ConstantFunctionLabel]] otherwise.
   */
  type ConstantTermLabelOfArity[N <: Arity] <: ConstantTermLabel[?] = N match
    case 0 => Constant
    case N => ConstantFunctionLabel[N]

  /**
   * A schematic [[TermLabel]], which can be either a [[Variable]] symbol or a [[SchematicFunctionSymbol]]. Corresponds to a [[K.SchematicFunctionLabel]]
   */
  sealed trait SchematicTermLabel[A <: (Term | (Seq[Term] |-> Term)) & LisaObject[A]] extends TermLabel[A] with SchematicLabel[A] {
    this: A & LisaObject[A] =>
    val underlyingLabel: K.SchematicTermLabel
    override def rename(newid: Identifier): SchematicTermLabel[A]
    def freshRename(taken: Iterable[Identifier]): SchematicTermLabel[A]
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
  type SchematicFunctionLabelOfArity[N <: Arity] <: SchematicTermLabel[?] = N match
    case 0 => Variable
    case N => SchematicFunctionLabel[N]

  /**
   * Can be either a [[ConstantFunctionSymbol]] symbol or a [[SchematicFunctionSymbol]]. Corresponds to a [[K.TermLabel]]
   */
  sealed trait FunctionLabel[N <: Arity] extends TermLabel[(Term ** N) |-> Term] with ((Term ** N) |-> Term) {
    val underlyingLabel: K.TermLabel
    def substituteUnsafe(map: Map[SchematicLabel[?], LisaObject[?]]): (Term ** N) |-> Term
    def applyUnsafe(args: (Term ** N)): Term = AppliedFunctional(this, args.toSeq)
    override def rename(newid: Identifier): FunctionLabel[N]
    def freshRename(taken: Iterable[Identifier]): FunctionLabel[N]
  }

  /**
   * A Variable, corresponding to [[K.VariableLabel]], is a schematic symbol for terms.
   * It counts both as the label and as the term itself.
   */
  class Variable(val id: Identifier) extends SchematicTermLabel[Term] with Term with Absolute {
    val arity: 0 = 0
    val label: Variable = this
    val args: Seq[Nothing] = Seq.empty
    val underlyingLabel: K.VariableLabel = K.VariableLabel(id)
    val underlying = K.VariableTerm(underlyingLabel)
    def applyUnsafe(args: Term ** 0) = this
    def substituteUnsafe(map: Map[SchematicLabel[?], LisaObject[?]]): Term = {
      map.get(this) match {
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
    def rename(newid: Identifier): Variable = Variable(newid)
    def freshRename(taken: Iterable[Identifier]): Variable = rename(K.freshId(taken, id))
    override def toString(): String = id
    def mkString(args: Seq[Term]): String = if (args.size == 0) toString() else toString() + "(" + "illegal_arguments: " + args.mkString(", ") + ")"

    def canEqual(that: Any): Boolean =
      that.isInstanceOf[Variable]

    // Intentionally avoiding the call to super.equals because no ancestor has overridden equals (see note 7 below)
    override def equals(that: Any): Boolean =
      that match {
        case other: Variable =>
          ((this eq other) // optional, but highly recommended sans very specific knowledge about this exact class implementation
          || (other.canEqual(this) // optional only if this class is marked final
            && (hashCode == other.hashCode) // optional, exceptionally execution efficient if hashCode is cached, at an obvious space inefficiency tradeoff
            && ((id == other.id))))
        case _ =>
          false
      }

    // Intentionally avoiding the call to super.hashCode because no ancestor has overridden hashCode (see note 7 below)
    override def hashCode(): Int =
      id.##
  }
  object Variable {
    def unapply(variable: Variable): Option[Identifier] = Some(variable.id)
  }

  /**
   * A Constant, corresponding to [[K.ConstantLabel]], is a label for terms.
   * It counts both as the label and as the term itself.
   */
  class Constant(val id: Identifier) extends Term with Absolute with ConstantTermLabel[Constant] with LisaObject[Constant] {
    val arity: 0 = 0
    val label: Constant = this
    val args: Seq[Nothing] = Seq.empty
    val underlyingLabel: K.ConstantFunctionLabel = K.ConstantFunctionLabel(id, 0)
    val underlying = K.Term(underlyingLabel, Seq.empty)
    def applyUnsafe(args: Term ** 0) = this
    def substituteUnsafe(map: Map[SchematicLabel[?], LisaObject[?]]): Constant = this
    def freeSchematicLabels: Set[SchematicLabel[?]] = Set.empty
    def allSchematicLabels: Set[SchematicLabel[?]] = Set.empty
    def rename(newid: Identifier): Constant = Constant(newid)
    def freshRename(taken: Iterable[Identifier]): Constant = rename(K.freshId(taken, id))
    override def toString(): String = id
    def mkString(args: Seq[Term]): String = if (args.size == 0) toString() else toString() + "(" + "illegal_arguments: " + args.mkString(", ") + ")"

    def canEqual(that: Any): Boolean =
      that.isInstanceOf[Constant]

    // Intentionally avoiding the call to super.equals because no ancestor has overridden equals (see note 7 below)
    override def equals(that: Any): Boolean =
      that match {
        case other: Constant =>
          ((this eq other) // optional, but highly recommended sans very specific knowledge about this exact class implementation
          || (other.canEqual(this) // optional only if this class is marked final
            && (hashCode == other.hashCode) // optional, exceptionally execution efficient if hashCode is cached, at an obvious space inefficiency tradeoff
            && ((id == other.id))))
        case _ =>
          false
      }

    // Intentionally avoiding the call to super.hashCode because no ancestor has overridden hashCode (see note 7 below)
    override def hashCode(): Int =
      id.##
  }
  object Constant {
    def unapply(constant: Constant): Option[Identifier] = Some(constant.id)
  }

  /**
   * A schematic functional label (corresponding to [[K.SchematicFunctionLabel]]) is a functional label and also a schematic label.
   * It can be substituted by any expression of type (Term ** N) |-> Term
   */
  class SchematicFunctionLabel[N <: Arity](val id: Identifier, val arity: N) extends SchematicTermLabel[(Term ** N) |-> Term] with FunctionLabel[N] {
    val underlyingLabel: K.SchematicTermLabel = K.SchematicFunctionLabel(id, arity)

    def unapplySeq(t: AppliedFunctional): Seq[Term] = t match {
      case AppliedFunctional(label, args) if (label == this) => args
      case _ => Seq.empty
    }
    @nowarn("msg=the type test for.*cannot be checked at runtime because its type arguments")
    def substituteUnsafe(map: Map[SchematicLabel[?], LisaObject[?]]): ((Term ** N) |-> Term) = {
      map.get(this) match {
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

    def canEqual(that: Any): Boolean =
      that.isInstanceOf[SchematicFunctionLabel[?]]

    // Intentionally avoiding the call to super.equals because no ancestor has overridden equals (see note 7 below)
    override def equals(that: Any): Boolean =
      that match {
        case other: SchematicFunctionLabel[N] =>
          ((this eq other) // optional, but highly recommended sans very specific knowledge about this exact class implementation
          || (other.canEqual(this) // optional only if this class is marked final
            && (hashCode == other.hashCode) // optional, exceptionally execution efficient if hashCode is cached, at an obvious space inefficiency tradeoff
            && ((id == other.id)
              && (arity == other.arity))))
        case _ =>
          false
      }

    // Intentionally avoiding the call to super.hashCode because no ancestor has overridden hashCode (see note 7 below)
    override def hashCode(): Int =
      31 * (
        id.##
      ) + arity.##
  }
  object SchematicFunctionLabel {
    def unapply[N <: Arity](sfl: SchematicFunctionLabel[N]): Option[(Identifier, N)] = Some((sfl.id, sfl.arity))
  }

  /**
   * A constant functional label of arity N.
   */
  class ConstantFunctionLabel[N <: Arity](val id: Identifier, val arity: N) extends ConstantTermLabel[((Term ** N) |-> Term)] with FunctionLabel[N] {
    val underlyingLabel: K.ConstantFunctionLabel = K.ConstantFunctionLabel(id, arity)
    private var infix: Boolean = false
    def unapplySeq(t: AppliedFunctional): Seq[Term] = t match {
      case AppliedFunctional(label, args) if (label == this) => args
      case _ => Seq.empty
    }
    def substituteUnsafe(map: Map[SchematicLabel[?], LisaObject[?]]): ConstantFunctionLabel[N] = this
    def freeSchematicLabels: Set[SchematicLabel[?]] = Set.empty
    def allSchematicLabels: Set[SchematicLabel[?]] = Set.empty
    def rename(newid: Identifier): ConstantFunctionLabel[N] = ConstantFunctionLabel(newid, arity)
    def freshRename(taken: Iterable[Identifier]): ConstantFunctionLabel[N] = rename(K.freshId(taken, id))
    override def toString(): String = id
    def mkString(args: Seq[Term]): String =
      if (infix & args.size == 2) (args(0).toStringSeparated() + " " + toString() + " " + args(1).toStringSeparated()) else toString() + "(" + args.mkString(", ") + ")"
    override def mkStringSeparated(args: Seq[Term]): String = if (infix) "(" + mkString(args) + ")" else mkString(args)

    def canEqual(that: Any): Boolean =
      that.isInstanceOf[SchematicFunctionLabel[?]]

    // Intentionally avoiding the call to super.equals because no ancestor has overridden equals (see note 7 below)
    override def equals(that: Any): Boolean =
      that match {
        case other: ConstantFunctionLabel[N] =>
          ((this eq other) // optional, but highly recommended sans very specific knowledge about this exact class implementation
          || (other.canEqual(this) // optional only if this class is marked final
            && (hashCode == other.hashCode) // optional, exceptionally execution efficient if hashCode is cached, at an obvious space inefficiency tradeoff
            && ((id == other.id)
              && (arity == other.arity))))
        case _ =>
          false
      }

    // Intentionally avoiding the call to super.hashCode because no ancestor has overridden hashCode (see note 7 below)
    override def hashCode(): Int =
      31 * (
        id.##
      ) + arity.##
  }
  object ConstantFunctionLabel {
    def infix[N <: Arity](id: Identifier, arity: N): ConstantFunctionLabel[N] =
      val x = ConstantFunctionLabel[N](id, arity)
      x.infix = true
      x
    def unapply[N <: Arity](cfl: ConstantFunctionLabel[N]): Option[(Identifier, N)] = Some((cfl.id, cfl.arity))
  }

  /**
   * A term made from a functional label of arity N and N arguments
   */
  class AppliedFunctional(val label: FunctionLabel[?], val args: Seq[Term]) extends Term with Absolute {
    override val underlying = K.Term(label.underlyingLabel, args.map(_.underlying))
    def substituteUnsafe(map: Map[SchematicLabel[?], LisaObject[?]]): Term =
      label.substituteUnsafe(map).applyUnsafe(args.map[Term]((x: Term) => x.substituteUnsafe(map)))

    def freeSchematicLabels: Set[SchematicLabel[?]] = label.freeSchematicLabels ++ args.flatMap(_.freeSchematicLabels)
    def allSchematicLabels: Set[SchematicLabel[?]] = label.allSchematicLabels ++ args.flatMap(_.allSchematicLabels)
    override def toString: String = label.mkString(args)
    override def toStringSeparated(): String = label.mkStringSeparated(args)

    def canEqual(that: Any): Boolean =
      that.isInstanceOf[AppliedFunctional]

    // Intentionally avoiding the call to super.equals because no ancestor has overridden equals (see note 7 below)
    override def equals(that: Any): Boolean =
      that match {
        case other: AppliedFunctional =>
          ((this eq other) // optional, but highly recommended sans very specific knowledge about this exact class implementation
          || (other.canEqual(this) // optional only if this class is marked final
            && (hashCode == other.hashCode) // optional, exceptionally execution efficient if hashCode is cached, at an obvious space inefficiency tradeoff
            && ((label == other.label)
              && (args == other.args))))
        case _ =>
          false
      }

    // Intentionally avoiding the call to super.hashCode because no ancestor has overridden hashCode (see note 7 below)
    override def hashCode(): Int =
      31 * (
        label.##
      ) + args.##
  }
  object AppliedFunctional {
    def unapply(af: AppliedFunctional): Option[(FunctionLabel[?], Seq[Term])] = Some((af.label, af.args))
  }

  //////////////////////////////////////
  ////////////// Formulas //////////////
  //////////////////////////////////////

  /**
   * The type of formulas, corresponding to [[K.Formula]]
   */
  sealed trait Formula extends TermOrFormula with LisaObject[Formula] {
    val underlying: K.Formula
    def toStringSeparated() = toString()
  }

  /////////////////////
  // Atomic Formulas //
  /////////////////////

  sealed trait AtomicFormula extends Formula {
    val label: AtomicLabel[?]
    val args: Seq[Term]
  }

  /**
   * A AtomicLabel is a [[LisaObject]] of type ((Term ** N) |-> Formula), that is represented by a predicate label.
   * It can be either a [[SchematicPredicateLabel]] or a [[ConstantPredicateLabel]].
   */
  sealed trait AtomicLabel[A <: (Formula | (Seq[Term] |-> Formula)) & LisaObject[A]] extends Label[A] with Absolute {
    this: A & LisaObject[A] =>
    val arity: Arity
    def id: Identifier
    val underlyingLabel: K.AtomicLabel
    def applySeq(args: Seq[Term]): Formula = this match
      case l: VariableFormula => l.applyUnsafe(args)
      case l: ConstantFormula => l.applyUnsafe(args)
      case l: PredicateLabel[?] => l.applyUnsafe(args)

    def rename(newid: Identifier): AtomicLabel[A]
    def freshRename(taken: Iterable[Identifier]): AtomicLabel[A]
    def mkString(args: Seq[Term]): String
    def mkStringSeparated(args: Seq[Term]): String = mkString(args)
  }

  /**
   * A constant [[AtomicLabel]], which can be either a [[ConstantFormula]] symbol or a [[ConstantPredicateSymbol]]. Corresponds to a [[K.ConstantAtomicLabel]]
   */
  sealed trait ConstantAtomicLabel[A <: (Formula | (Seq[Term] |-> Formula)) & LisaObject[A]] extends AtomicLabel[A] with ConstantLabel[A] {
    this: A & LisaObject[A] =>
    val underlyingLabel: K.ConstantAtomicLabel
    def substituteUnsafe(map: Map[SchematicLabel[?], LisaObject[?]]): ConstantAtomicLabel[A]
    override def rename(newid: Identifier): ConstantAtomicLabel[A]
    def freshRename(taken: Iterable[Identifier]): ConstantAtomicLabel[A]
  }
  object ConstantAtomicLabel {

    /**
     * Construct a ConstantTermLabel according to arity:
     * A [[Constant]] for arity 0, a [[ConstantFunctionLabel]] otherwise.
     * @param id The identifier of the new symbol
     * @param arity The arity of the new symbol
     * @return The new symbol
     */
    def apply[N <: Arity](id: Identifier, arity: N): ConstantAtomicLabelOfArity[N] = arity match {
      case a: 0 => ConstantFormula(id)
      case n: N => ConstantPredicateLabel[N](id, arity)
    }
  }

  /**
   * Types of constant atomic labels: [[ConstantFormula]] for if N = 0, [[ConstantPredicateLabel]] otherwise.
   */
  type ConstantAtomicLabelOfArity[N <: Arity] <: ConstantAtomicLabel[?] = N match {
    case 0 => ConstantFormula
    case N => ConstantPredicateLabel[N]
  }

  /**
   * A schematic [[AtomicLabel]], which can be either a [[VariableFormula]] symbol or a [[SchematicPredicateLabel]]. Corresponds to a [[K.SchematicAtomicLabel]]
   */
  sealed trait SchematicAtomicLabel[A <: (Formula | (Seq[Term] |-> Formula)) & LisaObject[A]] extends AtomicLabel[A] with SchematicLabel[A] {
    this: A & LisaObject[A] =>
    val underlyingLabel: K.SchematicAtomicLabel
    override def rename(newid: Identifier): SchematicAtomicLabel[A]
    def freshRename(taken: Iterable[Identifier]): SchematicAtomicLabel[A]

  }
  object SchematicAtomicLabel { // Companion
    /**
     * Construct a SchematicTermLabel according to arity:
     * A [[Variable]] for arity 0, a [[SchematicFunctionLabel]] otherwise.
     * @param id The identifier of the new symbol
     * @param arity The arity of the new symbol
     * @return The new symbol
     */
    def apply[N <: Arity](id: Identifier, arity: N): SchematicAtomicLabelOfArity[N] = arity match {
      case a: 0 => new VariableFormula(id)
      case n: N => new SchematicPredicateLabel[N](id, arity)
    }
  }

  type SchematicAtomicLabelOfArity[N <: Arity] <: SchematicAtomicLabel[?] = N match {
    case 0 => VariableFormula
    case N => SchematicPredicateLabel[N]
  }

  /**
   * Can be either a [[ConstantFunctionSymbol]] symbol or a [[SchematicFunctionSymbol]]. Corresponds to a [[K.TermLabel]]
   */
  sealed trait PredicateLabel[N <: Arity] extends AtomicLabel[(Term ** N) |-> Formula] with ((Term ** N) |-> Formula) with Absolute {
    val underlyingLabel: K.AtomicLabel
    def substituteUnsafe(map: Map[SchematicLabel[?], LisaObject[?]]): (Term ** N) |-> Formula
    def applyUnsafe(args: (Term ** N)): Formula = AppliedPredicate(this, args.toSeq)
    override def rename(newid: Identifier): PredicateLabel[N]
    def freshRename(taken: Iterable[Identifier]): PredicateLabel[N]
  }

  /**
   * A Variable for formulas, corresponding to [[K.VariableFormulaLabel]], is a schematic symbol for formulas.
   * It counts both as the label and as the term itself.
   */
  case class VariableFormula(id: Identifier) extends SchematicAtomicLabel[Formula] with AtomicFormula with Absolute {
    override val arity: 0 = 0
    val label: VariableFormula = this
    val args: Seq[Nothing] = Seq.empty
    val underlyingLabel: K.VariableFormulaLabel = K.VariableFormulaLabel(id)
    val underlying = K.AtomicFormula(underlyingLabel, Seq.empty)
    def applyUnsafe(args: Term ** 0): Formula = this
    def substituteUnsafe(map: Map[SchematicLabel[?], LisaObject[?]]): Formula = {
      map.get(this) match {
        case Some(subst) =>
          subst match {
            case s: Formula => s
            case _ => throw SubstitutionException()
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
  case class ConstantFormula(id: Identifier) extends ConstantAtomicLabel[Formula] with AtomicFormula with Absolute with ConstantLabel[Formula] {
    override val arity: 0 = 0
    val label: ConstantFormula = this
    val args: Seq[Nothing] = Seq.empty
    val underlyingLabel: K.ConstantAtomicLabel = K.ConstantAtomicLabel(id, 0)
    val underlying = K.AtomicFormula(underlyingLabel, Seq.empty)
    def applyUnsafe(args: Term ** 0): Formula = this
    def substituteUnsafe(map: Map[SchematicLabel[?], LisaObject[?]]): ConstantFormula = this
    def freeSchematicLabels: Set[SchematicLabel[?]] = Set.empty
    def allSchematicLabels: Set[SchematicLabel[?]] = Set.empty
    def rename(newid: Identifier): ConstantFormula = ConstantFormula(newid)
    def freshRename(taken: Iterable[Identifier]): ConstantFormula = rename(K.freshId(taken, id))
    override def toString(): String = id
    def mkString(args: Seq[Term]): String = if (args.size == 0) toString() else toString() + "(" + "illegal_arguments: " + args.mkString(", ") + ")"
  }

  /**
   * A schematic predicate label (corresponding to [[K.SchematicPredicateLabel]]) is a [[AtomicLabel]] and also a [[SchematicLabel]].
   * It can be substituted by any expression of type (Term ** N) |-> Formula
   */
  case class SchematicPredicateLabel[N <: Arity](id: Identifier, arity: N) extends SchematicAtomicLabel[(Term ** N) |-> Formula] with PredicateLabel[N] {
    val underlyingLabel: K.SchematicPredicateLabel = K.SchematicPredicateLabel(id, arity)
    def unapplySeq(t: AppliedFunctional): Seq[Term] = t match {
      case AppliedFunctional(label, args) if (label == this) => args
      case _ => Seq.empty
    }
    @nowarn("msg=the type test for.*cannot be checked at runtime because its type arguments")
    def substituteUnsafe(map: Map[SchematicLabel[?], LisaObject[?]]): |->[Term ** N, Formula] = {
      map.get(this) match {
        case Some(subst) =>
          subst match {
            case s: |->[Term ** N, Formula] => s
            case _ => throw SubstitutionException()
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
   * A constant predicate label corresponding to [[K.ConstantAtomicLabel]] of arity >= 1.
   */
  case class ConstantPredicateLabel[N <: Arity](id: Identifier, arity: N) extends ConstantAtomicLabel[Term ** N |-> Formula] with PredicateLabel[N] {
    val underlyingLabel: K.ConstantAtomicLabel = K.ConstantAtomicLabel(id, arity)
    private var infix = false
    def unapplySeq(f: AppliedPredicate): Seq[Term] = f match {
      case AppliedPredicate(label, args) if (label == this) => args
      case _ => Seq.empty
    }
    def substituteUnsafe(map: Map[SchematicLabel[?], LisaObject[?]]): ConstantPredicateLabel[N] = this
    def freeSchematicLabels: Set[SchematicLabel[?]] = Set.empty
    def allSchematicLabels: Set[SchematicLabel[?]] = Set.empty
    def rename(newid: Identifier): ConstantPredicateLabel[N] = ConstantPredicateLabel(newid, arity)
    def freshRename(taken: Iterable[Identifier]): ConstantPredicateLabel[N] = rename(K.freshId(taken, id))
    override def toString(): String = id
    def mkString(args: Seq[Term]): String = if (infix) (args(0).toStringSeparated() + " " + toString() + " " + args(1).toStringSeparated()) else toString() + "(" + args.mkString(", ") + ")"
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
  case class AppliedPredicate(label: PredicateLabel[?], args: Seq[Term]) extends AtomicFormula with Absolute {
    override val underlying = K.AtomicFormula(label.underlyingLabel, args.map(_.underlying))
    def substituteUnsafe(map: Map[SchematicLabel[?], LisaObject[?]]): Formula =
      label.substituteUnsafe(map).applyUnsafe(args.map[Term]((x: Term) => x.substituteUnsafe(map)))

    def freeSchematicLabels: Set[SchematicLabel[?]] = label.freeSchematicLabels ++ args.toSeq.flatMap(_.freeSchematicLabels)
    def allSchematicLabels: Set[SchematicLabel[?]] = label.allSchematicLabels ++ args.toSeq.flatMap(_.allSchematicLabels)

    override def toString: String = label.mkString(args)
    override def toStringSeparated(): String = label.mkStringSeparated(args)
  }

  ////////////////
  // Connectors //
  ////////////////

  /**
   * A ConnectorLabel is a [[LisaObject]] of type ((Formula ** N) |-> Formula), that is represented by a connector label in the kernel.
   * It can be either a [[SchematicConnectorLabel]] or a [[ConstantConnectorLabel]].
   */
  sealed trait ConnectorLabel extends (Seq[Formula] |-> Formula) with Label[(Seq[Formula] |-> Formula)] with Absolute {
    val arity: Arity
    def id: Identifier
    val underlyingLabel: K.ConnectorLabel
    def applySeq(args: Seq[Formula]): Formula = applyUnsafe(args)
    def rename(newid: Identifier): ConnectorLabel
    def freshRename(taken: Iterable[Identifier]): ConnectorLabel
    def substituteUnsafe(map: Map[SchematicLabel[?], LisaObject[?]]): |->[Seq[Formula], Formula]
    def mkString(args: Seq[Formula]): String
    def mkStringSeparated(args: Seq[Formula]): String

  }

  /**
   * A schematic predicate label (corresponding to [[K.SchematicPredicateLabel]]) is a [[ConnectorLabel]] and also a [[SchematicLabel]].
   * It can be substituted by any expression of type (Formula ** N) |-> Formula
   */
  case class SchematicConnectorLabel[N <: Arity](id: Identifier, arity: N) extends ConnectorLabel with SchematicLabel[Formula ** N |-> Formula] with ((Formula ** N) |-> Formula) {
    val underlyingLabel: K.SchematicConnectorLabel = K.SchematicConnectorLabel(id, arity)
    def unapplySeq(f: AppliedPredicate): Seq[Term] = f match {
      case AppliedPredicate(label, args) if (label == this) => args
      case _ => Seq.empty
    }
    @nowarn("msg=the type test for.*cannot be checked at runtime because its type arguments")
    def substituteUnsafe(map: Map[SchematicLabel[?], LisaObject[?]]): |->[Formula ** N, Formula] = {
      map.get(this) match {
        case Some(subst) =>
          subst match {
            case s: |->[Formula ** N, Formula] => s
            case _ => throw SubstitutionException()
          }
        case None => this
      }
    }
    // def apply(args: Seq[Formula]): Formula = apply(args)
    def applyUnsafe(args: Formula ** N): Formula = AppliedConnector(this, args.toSeq)

    def freeSchematicLabels: Set[SchematicLabel[?]] = Set(this)
    def allSchematicLabels: Set[SchematicLabel[?]] = Set(this)
    def rename(newid: Identifier): SchematicConnectorLabel[N] = SchematicConnectorLabel(newid, arity)
    def freshRename(taken: Iterable[Identifier]): SchematicConnectorLabel[N] = rename(K.freshId(taken, id))
    override def toString(): String = id
    def mkString(args: Seq[Formula]): String = toString() + "(" + args.mkString(", ") + ")"
    def mkStringSeparated(args: Seq[Formula]): String = mkString(args)

  }

  /**
   * A constant connector label is a logical operator such as /\, \/, !, ==>, <=>.
   * It corresponds to a [[K.ConstantConnectorLabel]].
   */
  trait ConstantConnectorLabel[N <: Arity] extends ConnectorLabel with ConstantLabel[Formula ** N |-> Formula] with ((Formula ** N) |-> Formula) {
    val underlyingLabel: K.ConstantConnectorLabel
    def id: Identifier = underlyingLabel.id
    def unapplySeq(f: AppliedConnector): Seq[Formula] = f match {
      case AppliedConnector(label, args) if (label == this) => args
      case _ => Seq.empty
    }
    def substituteUnsafe(map: Map[SchematicLabel[?], LisaObject[?]]): this.type = this
    def applyUnsafe(args: Formula ** N): Formula = AppliedConnector(this, args.toSeq)
    def freeSchematicLabels: Set[SchematicLabel[?]] = Set.empty
    def allSchematicLabels: Set[SchematicLabel[?]] = Set.empty
    def rename(newid: Identifier): ConstantConnectorLabel[N] = throw new Error("Can't rename a constant connector label")
    def freshRename(taken: Iterable[Identifier]): ConstantConnectorLabel[N] = rename(K.freshId(taken, id))
    override def toString(): String = id
    def mkString(args: Seq[Formula]): String = if (args.length == 2) (args(0).toString() + " " + toString() + " " + args(1).toString()) else toString() + "(" + args.mkString(", ") + ")"
    override def mkStringSeparated(args: Seq[Formula]): String = if (args.length == 2) "(" + mkString(args) + ")" else mkString(args)

  }

  /**
   * A formula made from a connector label of arity N and N arguments
   */
  case class AppliedConnector(label: ConnectorLabel, args: Seq[Formula]) extends Formula with Absolute {
    override val underlying = K.ConnectorFormula(label.underlyingLabel, args.map(_.underlying))
    def substituteUnsafe(map: Map[SchematicLabel[?], LisaObject[?]]): Formula =
      label.applyUnsafe(args.map[Formula]((x: Formula) => x.substituteUnsafe(map)))
    def freeSchematicLabels: Set[SchematicLabel[?]] = label.freeSchematicLabels ++ args.flatMap(_.freeSchematicLabels)
    def allSchematicLabels: Set[SchematicLabel[?]] = label.allSchematicLabels ++ args.flatMap(_.allSchematicLabels)
    // override def substituteUnsafe(v: Variable, subs: Term) = AppliedPredicateFormula[N](f, args.map(_.substituteUnsafe(v, subs)))

    override def toString: String = label.mkString(args)
    override def toStringSeparated(): String = label.mkString(args)
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
  trait BaseBinderLabel extends BinderLabel with ((Variable, Formula) |-> BinderFormula) with Absolute {
    val underlyingLabel: K.BinderLabel

    def applyUnsafe(arg: (Variable, Formula)): BinderFormula = BinderFormula(this, arg._1, arg._2)
    def apply(v: Variable, f: Formula): BinderFormula = applyUnsafe((v, f))
    def unapply(b: BinderFormula): Option[(Variable, Formula)] = b match {
      case BinderFormula(label, v, f) if (label == this) => Some((v, f))
      case _ => None
    }
    inline def freeSchematicLabels: Set[SchematicLabel[?]] = Set.empty
    inline def allSchematicLabels: Set[SchematicLabel[?]] = Set.empty
    inline def substituteUnsafe(map: Map[SchematicLabel[?], LisaObject[?]]): this.type = this
    override def toString() = id

  }

  /**
   * A quantified formula made of a [[BaseBinderLabel]] and an underlying formula, in a namefull representation.
   */
  case class BinderFormula(f: BaseBinderLabel, bound: Variable, body: Formula) extends Absolute with Formula with LisaObject[BinderFormula] {
    override val underlying = K.BinderFormula(f.underlyingLabel, bound.underlyingLabel, body.underlying)

    def allSchematicLabels: Set[Common.this.SchematicLabel[?]] = body.allSchematicLabels + bound
    def freeSchematicLabels: Set[Common.this.SchematicLabel[?]] = body.freeSchematicLabels - bound
    def substituteUnsafe(map: Map[SchematicLabel[?], LisaObject[?]]): BinderFormula = {
      val newSubst = map - bound
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

  // Application methods for |->

  extension [S, T <: LisaObject[T]](t: (S ** -1) |-> T) {
    def apply(s: Seq[S]): T = t.applyUnsafe(s)
  }
  extension [S, T <: LisaObject[T], N <: Arity](t: (S ** N) |-> T) {
    def applySeq(s: Seq[S]): T = t.applyUnsafe(s)
  }

  extension [S, T <: LisaObject[T]](t: (S ** 1) |-> T) {
    def apply(s1: S): T = t.applyUnsafe(Seq(s1))
  }
  extension [S, T <: LisaObject[T]](t: (S ** 2) |-> T) {
    def apply(s1: S, s2: S): T = t.applyUnsafe(Seq(s1, s2))
  }
  extension [S <: LisaObject[S], T <: LisaObject[T]](t: (S ** 3) |-> T) {
    def apply(s1: S, s2: S, s3: S): T = t.applyUnsafe(Seq(s1, s2, s3))
  }
  extension [S <: LisaObject[S], T <: LisaObject[T]](t: (S ** 4) |-> T) {
    def apply(s1: S, s2: S, s3: S, s4: S): T = t.applyUnsafe(Seq(s1, s2, s3, s4))
  }
  extension [S <: LisaObject[S], T <: LisaObject[T]](t: (S ** 5) |-> T) {
    def apply(s1: S, s2: S, s3: S, s4: S, s5: S): T = t.applyUnsafe(Seq(s1, s2, s3, s4, s5))
  }

}
