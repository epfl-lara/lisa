package lisa.fol

import lisa.utils.K
import scala.annotation.showAsInfix
import scala.annotation.nowarn
import scala.compiletime.ops.int.-
import scala.reflect.ClassTag
import lisa.utils.UserLisaException

trait Common {

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

  extension[T, N <: Arity] (self: T ** N) {
    @nowarn("msg=checked at runtime")
    @nowarn("msg=match may not be exhaustive")
    def toSeq: Seq[T] = self match {
      case l: Seq[T] => l
      case tup: Tuple => 
        tup.productIterator.toSeq.asInstanceOf[Seq[T]]
    }
    @nowarn("msg=checked at runtime")
    @nowarn("msg=match may not be exhaustive")
    def map[U](f: T => U): U**N = self match {
      case l : Seq[T] => l.map(f).asInstanceOf[(U**(N))]
      case tup : Tuple => tup.map[[t]=>>U]([u] => (x:u) => f(x.asInstanceOf[T])).asInstanceOf
    }
  }


  trait WithArity[N <: Arity] {
    val arity: N
  }

  class BadArityException(msg:String)(using line: sourcecode.Line, file: sourcecode.File) extends UserLisaException(msg) {
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
  class SubstPair(val _1: SchematicLabel[_], val _2: _1.SubstitutionType) {
    def toTuple = (_1, _2)
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
  trait LisaObject[+T<: LisaObject[T]] {
    this: T =>
      
    inline def lift:T & this.type = this

    /**
      * Substitution in the LisaObject of schematics by values. It is not guaranteed by the type system that types of schematics and values match, and the substitution can fail if that is the case.
      * This is the substitution that should be implemented.
      */
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]):T
    /**
      * Substitution in the LisaObject of schematics by values, with guaranteed correspondance between the types of schematics and values.
      * This is the substitution that should be used when writing proofs.
      */
    def substitute(pairs: SubstPair*):T = {
      substituteUnsafe(Map(pairs.map(s => (s._1, (s._2: LisaObject[_])))*))
    }
    def substituteOne[S <: LisaObject[S]](v: SchematicLabel[S], arg: S):T = substituteUnsafe(Map(v->arg))
    /**
      * Compute the free schematic symbols in the expression.
      */
    def freeSchematicLabels:Set[SchematicLabel[?]]
    def freeVariables: Set[Variable] = freeSchematicLabels.collect { case v: Variable => v}
    def freeVariableFormulas: Set[VariableFormula] = freeSchematicLabels.collect { case v: VariableFormula => v}
    /**
      * Compute the free and non-free schematic symbols in the expression.
      */
    def allSchematicLabels:Set[SchematicLabel[?]]
  }


  /**
    * Base types for LisaObjects: Terms and Formulas.
    */
  sealed trait TermOrFormula extends LisaObject[TermOrFormula] {
  }

  /**
    * Constructor types for LISA Objects: Functions into Terms and Formulas.
    */
  @showAsInfix
  infix trait |->[-I, +O <: LisaObject[O]] extends  LisaObject[I|->O] {
    def apply(arg: I): O

  }

  /**
    * A label is a [[LisaObject]] which is just a name. In general, constant symbols and schematic symbols.
    */
  trait Label[+A <: LisaObject[A]] extends LisaObject[A]{
    this : A =>
    def id: K.Identifier
    /**
      * Indicates how to rename the symbol.
      */
    def rename(newid: K.Identifier): Label[A]
    def freshRename(taken:Iterable[K.Identifier]): Label[A]
  }
  /**
    * Schematic labels can be substituted by expressions (LisaObject) of the corresponding type
    */
  sealed trait SchematicLabel[A <: LisaObject[A]] extends LisaObject[A] with Label[A]{
    this : A =>
    /**
      * The schematic label can be substituted by anything of an equivalent type. See [[SubstPair]], [[LisaObject]].
      */
    type SubstitutionType = A
    def rename(newid: K.Identifier):SchematicLabel[A]
    def freshRename(taken:Iterable[K.Identifier]): SchematicLabel[A]

    /**
      * Helper to build a [[SubstPair]]
      */
    def :=(replacement:A) = SubstPair(this, replacement)

  }


  /**
    * ConstantLabel represent constants in the theory and can't be freely substituted.
    */
  sealed trait ConstantLabel[+A <: LisaObject[A]]  extends LisaObject[A] with Label[A] {
    this : A =>
    def rename(newid: K.Identifier):ConstantLabel[A]
    def freshRename(taken:Iterable[K.Identifier]): ConstantLabel[A]
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



  //////////
  // Term //
  //////////


  /**
    * The type of terms, corresponding to [[K.Term]]
    */
  sealed abstract class Term extends TermOrFormula with LisaObject[Term] with ((Term ** 0) |-> Term) {
    def apply(args: Term ** 0): Term = this
    val underlying: K.Term


  }

  /////////////////////
  // Matching Kernel //
  /////////////////////
  /**
    * A TermLabel is a [[LisaObject]] of type ((Term ** N) |-> Term), that is represented by a functional label.
    * It can be either a [[SchematicFunctionLabel]] or a [[ConstantFunctionLabel]].
    */
  sealed trait TermLabel extends (Seq[Term] |-> Term)  with Absolute {
    val arity: Arity
    def id: K.Identifier
    val underlyingLabel: K.TermLabel
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): (Seq[Term] |-> Term)
    def rename(newid: K.Identifier):TermLabel
    def freshRename(taken:Iterable[K.Identifier]): TermLabel

  }

  sealed trait ConstantTermLabel extends TermLabel/* with ConstantLabel[ConstantTermLabel] */{
    //def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): ConstantTermLabel
    //def rename(newid: K.Identifier):ConstantTermLabel
    //def freshRename(taken:Iterable[K.Identifier]): ConstantTermLabel
  }
  sealed trait SchematicTermLabel extends TermLabel 

  /**
    * A Variable, corresponding to [[K.VariableLabel]], is a schematic symbol for terms.
    * It counts both as the label and as the term itself.
    *
    */
  case class Variable(id: K.Identifier) extends Term with Absolute with SchematicLabel[Term] with SchematicTermLabel with LisaObject[Term]{
    val arity = 0
    val underlyingLabel: K.VariableLabel = K.VariableLabel(id)
    val underlying = K.VariableTerm(underlyingLabel)

    def apply(args: Seq[Term]) = this

    @nowarn("msg=Unreachable")
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): Term = {
      map.get(this.asInstanceOf) match {
        case Some(subst) => subst match {
          case s: Term => s
          case _ => throw SubstitutionException()
        }
        case None => this
      }
    }

    def freeSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def allSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def rename(newid: K.Identifier):Variable = Variable(newid)
    def freshRename(taken:Iterable[K.Identifier]): Variable = rename(K.freshId(taken, id))

  }

  /**
    * A Constant, corresponding to [[K.ConstantLabel]], is a label for terms.
    * It counts both as the label and as the term itself.
    */
  case class Constant(id: K.Identifier) extends Term with Absolute with ConstantLabel[Constant] with ConstantTermLabel{
    val arity = 0
    val underlyingLabel: K.ConstantFunctionLabel = K.ConstantFunctionLabel(id, 0)
    val underlying = K.Term(underlyingLabel, Seq())

    def apply(args: Seq[Term]) = this

    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]):Constant = this
    def freeSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def allSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def rename(newid: K.Identifier): Constant = Constant(newid)
    def freshRename(taken:Iterable[K.Identifier]): Constant = rename(K.freshId(taken, id))

  }



  /**
    * A schematic functional label (corresponding to [[K.SchematicFunctionLabel]]) is a functional label and also a schematic label.
    * It can be substituted by any expression of type (Term ** N) |-> Term
    */
  case class SchematicFunctionLabel[N <: Arity](id: K.Identifier, arity : N) extends SchematicTermLabel with SchematicLabel[(Term ** N) |-> Term] with ((Term ** N) |-> Term) {
    val underlyingLabel: K.SchematicFunctionLabel = K.SchematicFunctionLabel(id, arity)
    def apply(args: (Term ** N)): Term = AppliedTerm(this, args.toSeq)
    @nowarn
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): ((Term ** N) |-> Term) = {
      map.get(this.asInstanceOf) match {
        case Some(subst) => subst match {
          case s: ((Term ** N) |-> Term) => s
          case _ => throw SubstitutionException()
        }
        case None => this.lift
      }
    }
    def freeSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def allSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def rename(newid: K.Identifier):SchematicFunctionLabel[N] = SchematicFunctionLabel(newid, arity)
    def freshRename(taken:Iterable[K.Identifier]): SchematicFunctionLabel[N] = rename(K.freshId(taken, id))
  }

  /**
    * A constant functional label of arity N.
    */
  case class ConstantFunctionLabel[N <: Arity](id: K.Identifier, arity : N) extends ConstantTermLabel with ConstantLabel[((Term ** N) |-> Term)] with ((Term ** N) |-> Term){
    val underlyingLabel: K.ConstantFunctionLabel = K.ConstantFunctionLabel(id, arity)
    def apply(args: (Term ** N)): Term = AppliedTerm(this, args.toSeq)
    inline def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): this.type =
      this
    def freeSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def allSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def rename(newid: K.Identifier):ConstantFunctionLabel[N] = ConstantFunctionLabel(newid, arity)
    def freshRename(taken:Iterable[K.Identifier]): ConstantFunctionLabel[N] = rename(K.freshId(taken, id))
  }

  /**
    * A term made from a functional label of arity N and N arguments
    */
  case class AppliedTerm private[Common] (f: TermLabel, args: Seq[Term]) extends Term with Absolute {

    override val underlying = K.Term(f.underlyingLabel, args.map(_.underlying))
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]):Term = {
      f.substituteUnsafe(map)(
        args.map[Term]((x:Term) => x.substituteUnsafe(map))
      )
    }

    def freeSchematicLabels:Set[SchematicLabel[?]] = f.freeSchematicLabels ++ args.flatMap(_.freeSchematicLabels)
    def allSchematicLabels:Set[SchematicLabel[?]] = f.allSchematicLabels ++ args.flatMap(_.allSchematicLabels)
    //override def substituteUnsafe(v: Variable, subs: Term) = AppliedTerm[N](f, args.map(_.substituteUnsafe(v, subs)))
  }

  //////////////
  // Formulas //
  //////////////


  /**
    * The type of formulas, corresponding to [[K.Formula]]
    */
  sealed abstract class Formula extends TermOrFormula with LisaObject[Formula] with ((Term ** 0) |-> Formula){
    val arity : Arity = 0
    def apply(args:Term**0): Formula = this
    val underlying: K.Formula

  }

  /**
    * A Variable for formulas, corresponding to [[K.VariableFormulaLabel]], is a schematic symbol for formulas.
    * It counts both as the label and as the term itself.
    */
  case class VariableFormula(id: K.Identifier) extends Formula with PredicateLabel[0] with SchematicLabel[Formula] {
    override val arity : 0 = 0
    val underlyingLabel: K.VariableFormulaLabel = K.VariableFormulaLabel(id)
    val underlying = K.PredicateFormula(underlyingLabel, Seq())

    override def apply(args:Term**0): Formula = this
    @nowarn("msg=Unreachable")
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): Formula = {
      map.get(this.asInstanceOf) match {
        case Some(subst) => subst match {
          case s: Formula => s
        }
        case None => this
      }
    }
    def freeSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def allSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def rename(newid: K.Identifier):VariableFormula = VariableFormula(newid)
    def freshRename(taken:Iterable[K.Identifier]): VariableFormula = rename(K.freshId(taken, id))
  }
  /**
    * A Constant formula, corresponding to [[K.ConstantFormulaLabel]].
    * It counts both as the label and as the formula itself. Usually either True or False.
    */
  case class ConstantFormula(id: K.Identifier) extends Formula with PredicateLabel[0] with ConstantLabel[Formula] {
    override val arity : 0 = 0
    val underlyingLabel: K.ConstantPredicateLabel = K.ConstantPredicateLabel(id, 0)
    val underlying = K.PredicateFormula(underlyingLabel, Seq())
    override def apply(args:Term**0): Formula = this
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]):this.type = this
    def freeSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def allSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def rename(newid: K.Identifier):ConstantFormula = ConstantFormula(newid)
    def freshRename(taken:Iterable[K.Identifier]): ConstantFormula = rename(K.freshId(taken, id))
  }

  /**
    * A PredicateLabel is a [[LisaObject]] of type ((Term ** N) |-> Formula), that is represented by a predicate label.
    * It can be either a [[SchematicPredicateLabel]] or a [[ConstantPredicateLabel]].
    */
  sealed trait PredicateLabel[N <: Arity] extends |->[Term ** N, Formula] with WithArity[N] with Absolute {
    val arity : N
    def id: K.Identifier
    val underlyingLabel: K.PredicateLabel // | K.LambdaFormulaFormula

    def apply(args: Term ** N): Formula = PredicateFormula[N](this, args.toSeq)
    def rename(newid: K.Identifier): PredicateLabel[N]
    def freshRename(taken:Iterable[K.Identifier]): PredicateLabel[N]
  }

  /**
    * A schematic predicate label (corresponding to [[K.SchematicPredicateLabel]]) is a [[PredicateLabel]] and also a [[SchematicLabel]].
    * It can be substituted by any expression of type (Term ** N) |-> Formula
    */
  case class SchematicPredicateLabel[N <: Arity](id: K.Identifier, arity : N) extends PredicateLabel[N] with SchematicLabel[Term ** N |->Formula]{
    val underlyingLabel: K.SchematicPredicateLabel = K.SchematicPredicateLabel(id, arity)

    @nowarn
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): |->[Term ** N, Formula]  = {
      map.get(this.asInstanceOf) match {
        case Some(subst) => subst match {
          case s: |->[Term ** N, Formula]  => s
        }
        case None => this
      }
    }
    def freeSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def allSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def rename(newid: K.Identifier): SchematicPredicateLabel[N] = SchematicPredicateLabel(newid, arity)
    def freshRename(taken:Iterable[K.Identifier]): SchematicPredicateLabel[N] = rename(K.freshId(taken, id))

  }

  /**
    * A constant predicate label corresponding to [[K.ConstantPredicateLabel]].
    */
  case class ConstantPredicateLabel[N <: Arity](id: K.Identifier, arity : N) extends PredicateLabel[N] with ConstantLabel[Term ** N |->Formula]{
    val underlyingLabel: K.ConstantPredicateLabel = K.ConstantPredicateLabel(id, arity)
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): this.type =
      this
    def freeSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def allSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def rename(newid: K.Identifier): ConstantPredicateLabel[N] = ConstantPredicateLabel(newid, arity)
    def freshRename(taken:Iterable[K.Identifier]): ConstantPredicateLabel[N] = rename(K.freshId(taken, id))
  }

  /**
    * A formula made from a predicate label of arity N and N arguments
    */
  case class PredicateFormula[N <: Arity](p: PredicateLabel[N], args: Seq[Term]) extends Formula with Absolute {
    override val underlying = K.PredicateFormula(p.underlyingLabel, args.map(_.underlying))
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]):Formula =
      p.substituteUnsafe(map)(args.map[Term]((x:Term) => x.substituteUnsafe(map)))

    def freeSchematicLabels:Set[SchematicLabel[?]] = p.freeSchematicLabels ++ args.toSeq.flatMap(_.freeSchematicLabels)
    def allSchematicLabels:Set[SchematicLabel[?]] = p.allSchematicLabels ++ args.toSeq.flatMap(_.allSchematicLabels)
  }

/**
  * A ConnectorLabel is a [[LisaObject]] of type ((Formula ** N) |-> Formula), that is represented by a connector label in the kernel.
  * It can be either a [[SchematicConnectorLabel]] or a [[ConstantConnectorLabel]].
  */
  sealed trait ConnectorLabel[N <: Arity] extends |->[Formula ** N, Formula] with WithArity[N] with Absolute with Label[(Formula**N) |-> Formula] {
    val arity : N
    def id: K.Identifier
    val underlyingLabel: K.ConnectorLabel
    
    def apply(args: Formula ** N): ConnectorFormula = ConnectorFormula(this, args.toSeq)
    def rename(newid: K.Identifier):ConnectorLabel[N]
    def freshRename(taken:Iterable[K.Identifier]): ConnectorLabel[N]

    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): |->[Formula ** N, Formula]

  }

  /**
    * A schematic predicate label (corresponding to [[K.SchematicPredicateLabel]]) is a [[ConnectorLabel]] and also a [[SchematicLabel]].
    * It can be substituted by any expression of type (Formula ** N) |-> Formula
  */
  case class SchematicConnectorLabel[N <: Arity](id: K.Identifier, arity : N) extends ConnectorLabel[N] with SchematicLabel[Formula ** N |->Formula]{
    val underlyingLabel: K.SchematicConnectorLabel = K.SchematicConnectorLabel(id, arity)

    @nowarn
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): |->[Formula ** N, Formula] = {
      map.get(this.asInstanceOf) match {
        case Some(subst) => subst match {
          case s: |->[Formula ** N, Formula]  => s
        }
        case None => this
      }
    }
    def freeSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def allSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def rename(newid: K.Identifier): SchematicConnectorLabel[N] = SchematicConnectorLabel(newid, arity)
    def freshRename(taken:Iterable[K.Identifier]): SchematicConnectorLabel[N] = rename(K.freshId(taken, id))

  }

  /**
    * A constant connector label is a logical operator such as /\, \/, !, ==>, <=>.
    * It corresponds to a [[K.ConstantConnectorLabel]].
    */
  trait ConstantConnectorLabel[N <: Arity] extends ConnectorLabel[N] with ConstantLabel[Formula ** N |-> Formula]{
    val underlyingLabel: K.ConstantConnectorLabel
    def id: K.Identifier = underlyingLabel.id
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): this.type = this
    def freeSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def allSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def rename(newid: K.Identifier): ConstantConnectorLabel[N] = throw new Error("Can't rename a constant connector label")
    def freshRename(taken:Iterable[K.Identifier]): ConstantConnectorLabel[N] = rename(K.freshId(taken, id))

  }
  /**
    * A formula made from a connector label of arity N and N arguments
    */
  case class ConnectorFormula(p: ConnectorLabel[?], args: Seq[Formula]) extends Formula with Absolute {
    assert(args.length == p.arity)
    override val underlying = K.ConnectorFormula(p.underlyingLabel, args.map(_.underlying))
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]):Formula = {
      val p2 = p.substituteUnsafe(map)
      p2 match {
        case p2 : ConnectorLabel[?] => ConnectorFormula(p2, args.map[Formula]((x:Formula) => x.substituteUnsafe(map)))
        case _ => p2(args.map[Formula]((x:Formula) => x.substituteUnsafe(map)))
      }
    }

    def freeSchematicLabels:Set[SchematicLabel[?]] = p.freeSchematicLabels ++ args.flatMap(_.freeSchematicLabels)
    def allSchematicLabels:Set[SchematicLabel[?]] = p.allSchematicLabels ++ args.flatMap(_.allSchematicLabels)
    //override def substituteUnsafe(v: Variable, subs: Term) = PredicateFormulaFormula[N](f, args.map(_.substituteUnsafe(v, subs)))
  }


  /**
    * A binder for variables, for example \exists, \forall and \exists! but possibly others.
    */
  abstract class BinderLabel extends |->[(Variable, Formula), Formula] with Absolute {
    def id: K.Identifier
  }

  /**
    * A binder label that exactly correspond to a kernel binder, i.e. \exists, \forall and \exists!
    */
  trait BaseBinderLabel extends BinderLabel with Absolute {
    val underlyingLabel: K.BinderLabel

    def apply(arg: (Variable, Formula)): BinderFormula = BinderFormula(this, arg._1, arg._2)
    inline def freeSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    inline def allSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    inline def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): this.type = this

  }

  /**
    * A quantified formula made of a [[BaseBinderLabel]] and an underlying formula, in a namefull representation.
    *
    */
  case class BinderFormula(f: BaseBinderLabel, bound: Variable, body: Formula) extends Formula with Absolute {
    override val underlying = K.BinderFormula(f.underlyingLabel, bound.underlyingLabel, body.underlying)

    def allSchematicLabels: Set[Common.this.SchematicLabel[?]] = body.allSchematicLabels+bound
    def freeSchematicLabels: Set[Common.this.SchematicLabel[?]] = body.freeSchematicLabels-bound
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): Formula = {
      val newSubst = map - bound.asInstanceOf
      if (map.values.flatMap(_.freeSchematicLabels).toSet.contains(bound)){
        val taken:Set[SchematicLabel[?]] = body.allSchematicLabels ++ map.keys
        val newBound:Variable = bound.rename(lisa.utils.KernelHelpers.freshId(taken.map(_.id), bound.id))
        val newBody = body.substituteOne(bound, newBound.lift)
        BinderFormula(f, newBound, newBody.substituteUnsafe(newSubst))
      } else {
        BinderFormula(f, bound, body.substituteUnsafe(newSubst))
      }
    }

  }
  def instantiateBinder(f: BinderFormula, t: Term): Formula = f.body.substituteUnsafe(Map(f.bound -> t))


}
