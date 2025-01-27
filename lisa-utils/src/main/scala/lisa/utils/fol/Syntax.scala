package lisa.utils.fol

import lisa.utils.K
import lisa.utils.K.Identifier
import lisa.utils.K.given_Conversion_String_Identifier


import scala.annotation.nowarn
import scala.annotation.showAsInfix
import scala.annotation.targetName
import scala.util.Sorting
import lisa.utils.KernelHelpers.freshId

trait Syntax {

  type IsSort[T] = Sort{type Self = T}

  @showAsInfix
  infix type >>:[I, O] = Arrow[I, O]

  /** 
   * A trait representing a sort. 
   * 
   * Sorts are used to classify expressions and are either [[Ind]], [[Prop]], or _ [[Arrow]] _.
   */
  trait Sort {
    type Self
    val underlying: K.Sort
  }


  /** 
   * The sort of individuals, i.e. sets, numbers, etc. Corresponds to [[K.Ind]] 
   */
  sealed trait Ind
  /** The sort of propositions. Corresponds to [[K.Prop]] */
  sealed trait Prop
  /** The sort of expression which take arguments. Corresponds to [[K.Arrow]]. Can be used as `A >>: B` */
  sealed trait Arrow[A: Sort, B: Sort]

  /** Typeclass asserting that [[Ind]] is a sort */
  given given_TermType:  IsSort[Ind] with
    val underlying = K.Ind
  /** Typeclass asserting that [[Prop]] is a sort */
  given given_FormulaType: IsSort[Prop] with
    val underlying = K.Prop
  /** Typeclass asserting that [[Arrow]][_, _] is a sort */
  given given_ArrowType[A : Sort as ta, B : Sort as tb]: (IsSort[Arrow[A, B]]) with
    val underlying = K.Arrow(ta.underlying, tb.underlying)

  /**
    * A pair of a variable and an expression of matching Sort. Used for substitution.
    */
  sealed trait SubstPair extends Product {
    type S
    val _1: Variable[S]
    val _2: Expr[S]
  }

  /** Concrete implementation of the [[SubstPair]] trait. Done this way to havee a type membeer instead of a type parameter.*/
  private case class ConcreteSubstPair[S1] (_1: Variable[S1], _2: Expr[S1]) extends SubstPair {type S = S1}

  /** Factory object for [[SubstPair]] */
  object SubstPair {
    /** Creates a new well-sorted substitution pair. */
    def apply[S1 : Sort](_1: Variable[S1], _2: Expr[S1]): SubstPair {type S = S1} = new ConcreteSubstPair[S1](_1, _2)
    def unapply[S1](s: SubstPair{type S = S1}): SubstPair{type S = S1} = s
  }

  /** 
   * Used to cast expressions to a specific sort, without checking.
   * Useful when the type is not known at compile time.
   */
  def unsafeSortEvidence[S](sort: K.Sort) : IsSort[S] = new Sort { type Self = S; val underlying = sort }

  /** Converts a (Variable, Expr) pair to a SubstPair */
  given [T: Sort]: Conversion[(Variable[T], Expr[T]), SubstPair{type S = T}] = s => SubstPair(s._1, s._2)


  /** A match type that extracts the arguments of `S1` such that `Target` is the return sort. 
   * 
   * For example, 
   * 
   * `ArgsTo[Arrow[A, B], B]` will be `Expr[A] *: EmptyTuple`.
   * 
   * `ArgsTo[Arrow[A, Arrow[B, C]], C]` will be `Expr[A] *: Expr[B] *: EmptyTuple`.
   * 
  */
  type ArgsTo[S1, Target] <: NonEmptyTuple = S1 match {
    case Arrow[a, Target] => Tuple1[Expr[a]]
    case Arrow[a, b] => Expr[a] *: ArgsTo[b, Target]
  }


  /**
    * An object that supports substitution of variables with expressions.
    * Typically, [[Expr]] and [[Sequent]] are LisaObjects.
    */
  trait LisaObject {
    /** Performs simultaneous substitution of variables with expressions.
      * 
      * If the substitution is not well-sorted, an exception may be thrown when constructing the result.
      *
      * @param m The map of substitutions 
      * @return The result of the substitution
      * 
      * @see [[substituteWithCheck]]
      * @see [[substitute]]
      */
    def substituteUnsafe(m: Map[Variable[?], Expr[?]]): LisaObject

    /** Performs simultaneous substitution of variables with expressions. First checks that the sorts of the substitution map.
      *
      * @param m The map of substitutions
      * @return The result of the substitution
      * @throws IllegalArgumentException if the substitution is not well-sorted
      */
    def substituteWithCheck(m: Map[Variable[?], Expr[?]]): LisaObject = {
      if m.forall((k, v) => k.sort == v.sort) then
        substituteUnsafe(m)
      else 
        val culprit = m.find((k, v) => k.sort != v.sort).get
        throw new IllegalArgumentException("Sort mismatch in substitution: " + culprit._1 + " -> " + culprit._2)
    }

    /** Performs simultaneous substitution of variables with expressions. 
      * 
      * @param pairs The pairs of substitutions
      * @return The result of the substitution
      */
    def substitute(pairs: SubstPair*): LisaObject = 
      substituteWithCheck(pairs.view.map(s => (s._1, s._2)).toMap)

    /** Returns the set of free variables in the expression */
    def freeVars: Set[Variable[?]] 
    /** Returns the set of free variables of sort [[Ind]] in the expression */
    def freeTermVars: Set[Variable[Ind]]
    /** Returns the set of constants in the expression */
    def constants: Set[Constant[?]]
  }

  /** 
   * A Lisa expression. 
   * 
   * Expressions are elements of the simply typed lambda calculus with base types (called [[Sort]]) [[Ind]] and [[Prop]].
   * 
   * @tparam S The sort of the expression, usually [[Ind]], [[Prop]], or an [[Arrow]].
   */
  sealed trait Expr[S] extends LisaObject {
    /** The sort of the expression */
    val sort: K.Sort
    private val arity = K.flatTypeParameters(sort).size

    /** The underlying kernel expression */
    def underlying: K.Expression

    def substituteUnsafe(m: Map[Variable[?], Expr[?]]): Expr[S]
    override def substituteWithCheck(m: Map[Variable[?], Expr[?]]): Expr[S] =
      super.substituteWithCheck(m).asInstanceOf[Expr[S]]
    override def substitute(pairs: SubstPair*): Expr[S] = 
      super.substitute(pairs*).asInstanceOf[Expr[S]]

    /** Extracts the applied arguments of the expression.
      * 
      * For example, let `f :: A >>: B >>: C`. then
      * {{{
      * f(a)(b)(c) match {
      *   case f(a, b, c) => ...
      * }}}
      *
      */
    def unapplySeq[Target](e: Expr[Target]): Option[ArgsTo[S, Target]] = 
      def inner[Target](e: Expr[Target]): Option[ArgsTo[S, Target]] = e match
        case App(f2, arg) if this == f2 => Some((arg *: EmptyTuple).asInstanceOf[ArgsTo[S, Target]])
        case App(f2, arg) => inner(f2).map(value => (arg *: value).asInstanceOf[ArgsTo[S, Target]])
        case _ => None
      inner[Target](e)

    @targetName("unapplySeq2")
    def unapplySeq(e: Expr[?]): Option[Seq[Expr[?]]] = Multiapp(this).unapply(e)

    /** Default String representation of the expression, with potential arguments. */
    final def defaultMkString(args: Seq[Expr[?]]): String = s"$this(${args.map(a => s"${a}").mkString(", ")})"
    /** Default String representation of the expression, with potential arguments, encapsulated by parenthesis if necessary. */
    final def defaultMkStringSeparated(args: Seq[Expr[?]]): String = s"(${defaultMkString(args)})"
    /** String representation of the expression, with potential arguments. Can be updated.*/
    var mkString: Seq[Expr[?]] => String = defaultMkString
    /** String representation of the expression, with potential arguments, encapsulated by parenthesis if necessary. Can be updated.*/
    var mkStringSeparated: Seq[Expr[?]] => String = defaultMkStringSeparated


    /** Construct an unsafe application. If the sorts don't match, will throw an exception.
      * @param arg The argument to apply to `this`.
      * @throws IllegalArgumentException if the sorts don't match.
      */
    def #@(arg: Expr[?]): RetExpr[S] = 
      App.unsafe(this, arg).asInstanceOf

    /** Iteratively construct an unsafe application. If the sorts don't match, will throw an exception.
     * @param args The arguments to apply to `this`.
     * @throws IllegalArgumentException if the sorts don't match.
     */
    def #@@(args: Seq[Expr[?]]): Expr[?] = 
      Multiapp.unsafe(this, args)

    /** A structural representation of the expression for debugging purposes.
     * 
     * Equal to the default representation of case classes.
     */
    def structuralToString: String = this match
      case Variable(id) => s"Variable($id, $sort)"
      case Constant(id) => s"Constant($id, $sort)"
      case App(f, arg) => s"App(${f.structuralToString}, ${arg.structuralToString})"
      case Abs(v, body) => s"Abs(${v.structuralToString}, ${body.structuralToString})"
  }

  /** (Inline) extractor object for unsafe applications */
  object #@ {
    /** Extracts the function and argument of an application. 
      * Example: 
      * {{{
      * singleton(∅) match 
      *   case f #@ x => ...
      * }}}
      */
    def unapply[S, T](e: Expr[T]): Option[(Expr[Arrow[S, T]], Expr[S])] = (e: @unchecked) match
      case App[S, T](f, arg) => Some((f, arg))
      case _ => None
  }

  /** Well-sorted application constructor. Used when sorts are known at compile time. */
  extension [S, T](f: Expr[Arrow[S, T]]) 
    def apply(using IsSort[S], IsSort[T])(arg: Expr[S]): Expr[T] = App(f, arg)


  /** match type computing the return sort of an arrow sort. */
  type RetExpr[T] <: Expr[?] = T match {
    case Arrow[a, b] => Expr[b]
  }

  /** Utility class for expressions taking multiple arguments. */
  class Multiapp(f: Expr[?]):
    /** Extractor for expressions with multiple arguments. */
    def unapply (e: Expr[?]): Option[Seq[Expr[?]]] = 
      def inner(e: Expr[?]): Option[List[Expr[?]]] = e match
        case App(f2, arg) if f == f2 => Some(List(arg))
        case App(f2, arg) => inner(f2).map(arg :: _)
        case _ => None
      inner(e).map(_.reverse)

  /** Utility object for expressions taking multiple arguments. */
  object Multiapp:
    def unsafe(f: Expr[?], args: Seq[Expr[?]]): Expr[?] = 
      args.foldLeft(f)((f, arg) => App.unsafe(f, arg))
    def unapply(e: Expr[?]): Some[(Expr[?], Seq[Expr[?]])] = Some(unfoldAllApp(e))
  
  /** Computes the list of consecutively applied arguments of an expression. 
    * Example: 
    * {{{
    * unfoldAllApp(Abs(x, f(x))(a)(b)(c)) == (Abs(x, f(x)), List(a, b, c))
    * 
    * @param e
    * @return
    */
  def unfoldAllApp(e:Expr[?]): (Expr[?], List[Expr[?]]) = 
    def rec(e: Expr[?]): (Expr[?], List[Expr[?]]) = e match
      case App(f, arg) =>
        val (f1, args) = unfoldAllApp(f)
        (f1, arg :: args )
      case _ => (e, Nil)
    val (f, args) = rec(e)
    (f, args.reverse)




  /**
    * A variable of a given sort.
    * 
    * Variables are leaf [[Expr]]essions that can be bound and instantiated.
    * 
    * Corresponds to [[K.Variable]].
    * 
    * @tparam S The sort of the variable.
    *
    */
  case class Variable[S : Sort as sortEv](id: K.Identifier) extends Expr[S] {
    /** The runtime sort of the variable */
    val sort: K.Sort = sortEv.underlying
    /** The underlying kernel variable */
    val underlying: K.Variable = K.Variable(id, sort)
    def substituteUnsafe(m: Map[Variable[?], Expr[?]]): Expr[S] = m.getOrElse(this, this).asInstanceOf[Expr[S]]
    override def substituteWithCheck(m: Map[Variable[?], Expr[?]]): Expr[S] =
      super.substituteWithCheck(m).asInstanceOf[Expr[S]]
    override def substitute(pairs: SubstPair*): Expr[S] = 
      super.substitute(pairs*).asInstanceOf[Expr[S]]
    def freeVars: Set[Variable[?]] = Set(this)
    def freeTermVars: Set[Variable[Ind]] = if sort == K.Ind then Set(this.asInstanceOf) else Set.empty
    def constants: Set[Constant[?]] = Set.empty
    /** Returns a variable of the same type with the given identifier */
    def rename(newId: K.Identifier): Variable[S] = Variable(newId)
    /** Returns a variable with a fresh identifier, with respect to the given expressions */
    def freshRename(existing: Iterable[Expr[?]]): Variable[S] = {
      val newId = K.freshId(existing.flatMap(_.freeVars.map(_.id)), id)
      Variable(newId)
    }
    override def toString(): String = id.toString
    /** Constructs a [[SubstPair]]. Used for substitutions and instantiations. */
    def :=(replacement: Expr[S]) = SubstPair(this, replacement)
  }

  /** Factory object for [[Variable]].
    */
  object Variable {
    def unsafe(id: String, sort: K.Sort): Variable[?] = Variable(id)(using unsafeSortEvidence(sort))
    /** Constructs a variable whose sort is only known at runtime. */
    def unsafe(id: Identifier, sort: K.Sort): Variable[?] = Variable(id)(using unsafeSortEvidence(sort))
  }


  /**
    * A constant of a given sort.
    * 
    * Constants are leaf [[Expr]]essions that cannot be bound or instantiated. They are usually user-defined, or fixed by a theory.
    * 
    */
  case class Constant[S : Sort as sortEv](id: K.Identifier) extends Expr[S] {
    val sort: K.Sort = sortEv.underlying
    private var infix: Boolean = false
    /** Set the variable to be printed infix. 
     * 
     * Does not affect the input syntax. To allow infix input syntax, define an `extension`.
     */
    def printInfix(): Constant[S] = 
      infix = true
      this
    val underlying: K.Constant = K.Constant(id, sort)
    def substituteUnsafe(m: Map[Variable[?], Expr[?]]): Constant[S] = this
    override def substituteWithCheck(m: Map[Variable[?], Expr[?]]): Expr[S] =
      super.substituteWithCheck(m).asInstanceOf[Constant[S]]
    override def substitute(pairs: SubstPair*): Constant[S] = 
      super.substitute(pairs*).asInstanceOf[Constant[S]]
    def freeVars: Set[Variable[?]] = Set.empty
    def freeTermVars: Set[Variable[Ind]] = Set.empty
    def constants: Set[Constant[?]] = Set(this)
    /** Returns a constant with the given identifier */
    def rename(newId: K.Identifier): Constant[S] = Constant(newId)
    // Special handling for inxfix constants
    override def toString(): String = id.toString
    mkString = (args: Seq[Expr[?]]) => 
      if infix && args.size == 2 then 
        s"${args(0)} $this ${args(1)}"
      else if infix & args.size > 2 then
        s"(${args(0)} $this ${args(1)})${args.drop(2).map(_.mkStringSeparated).mkString})"
      else 
        defaultMkString(args)
    mkStringSeparated = (args: Seq[Expr[?]]) => 
      if infix && args.size == 2 then 
        s"${args(0)} $this ${args(1)}"
      else if infix & args.size > 2 then
        s"(${args(0)} $this ${args(1)})${args.drop(2).map(_.mkStringSeparated).mkString})"
      else 
        defaultMkStringSeparated(args)

    /** Returns the constant as a Binder. */
    def asBinder[T1: Sort, T2: Sort, T3: Sort](using S =:= Arrow[Arrow[T1, T2], T3]): Binder[T1, T2, T3] & Constant[Arrow[Arrow[T1, T2], T3]] = 
      new Binder[T1, T2, T3](id)
  }

  /** Factory object for [[Constant]] with sort unknown at compile time.*/
  object Constant {
    /** Constructs a constant with the given identifier and sort. */
    def unsafe(id: String, sort: K.Sort): Constant[?] = Constant(id)(using unsafeSortEvidence(sort))
  }

  /** A special kind of constant of type `(A >>: B) >>: C`.
   * 
   * The binder "binds" a varible of type `A` in an expression of type `B` to produce an expression of type `C`.
   * 
   * Examples: ∀ :: (Ind >>: Prop) >>: Prop, ∃ :: (Ind >>: Prop) >>: Prop, ϵ :: (Ind >>: Prop) >>: Ind
   * 
   * @tparam S The sort of the variable
   * @tparam T The sort of the body
   * @tparam T3 The sort of the result
   */
  class Binder[S: Sort, T: Sort, T3: Sort](id: K.Identifier) extends Constant[Arrow[Arrow[S, T], T3]](id) {
    /** Binds `v` in `e`. */
    def apply(v1: Variable[S], e: Expr[T]): App[Arrow[S, T], T3] = App(this, Abs(v1, e))
    @targetName("unapplyBinder")
    /** Extract the variable and body of the binder. */
    def unapply(e: Expr[?]): Option[(Variable[S], Expr[T])] = e match {
      case App(f:Expr[Arrow[Arrow[S, T], T3]], Abs(v, e)) if f == this => Some((v, e))
      case _ => None
    }
    mkString = (args: Seq[Expr[?]]) =>
      if args.size == 0 then toString
      else args(0) match {
        case Abs(v, e) => s"$id($v, $e)${args.drop(1).map(_.mkStringSeparated).mkString}"
        case _ => defaultMkString(args)
      }
    mkStringSeparated = (args: Seq[Expr[?]]) =>
      args match {
        case Seq(Abs(v, e)) => s"($id($v, $e))"
        case _ => defaultMkStringSeparated(args)
      }
  }


  /**
    * An application of a functional expression to an argument.
    * 
    * The sorts must match: `f.sort` must be of the form `A >>: B` and `arg.sort` must be `A`.
    */
  case class App[S, T](f: Expr[Arrow[S, T]], arg: Expr[S]) extends Expr[T] {
    val sort: K.Sort = f.sort match
      case K.Arrow(from, to) if from == arg.sort => to
      case _ => throw new IllegalArgumentException("Sort mismatch. f: " + f.sort + ", arg: " + arg.sort)
    
    val underlying: K.Application = K.Application(f.underlying, arg.underlying)
    def substituteUnsafe(m: Map[Variable[?], Expr[?]]): App[S, T] = App[S, T](f.substituteUnsafe(m), arg.substituteUnsafe(m))
    override def substituteWithCheck(m: Map[Variable[?], Expr[?]]): App[S, T] =
      super.substituteWithCheck(m).asInstanceOf[App[S, T]]
    override def substitute(pairs: SubstPair*): App[S, T] = 
      super.substitute(pairs*).asInstanceOf[App[S, T]]
    def freeVars: Set[Variable[?]] = f.freeVars ++ arg.freeVars
    def freeTermVars: Set[Variable[Ind]] = f.freeTermVars ++ arg.freeTermVars
    def constants: Set[Constant[?]] = f.constants ++ arg.constants
    override def toString(): String = 
      val (f, args) = unfoldAllApp(this)
      f.mkString(args)
  }

  /** Factory object for [[App]] when the sorts are unknown at compile time. */
  object App {
    /**
      * Constructs an application of `f` to `arg`.
      * 
      * @throws IllegalArgumentException if the sorts don't match.
      */
    def unsafe(f: Expr[?], arg: Expr[?]): Expr[?] = 
      val rsort = K.legalApplication(f.sort, arg.sort)
      rsort match 
        case Some(to) => 
          App(f.asInstanceOf, arg)
        case None => throw new IllegalArgumentException(s"Cannot apply $f of sort ${f.sort} to $arg of sort ${arg.sort}")
  }


  /** A lambda abstraction of a variable over an expression.
    * 
    * The sort of the variable must match the sort of the body.
    */
  case class Abs[S, T](v: Variable[S], body: Expr[T]) extends Expr[Arrow[S, T]] {
    val sort: K.Sort = K.Arrow(v.sort, body.sort)
    val underlying: K.Lambda = K.Lambda(v.underlying, body.underlying)
    def substituteUnsafe(m: Map[Variable[?], Expr[?]]): Abs[S, T] = 
      lazy val frees = m.values.flatMap(_.freeVars).toSet
      if m.keySet.contains(v) || frees.contains(v) then
        // rename
        val v1: Variable[S] = Variable.unsafe(freshId(frees.map(_.id), v.id), v.sort).asInstanceOf
        new Abs(v1, body.substituteUnsafe(Map(v -> v1))).substituteUnsafe(m)
      else
        new Abs(v, body.substituteUnsafe(m))
    override def substituteWithCheck(m: Map[Variable[?], Expr[?]]): Abs[S, T] =
      super.substituteWithCheck(m).asInstanceOf[Abs[S, T]]
    override def substitute(pairs: SubstPair*): Abs[S, T] = 
      super.substitute(pairs*).asInstanceOf[Abs[S, T]]
    def freeVars: Set[Variable[?]] = body.freeVars - v
    def freeTermVars: Set[Variable[Ind]] = body.freeTermVars.filterNot(_ == v)
    def constants: Set[Constant[?]] = body.constants
    override def toString(): String = s"Abs($v, $body)"
  }

  /** Factory object for [[Abs]] when the sorts are unknown at compile time. */
  object Abs:
    /**
      * Constructs a lambda abstraction of `v` over `body`. Always succeeds.
      */
    def unsafe(v: Variable[?], body: Expr[?]): Expr[?] = 
      new Abs(v.asInstanceOf, body.asInstanceOf)
    
    def apply[S1, S2](v: Variable[S1], body: Expr[S2]): Abs[S1, S2] = new Abs(v, body)

    def apply(xs: Seq[Variable[?]], t: Expr[?]): Expr[?] = xs.foldRight(t)((x, t) => new Abs(x, t))

  /** Alias for [[Abs]] */
  val lambda = Abs




}




