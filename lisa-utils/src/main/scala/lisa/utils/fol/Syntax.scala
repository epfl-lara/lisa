package lisa.fol

import lisa.utils.K
import lisa.utils.K.Identifier
import lisa.utils.K.given_Conversion_String_Identifier


import scala.annotation.nowarn
import scala.annotation.showAsInfix
import scala.annotation.targetName

trait Syntax {

  type IsSort[T] = Sort{type Self = T}

  sealed trait T
  sealed trait F
  sealed trait Arrow[A: Sort, B: Sort]

  type Formula = Expr[F]
  type Term = Expr[T]
    @showAsInfix
  infix type >>:[I, O] = (I, O) match {
    case (Expr[a], Expr[b]) => Expr[Arrow[a, b]]
  }
  
  type SortOf[T] = T match {
    case Expr[t] => t
  }

  trait Sort {
    type Self
    val underlying: K.Sort
  }
  given given_TermType:  IsSort[T] with
    val underlying = K.Term
  given given_FormulaType: IsSort[F] with
    val underlying = K.Formula
  given given_ArrowType[A : Sort as ta, B : Sort as tb]: (IsSort[Arrow[A, B]]) with
    val underlying = K.Arrow(ta.underlying, tb.underlying)

  sealed trait SubstPair extends Product {
    type S
    val _1: Variable[S]
    val _2: Expr[S]
  }
  private case class ConcreteSubstPair[S1] (_1: Variable[S1], _2: Expr[S1]) extends SubstPair {type S = S1}
  object SubstPair {
    def apply[S1 : Sort](_1: Variable[S1], _2: Expr[S1]): SubstPair {type S = S1} = new ConcreteSubstPair[S1](_1, _2)
    def unapply[S1](s: SubstPair{type S = S1}): SubstPair{type S = S1} = s
  }

  def unsafeSortEvidence[S](sort: K.Sort) : IsSort[S] = new Sort { type Self = S; val underlying = sort }

  given [T: Sort]: Conversion[(Variable[T], Expr[T]), SubstPair{type S = T}] = s => SubstPair(s._1, s._2)


  type ArgsTo[S1, Target] <: NonEmptyTuple = S1 match {
    case Arrow[a, Target] => Tuple1[Expr[a]]
    case Arrow[a, b] => Expr[a] *: ArgsTo[b, Target]
  }


  trait LisaObject {
    def substituteUnsafe(m: Map[Variable[?], Expr[?]]): LisaObject
    def substituteWithCheck(m: Map[Variable[?], Expr[?]]): LisaObject = {
      if m.forall((k, v) => k.sort == v.sort) then
        substituteUnsafe(m)
      else 
        val culprit = m.find((k, v) => k.sort != v.sort).get
        throw new IllegalArgumentException("Sort mismatch in substitution: " + culprit._1 + " -> " + culprit._2)
    }
    def substitute(pairs: SubstPair*): LisaObject = 
      substituteWithCheck(pairs.view.map(s => (s._1, s._2)).toMap)

    def freeVars: Set[Variable[?]] 
    def freeTermVars: Set[Variable[T]]
    def constants: Set[Constant[?]]
  }
  sealed trait Expr[S] extends LisaObject {
    val sort: K.Sort
    private val arity = K.flatTypeParameters(sort).size
    def underlying: K.Expression

    def substituteUnsafe(m: Map[Variable[?], Expr[?]]): Expr[S]
    override def substituteWithCheck(m: Map[Variable[?], Expr[?]]): Expr[S] =
      super.substituteWithCheck(m).asInstanceOf[Expr[S]]
    override def substitute(pairs: SubstPair*): Expr[S] = 
      super.substitute(pairs*).asInstanceOf[Expr[S]]

    def unapplySeq[Target](e: Expr[Target]): Option[ArgsTo[S, Target]] = 
      def inner[Target](e: Expr[Target]): Option[ArgsTo[S, Target]] = e match
        case App(f2, arg) if this == f2 => Some((arg *: EmptyTuple).asInstanceOf[ArgsTo[S, Target]])
        case App(f2, arg) => inner(f2).map(value => (arg *: value).asInstanceOf[ArgsTo[S, Target]])
        case _ => None
      inner[Target](e)

    @targetName("unapplySeq2")
    def unapplySeq(e: Expr[?]): Option[Seq[Expr[?]]] = Multiapp(this).unapply(e)


    /*
    @targetName("unapply2")
    def unapply[T1, T2, T3](e: Expr[T3]): Option[(Expr[T1], Expr[T2])] = (e: @unchecked) match 
      case App[T2, T3](e1, a2) => e1 match 
        case App[T1, T2 >>: T3](f, a1) if f == this => Some((a1, a2))
        case _ => None
      case _ => None
        
    @targetName("unapply1")  
    def unapply[T1, T2](e: Expr[T2]): Option[Expr[T1]] = (e: @unchecked) match {
      case App[T1, T2](f, arg)  if f == this => Some(arg)
      case _ => None
    }
      */
    final def defaultMkString(args: Seq[Expr[?]]): String = s"$this(${args.map(a => s"(${a})")})"
    final def defaultMkStringSeparated(args: Seq[Expr[?]]): String = s"(${defaultMkString(args)})"
    var mkString: Seq[Expr[?]] => String = defaultMkString
    var mkStringSeparated: Seq[Expr[?]] => String = defaultMkStringSeparated


    def #@(arg: Expr[?]): RetExpr[S] = 
      App.unsafe(this, arg).asInstanceOf

    def #@@(args: Seq[Expr[?]]): Expr[?] = 
      Multiapp.unsafe(this, args)

    def structuralToString: String = this match
      case Variable(id) => s"Variable($id, $sort)"
      case Constant(id) => s"Constant($id, $sort)"
      case App(f, arg) => s"App(${f.structuralToString}, ${arg.structuralToString})"
      case Abs(v, body) => s"Abs(${v.structuralToString}, ${body.structuralToString})"
    
  }
  object #@ {
    def unapply[T1, T2](e: Expr[T2]): Option[(Expr[Arrow[T1, T2]], Expr[T1])] = (e: @unchecked) match
      case App[T1, T2](f, arg) => Some((f, arg))
      case _ => None
  }

  extension [T1, T2](f: Expr[Arrow[T1, T2]]) 
    def apply(using IsSort[T1], IsSort[T2])(arg: Expr[T1]): Expr[T2] = App(f, arg)


  type RetExpr[T] <: Expr[?] = T match {
    case Arrow[a, b] => Expr[b]
  }

  class Multiapp(f: Expr[?]):
    def unapply (e: Expr[?]): Option[Seq[Expr[?]]] = 
      def inner(e: Expr[?]): Option[List[Expr[?]]] = e match
        case App(f2, arg) if f == f2 => Some(List(arg))
        case App(f2, arg) => inner(f2).map(arg :: _)
        case _ => None
      inner(e).map(_.reverse)

  object Multiapp:
    def unsafe(f: Expr[?], args: Seq[Expr[?]]): Expr[?] = 
      args.foldLeft(f)((f, arg) => App.unsafe(f, arg))
    def unapply(e: Expr[?]): Some[(Expr[?], Seq[Expr[?]])] = Some(unfoldAllApp(e))
  
  


  def unfoldAllApp(e:Expr[?]): (Expr[?], List[Expr[?]]) = 
    def rec(e: Expr[?]): (Expr[?], List[Expr[?]]) = e match
      case App(f, arg) =>
        val (f1, args) = unfoldAllApp(f)
        (f1, arg :: args )
      case _ => (e, Nil)
    val (f, args) = rec(e)
    (f, args.reverse)




  case class Variable[S : Sort as sortEv](id: K.Identifier) extends Expr[S] {
    val sort: K.Sort = sortEv.underlying
    val underlying: K.Variable = K.Variable(id, sort)
    def substituteUnsafe(m: Map[Variable[?], Expr[?]]): Expr[S] = m.getOrElse(this, this).asInstanceOf[Expr[S]]
    override def substituteWithCheck(m: Map[Variable[?], Expr[?]]): Expr[S] =
      super.substituteWithCheck(m).asInstanceOf[Expr[S]]
    override def substitute(pairs: SubstPair*): Expr[S] = 
      super.substitute(pairs*).asInstanceOf[Expr[S]]
    def freeVars: Set[Variable[?]] = Set(this)
    def freeTermVars: Set[Variable[T]] = if sort == K.Term then Set(this.asInstanceOf) else Set.empty
    def constants: Set[Constant[?]] = Set.empty
    def rename(newId: K.Identifier): Variable[S] = Variable(newId)
    def freshRename(existing: Iterable[Expr[?]]): Variable[S] = {
      val newId = K.freshId(existing.flatMap(_.freeVars.map(_.id)), id)
      Variable(newId)
    }
    override def toString(): String = id.toString
    def :=(replacement: Expr[S]) = SubstPair(this, replacement)
  }

  object Variable {
    def unsafe(id: String, sort: K.Sort): Variable[?] = Variable(id)(using unsafeSortEvidence(sort))
  }


  case class Constant[S : Sort as sortEv](id: K.Identifier) extends Expr[S] {
    val sort: K.Sort = sortEv.underlying
    private var infix: Boolean = false
    def setInfix(): Unit = infix = true
    val underlying: K.Constant = K.Constant(id, sort)
    def substituteUnsafe(m: Map[Variable[?], Expr[?]]): Constant[S] = this
    override def substituteWithCheck(m: Map[Variable[?], Expr[?]]): Expr[S] =
      super.substituteWithCheck(m).asInstanceOf[Constant[S]]
    override def substitute(pairs: SubstPair*): Constant[S] = 
      super.substitute(pairs*).asInstanceOf[Constant[S]]
    def freeVars: Set[Variable[?]] = Set.empty
    def freeTermVars: Set[Variable[T]] = Set.empty
    def constants: Set[Constant[?]] = Set(this)
    def rename(newId: K.Identifier): Constant[S] = Constant(newId)
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
  }

  object Constant {
    def unsafe(id: String, sort: K.Sort): Constant[?] = Constant(id)(using unsafeSortEvidence(sort))
  }

  class Binder[T1: Sort, T2: Sort, T3: Sort](id: K.Identifier) extends Constant[Arrow[Arrow[T1, T2], T3]](id) {
    def apply(v1: Variable[T1], e: Expr[T2]): App[Arrow[T1, T2], T3] = App(this, Abs(v1, e))
    @targetName("unapplyBinder")
    def unapply(e: Expr[T3]): Option[(Variable[T1], Expr[T2])] = e match {
      case App(f:Expr[Arrow[Arrow[T1, T2], T3]], Abs(v, e)) if f == this => Some((v, e))
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


  case class App[T1, T2](f: Expr[Arrow[T1, T2]], arg: Expr[T1]) extends Expr[T2] {
    val sort: K.Sort = f.sort match
      case K.Arrow(from, to) if from == arg.sort => to
      case _ => throw new IllegalArgumentException("Sort mismatch. f: " + f.sort + ", arg: " + arg.sort)
    
    val underlying: K.Application = K.Application(f.underlying, arg.underlying)
    def substituteUnsafe(m: Map[Variable[?], Expr[?]]): App[T1, T2] = App[T1, T2](f.substituteUnsafe(m), arg.substituteUnsafe(m))
    override def substituteWithCheck(m: Map[Variable[?], Expr[?]]): App[T1, T2] =
      super.substituteWithCheck(m).asInstanceOf[App[T1, T2]]
    override def substitute(pairs: SubstPair*): App[T1, T2] = 
      super.substitute(pairs*).asInstanceOf[App[T1, T2]]
    def freeVars: Set[Variable[?]] = f.freeVars ++ arg.freeVars
    def freeTermVars: Set[Variable[T]] = f.freeTermVars ++ arg.freeTermVars
    def constants: Set[Constant[?]] = f.constants ++ arg.constants
    override def toString(): String = 
      val (f, args) = unfoldAllApp(this)
      f.mkString(args)
  }

  object App {
    def unsafe(f: Expr[?], arg: Expr[?]): Expr[?] = 
      val rsort = K.legalApplication(f.sort, arg.sort)
      rsort match 
        case Some(to) => 
          App(f.asInstanceOf, arg)
        case None => throw new IllegalArgumentException(s"Cannot apply $f of sort ${f.sort} to $arg of sort ${arg.sort}")
  }


  case class Abs[T1, T2](v: Variable[T1], body: Expr[T2]) extends Expr[Arrow[T1, T2]] {
    val sort: K.Sort = K.Arrow(v.sort, body.sort)
    val underlying: K.Lambda = K.Lambda(v.underlying, body.underlying)
    def substituteUnsafe(m: Map[Variable[?], Expr[?]]): Abs[T1, T2] = Abs(v, body.substituteUnsafe(m - v))
    override def substituteWithCheck(m: Map[Variable[?], Expr[?]]): Abs[T1, T2] =
      super.substituteWithCheck(m).asInstanceOf[Abs[T1, T2]]
    override def substitute(pairs: SubstPair*): Abs[T1, T2] = 
      super.substitute(pairs*).asInstanceOf[Abs[T1, T2]]
    def freeVars: Set[Variable[?]] = body.freeVars - v
    def freeTermVars: Set[Variable[T]] = body.freeTermVars.filterNot(_ == v)
    def constants: Set[Constant[?]] = body.constants
    override def toString(): String = s"Abs($v, $body)"
  }

  object Abs {
    def unsafe(v: Variable[?], body: Expr[?]): Expr[?] = 
      Abs(v.asInstanceOf, body.asInstanceOf)
  }




}




