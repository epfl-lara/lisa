package lisa.fol

import lisa.utils.K
import lisa.utils.K.Identifier
import lisa.utils.K.given_Conversion_String_Identifier


import scala.annotation.nowarn
import scala.annotation.showAsInfix
import scala.annotation.targetName

trait Syntax {

  type IsSort[T] = Sort{type Self = T}
  

  trait T
  trait F
  trait Arrow[A: Sort, B: Sort]

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

  class SubstPair[T: Sort] private (val _1: Var[T], val _2: Expr[T])
  object SubstPair {
    def apply[T : Sort](_1: Var[T], _2: Expr[T]) = new SubstPair(_1, _2)
  }

  given [T: Sort]: Conversion[(Var[T], Expr[T]), SubstPair[T]] = s => SubstPair(s._1, s._2)


  trait LisaObject {
    def substituteUnsafe(m: Map[Var[?], Expr[?]]): LisaObject
    def substituteWithCheck(m: Map[Var[?], Expr[?]]): LisaObject = {
      if m.forall((k, v) => k.sort == v.sort) then
        substituteUnsafe(m)
      else 
        val culprit = m.find((k, v) => k.sort != v.sort).get
        throw new IllegalArgumentException("Sort mismatch in substitution: " + culprit._1 + " -> " + culprit._2)
    }
    def substitute(pairs: SubstPair[?]*): LisaObject = 
      substituteWithCheck(pairs.view.map(s => (s._1, s._2)).toMap)

    def freeVars: Set[Var[?]] 
    def freeTermVars: Set[Var[T]]
    def constants: Set[Cst[?]]
  }
  trait Expr[S: Sort] extends LisaObject {
    val sort: K.Sort = summon[IsSort[S]].underlying
    private val arity = K.flatTypeParameters(sort).size
    def underlying: K.Expression

    def substituteUnsafe(m: Map[Var[?], Expr[?]]): Expr[S]
    override def substituteWithCheck(m: Map[Var[?], Expr[?]]): Expr[S] =
      super.substituteWithCheck(m).asInstanceOf[Expr[S]]
    override def substitute(pairs: SubstPair[?]*): LisaObject = 
      super.substitute(pairs: _*).asInstanceOf[Expr[S]]

    def unapply[T1, T2](e: Expr[Arrow[T1, T2]]): Option[Expr[T1]] = e match {
      case App[T1, T2](f, arg) if f == this => Some(arg)
      case _ => None
    }
    final def defaultMkString(args: Seq[Expr[?]]): String = s"$this(${args.map(a => s"(${a})")})"
    final def defaultMkStringSeparated(args: Seq[Expr[?]]): String = s"(${defaultMkString(args)})"
    var mkString: Seq[Expr[?]] => String = defaultMkString
    var mkStringSeparated: Seq[Expr[?]] => String = defaultMkStringSeparated
  }
  
  class Multiapp(f: Expr[?]):
    def unapply (e: Expr[?]): Option[Seq[Expr[?]]] = 
      def inner(e: Expr[?]): Option[List[Expr[?]]] = e match
        case App(f2, arg) if f == f2 => Some(List(arg))
        case App(f2, arg) => inner(f2).map(arg :: _)
        case _ => None
      inner(e).map(_.reverse)
    
  

  def unfoldAllApp(e:Expr[?]): (Expr[?], List[Expr[?]]) = e match
    case App(f, arg) =>
      val (f1, args) = unfoldAllApp(f)
      (f1, arg :: args )
    case _ => (e, Nil)




  case class Var[S : Sort](id: K.Identifier) extends Expr[S] {
    val underlying: K.Variable = K.Variable(id, sort)
    def substituteUnsafe(m: Map[Var[?], Expr[?]]): Expr[S] = m.getOrElse(this, this).asInstanceOf[Expr[S]]
    override def substituteWithCheck(m: Map[Var[?], Expr[?]]): Expr[S] =
      super.substituteWithCheck(m).asInstanceOf[Expr[S]]
    override def substitute(pairs: SubstPair[?]*): Expr[S] = 
      super.substitute(pairs: _*).asInstanceOf[Expr[S]]
    def freeVars: Set[Var[?]] = Set(this)
    def freeTermVars: Set[Var[T]] = if sort == K.Term then Set(this.asInstanceOf) else Set.empty
    def constants: Set[Cst[?]] = Set.empty
    def rename(newId: K.Identifier): Var[S] = Var(newId)
    def freshRename(existing: Iterable[Expr[?]]): Var[S] = {
      val newId = K.freshId(existing.flatMap(_.freeVars.map(_.id)), id)
      Var(newId)
    }
    override def toString(): String = id.toString
    def :=(replacement: Expr[S]) = SubstPair(this, replacement)
  }

  object Var {
    def apply(id: String, sort: K.Sort): Var[?] = Var(id)(using new Sort { type Self = T; val underlying = sort })
  }


  case class Cst[S : Sort](id: K.Identifier) extends Expr[S] {
    private var infix: Boolean = false
    def setInfix(): Unit = infix = true
    val underlying: K.Constant = K.Constant(id, sort)
    def substituteUnsafe(m: Map[Var[?], Expr[?]]): Cst[S] = this
    override def substituteWithCheck(m: Map[Var[?], Expr[?]]): Expr[S] =
      super.substituteWithCheck(m).asInstanceOf[Cst[S]]
    override def substitute(pairs: SubstPair[?]*): Cst[S] = 
      super.substitute(pairs: _*).asInstanceOf[Cst[S]]
    def freeVars: Set[Var[?]] = Set.empty
    def freeTermVars: Set[Var[T]] = Set.empty
    def constants: Set[Cst[?]] = Set(this)
    def rename(newId: K.Identifier): Cst[S] = Cst(newId)
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

  object Cst {
    def apply(id: String, sort: K.Sort): Cst[?] = Cst(id)(using new Sort { type Self = T; val underlying = sort })
  }

  class Binder[T1: Sort, T2: Sort, T3: Sort](id: K.Identifier) extends Cst[Arrow[Arrow[T1, T2], T3]](id) {
    def apply(v1: Var[T1], e: Expr[T2]): App[Arrow[T1, T2], T3] = App(this, Abs(v1, e))
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


  case class App[T1 : Sort, T2 : Sort](f: Expr[Arrow[T1, T2]], arg: Expr[T1]) extends Expr[T2] {
    val underlying: K.Application = K.Application(f.underlying, arg.underlying)
    def substituteUnsafe(m: Map[Var[?], Expr[?]]): App[T1, T2] = App[T1, T2](f.substituteUnsafe(m), arg.substituteUnsafe(m))
    override def substituteWithCheck(m: Map[Var[?], Expr[?]]): App[T1, T2] =
      super.substituteWithCheck(m).asInstanceOf[App[T1, T2]]
    override def substitute(pairs: SubstPair[?]*): App[T1, T2] = 
      super.substitute(pairs: _*).asInstanceOf[App[T1, T2]]
    def freeVars: Set[Var[?]] = f.freeVars ++ arg.freeVars
    def freeTermVars: Set[Var[T]] = f.freeTermVars ++ arg.freeTermVars
    def constants: Set[Cst[?]] = f.constants ++ arg.constants
    override def toString(): String = 
      val (f, args) = unfoldAllApp(this)
      f.mkString(args)
  }

  object App {
    def apply(f: Expr[?], arg: Expr[?]): Expr[?] = 
      val rsort = K.legalApplication(f.sort, arg.sort)
      rsort match 
        case Some(to) => 
          App(f.asInstanceOf, arg.asInstanceOf)(using new Sort { type Self = T; val underlying = to }, new Sort { type Self = T; val underlying = to })
        case None => throw new IllegalArgumentException(s"Cannot apply $f of sort ${f.sort} to $arg of sort ${arg.sort}")
  }


  case class Abs[T1 : Sort, T2 : Sort](v: Var[T1], body: Expr[T2]) extends Expr[Arrow[T1, T2]] {
    val underlying: K.Lambda = K.Lambda(v.underlying, body.underlying)
    def substituteUnsafe(m: Map[Var[?], Expr[?]]): Abs[T1, T2] = Abs(v, body.substituteUnsafe(m - v))
    override def substituteWithCheck(m: Map[Var[?], Expr[?]]): Abs[T1, T2] =
      super.substituteWithCheck(m).asInstanceOf[Abs[T1, T2]]
    override def substitute(pairs: SubstPair[?]*): Abs[T1, T2] = 
      super.substitute(pairs: _*).asInstanceOf[Abs[T1, T2]]
    def freeVars: Set[Var[?]] = body.freeVars - v
    def freeTermVars: Set[Var[T]] = body.freeTermVars.filterNot(_ == v)
    def constants: Set[Cst[?]] = body.constants
    override def toString(): String = s"Abs($v, $body)"
  }


  extension [T1, T2](f: Expr[Arrow[T1, T2]]) {
    def apply(using IsSort[T1], IsSort[T2])(arg: Expr[T1]): Expr[T2] = App(f, arg)
  }




  private val x = Var[T]("x")
  private val y = Var[F]("x")
  private val z: Expr[Arrow[T, F]] = Var("x")
  z(x)



}




