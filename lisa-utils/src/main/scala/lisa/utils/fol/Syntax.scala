package lisa.fol

import lisa.utils.K
import lisa.utils.K.Identifier
import lisa.utils.K.given_Conversion_String_Identifier


import scala.annotation.nowarn
import scala.annotation.showAsInfix
import scala.annotation.targetName

trait Syntax {
  







  object First {
    trait T
    trait F
    trait Arrow[A: Type, B: Type]

    trait Type {
      type Self
      val underlying: K.Type
    }
    given given_TermType:  (Type{type Self = T}) with
      val underlying = K.Term
    given given_FormulaType: (Type{type Self = F}) with
      val underlying = K.Formula
    given given_ArrowType[A : Type, B : Type]: (Type{type Self = Arrow[A, B]}) with
      val underlying = K.Arrow(summon[Type{type Self = A}].underlying, summon[Type{type Self = B}].underlying)

    class SubstPair[T: Type] private (val _1: Var[T], val _2: Expr[T]) {
      // def toTuple = (_1, _2)
    }
    object SubstPair {
      def apply[T : Type](_1: Var[T], _2: Expr[T]) = new SubstPair(_1, _2)
    }

    given [T: Type]: Conversion[(Var[T], Expr[T]), SubstPair[T]] = s => SubstPair(s._1, s._2)


    trait Expr[S : Type] {
      val typ: K.Type = summon[Type{type Self = S}].underlying
      def underlying: K.Expression
      def substUnsafe(m: Map[Var[?], Expr[?]]): Expr[S]
      def substituteWithCheck(m: Map[Var[?], Expr[?]]): Expr[S] = {
        if m.forall((k, v) => k.typ == v.typ) then
          substUnsafe(m)
        else 
          val culprit = m.find((k, v) => k.typ != v.typ).get
          throw new IllegalArgumentException("Type mismatch in substitution: " + culprit._1 + " -> " + culprit._2)
      }
      def substitute(pairs: SubstPair[?]*): Expr[S] = 
        substituteWithCheck(pairs.view.map(s => (s._1, s._2)).toMap)

      def freeVars: Set[Var[?]] 
      def freeTermVars: Set[Var[T]]
    }


    type Formula = Expr[F]
    type Term = Expr[T]

    case class Var[S : Type](id: K.Identifier) extends Expr[S] {
      val underlying: K.Variable = K.Variable(id, typ)
      def substUnsafe(m: Map[Var[?], Expr[?]]): Expr[S] = m.getOrElse(this, this).asInstanceOf[Expr[S]]
      def freeVars: Set[Var[?]] = Set(this)
      def freeTermVars: Set[Var[T]] = if typ == K.Term then Set(this.asInstanceOf) else Set.empty
      def rename(newId: K.Identifier): Var[S] = Var(newId)
      def freshRename(existing: Iterable[Expr[?]]): Var[S] = {
        val newId = K.freshId(existing.flatMap(_.freeVars.map(_.id)), id)
        Var(newId)
      }

      def :=(replacement: Expr[S]) = SubstPair(this, replacement)
    }
    case class Cst[S : Type](id: K.Identifier) extends Expr[S] {
      val underlying: K.Constant = K.Constant(id, typ)
      def substUnsafe(m: Map[Var[?], Expr[?]]): Cst[S] = this
      def freeVars: Set[Var[?]] = Set.empty
      def freeTermVars: Set[Var[T]] = Set.empty
      def rename(newId: K.Identifier): Cst[S] = Cst(newId)
    }
    case class App[T1 : Type, T2 : Type](f: Expr[Arrow[T1, T2]], arg: Expr[T1]) extends Expr[T2] {
      val underlying: K.Application = K.Application(f.underlying, arg.underlying)
      def substUnsafe(m: Map[Var[?], Expr[?]]): App[T1, T2] = App(f.substUnsafe(m), arg.substUnsafe(m))
      def freeVars: Set[Var[?]] = f.freeVars ++ arg.freeVars
      def freeTermVars: Set[Var[T]] = f.freeTermVars ++ arg.freeTermVars
    }
    case class Abs[T1 : Type, T2 : Type](v: Var[T1], body: Expr[T2]) extends Expr[Arrow[T1, T2]] {
      val underlying: K.Lambda = K.Lambda(v.underlying, body.underlying)
      def substUnsafe(m: Map[Var[?], Expr[?]]): Abs[T1, T2] = Abs(v, body.substUnsafe(m - v))
      def freeVars: Set[Var[?]] = body.freeVars - v
      def freeTermVars: Set[Var[T]] = body.freeTermVars.filterNot(_ == v)
    }

    extension [T1 : Type, T2 : Type](f: Expr[Arrow[T1, T2]]) {
      def apply(arg: Expr[T1]): Expr[T2] = App(f, arg)
    }


    val x = Var[T]("x")
    val y: Expr[F] = Var("x")
    val z: Expr[Arrow[T, F]] = Var("x")
    z(x)


    @showAsInfix
    infix type |->[I, O] = (I, O) match {
      case (Expr[T], Expr[F]) => Expr[Arrow[T, F]]
    }
  }

  object FirstTest {
    import First._

    val x1: Term = Var("x")
    val y1: Formula	= Var("y")
    val z1: (Term |-> Formula) = Var("z")
  }




  object Third {
    trait Expr {
      val typ: K.Type
    }


    opaque type Term <: Expr = Expr
    opaque type Formula <: Expr = Expr
    opaque type |->[A, B] <: Expr = Expr

    sealed trait Type {
      type Self <: Expr 
      val underlying: K.Type
      val isExpr: (Expr =:= Self)
    }
    given (Term is Type) with
      val underlying = K.Term
      val isExpr = summon[Expr =:= Term]
    given (Formula is Type) with
      val underlying = K.Formula
      val isExpr = summon[Expr =:= Formula]
    given [A : Type, B : Type]: ((|->[A, B]) is Type) with
      val underlying = K.Arrow(summon[Type{type Self = A}].underlying, summon[Type{type Self = B}].underlying)
      val isExpr = summon[Expr =:= |->[A, B]]


    case class Var(id: K.Identifier, typ: K.Type) extends Expr
    object Var {
      def apply[T: Type](id: String): Var & T = 
        val evT = summon[Type{type Self = T}]
        (new Var(id, evT.underlying)).asInstanceOf
    }
    case class Cst(id: K.Identifier, typ: K.Type) extends Expr
    case class App(f: Expr, arg: Expr, typ: K.Type) extends Expr
    case class Abs(v: Var, body: Expr, typ: K.Type) extends Expr

  }


  object Fourth {

    trait Expr[T <: Expr[T]] {
      val typ: K.Type
    }

    /*
    opaque type Term <: Expr[?] = Expr[?]
    opaque type Formula <: Expr[?] = Expr[?]
    opaque type |->[A, B] <: Expr[?] = Expr[?]
*/

    sealed trait Term extends Expr[Term] {
    }
    sealed trait Formula extends Expr[Formula] {
    }
    sealed trait |->[A, B] extends Expr[|->[A, B]] {
    }

    sealed trait Type {
      type Self <: Expr[?]
      val underlying: K.Type
    }
    given (Term is Type) with
      val underlying = K.Term
    given (Formula is Type) with
      val underlying = K.Formula
    given [A : Type, B : Type]: ((|->[A, B]) is Type) with
      val underlying = K.Arrow(summon[Type{type Self = A}].underlying, summon[Type{type Self = B}].underlying)

    case class Var[T<: Expr[T]](id: K.Identifier, typ: K.Type) extends Expr[T]
    object Var {
      def apply[T <: Expr[T] : Type](id: String): Var[T] = 
        val evT = summon[Type{type Self = T}]
        (new Var(id, evT.underlying)).asInstanceOf
    }



  }

  object FourthTest {
    import Fourth._

    val x: Var[Term] = Var("x")
    val y: Var[Formula] = Var("y")
    val z: Var[ |->[Term, Formula]] = Var("z")
  }


}




