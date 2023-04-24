package lisa.structures

import lisa.kernel.fol.FOL
import lisa.prooflib as PL
import lisa.settheory.SetTheoryLibrary
import lisa.utils.KernelHelpers.{*, given}

import scala.annotation.showAsInfix
import scala.compiletime.ops.int.-
import scala.Tuple.*

/*given [H <: Formula, T <: Tuple](using c: FormulaSetConverter[T]): FormulaSetConverter[H *: T] with {
  override def apply(t: H *: T): Set[Formula] = c.apply(t.tail) + t.head
}

 */
object Terms2 {

  type Arity = Int & Singleton

  @showAsInfix
  type **[T, N <: Arity] <: Tuple & Matchable = N match {
    case 0 => EmptyTuple
    case _ => T *: (T ** (N - 1))
  }


  sealed trait TermConstructor{
  }

  @showAsInfix
  abstract class |->[I, +O <: Term] extends TermConstructor{
    def app(arg: I): O

  }

  extension[T <: Matchable, N<:Arity](tup:T**N) {
    /*
    def map2[U <: Matchable](f:T=>U): U**N = tup match {
      case e:EmptyTuple => EmptyTuple.asInstanceOf
      case head*:tail => f(head)*:tail.asInstanceOf[T**(N-1)].map2(f).asInstanceOf
    }*/

    def toSeq: Seq[T] = tup.productIterator.toSeq.asInstanceOf
  }



  // inline def *:[H, This >: H *: T <: Tuple](x: H): H *: This

  abstract class Term {
    val underlying : FOL.Term
    val arity: Int = 0

    def substitute2(v: Variable, t: Term): Term

    final def substitute(v:Variable, t:Term): Term = {
      val r = substitute2(v,t)
      assert(r.underlying == FOL.substituteVariables(underlying, Map((FOL.VariableLabel(v.id), t.underlying))))
      r
    }

    //inline def *=>[H, This >: H *: T <: Tuple](x: H): TermLikeFunction[This, ] // H *: This

    //def *=>(TermLikeFunction) : TermLikeFunction
  }

  case class FunctionSymbol[T<:Tuple, A >: Union[T] <: Term](id:FOL.Identifier, defined:Boolean)(using val arity: Size[T]) extends |->[T, Term] {
    val underlying: FOL.TermLabel = if (defined) FOL.ConstantFunctionLabel(id, arity) else FOL.SchematicFunctionLabel(id, arity)
    def app(arg: T): AppliedFunctionSymbol[T, A] = AppliedFunctionSymbol[T, A](this, arg)
  }

  case class AppliedFunctionSymbol[T<:Tuple, A >: Union[T] <: Term](f:FunctionSymbol[T, A], arg:T) extends Term{
    override val underlying = FOL.Term(f.underlying, arg.toSeq.map(_.underlying))
    override def substitute2(v: Variable, t: Term) = AppliedFunctionSymbol[T, A](f, arg.map2(_.substitute2(v,t)))
  }


/*
class LambdaTerm[I <: Term, +O <: TermLike](val variable: Variable, val body:O) extends |->[I, O] {
  def app(arg:I):O = body.substitute2(variable, arg)

  def substitute2(v: Variable, t: Term): |->[I, O] = new LambdaTerm[I, O](variable, body.substitute2(v, t))
}

class LambdaApplication[-I<: Term, +O <: TermLike](lambda: LambdaTerm[I, O], arg: I) extends O {}

type Application[-I, +O <: TermLike, F <: |->[I, O]] <: O

*/
  trait Global //TermLike extends TermLike

  class Variable(val id:FOL.Identifier) extends Term with Global {
    val underlying = FOL.VariableTerm(FOL.VariableLabel(id))

    override def substitute2(v: Variable, t: Term): Term = if (v.id == id) t else this
  }




  abstract class SchematicSymbol

  abstract class LocalTerm(val proof: SetTheoryLibrary.Proof) extends Term {
    val properties = ???
  }

}
