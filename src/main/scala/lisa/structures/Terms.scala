package lisa.structures
import lisa.kernel.fol.FOL
import lisa.utils.KernelHelpers as KH
import lisa.prooflib as PL
import lisa.settheory.SetTheoryLibrary

import scala.annotation.showAsInfix


/*given [H <: Formula, T <: Tuple](using c: FormulaSetConverter[T]): FormulaSetConverter[H *: T] with {
  override def apply(t: H *: T): Set[Formula] = c.apply(t.tail) + t.head
}

 */
object Terms {
  abstract class TermLike {
    val arity: Int
  }

  // inline def *:[H, This >: H *: T <: Tuple](x: H): H *: This

  abstract class Term extends TermLike{
    val underlying : FOL.Term
    val arity: Int = 0

    protected def substitute2(v: Variable, t: Term): Term

    final def substitute(v:Variable, t:Term): Unit = {
      val r = substitute2(v,t)
      assert(r.underlying == FOL.substituteVariables(underlying, Map((FOL.VariableLabel(v.id), t.underlying))))
    }

    //inline def *=>[H, This >: H *: T <: Tuple](x: H): TermLikeFunction[This, ] // H *: This

    //def *=>(TermLikeFunction) : TermLikeFunction
  }

  //sealed abstract class *:[+H, +T <: Tuple] extends NonEmptyTuple



  @showAsInfix
  abstract class |->[-I, +O <: TermLike] {
    def app(arg:I):O
  }
  class LambdaTerm[+O <: TermLike](val variable: Variable, body:O) extends |->[Term, O] {
    def app(arg:Term):O = ???
  }

  type Application[-I, +O <: TermLike, F <: |->[I, O]] <: O


  trait Global //TermLike extends TermLike

  class Variable(val id:FOL.Identifier) extends Term with Global {
    val underlying = FOL.VariableTerm(FOL.VariableLabel(id))

    override def substitute2(v: Variable, t: Term) = if (v.id == id) t else this
  }




  abstract class SchematicSymbol

  abstract class LocalTerm(val proof: SetTheoryLibrary.Proof) extends Term {
    val properties = ???
  }

}
