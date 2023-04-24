package lisa.structures
import leo.datastructures.TPTP.THF.Variable
import lisa.kernel.fol.FOL
import lisa.utils.KernelHelpers.{*, given}
import lisa.prooflib as PL
import lisa.settheory.SetTheoryLibrary

import scala.annotation.showAsInfix


/*given [H <: Formula, T <: Tuple](using c: FormulaSetConverter[T]): FormulaSetConverter[H *: T] with {
  override def apply(t: H *: T): Set[Formula] = c.apply(t.tail) + t.head
}

 */
object Terms {
/*
  sealed trait Type{
    val arity: Int
  }

  sealed trait Term[+T <: Type] {
  }

  sealed trait AppliableTerm[I, +O <: Type] extends Term[|->[I, O]] {

    def app(arg:I): Term[O]
  }
  @showAsInfix
  abstract class |->[I, +O <: Type] extends Type{
    val arity: Int
    def app(arg: I): O

  }





  // inline def *:[H, This >: H *: T <: Tuple](x: H): H *: This

  abstract class Object extends Type{
    val underlying : FOL.Term
    val arity: Int = 0

    def substitute2(v: Variable, t: Object): Object

    final def substitute(v:Variable, t:Object): Object = {
      val r = substitute2(v,t)
      assert(r.underlying == FOL.substituteVariables(underlying, Map((FOL.VariableLabel(v.id), t.underlying))))
      r
    }
  }

  type IsApplicable[O<:Type] = O match {
    case |->[s, t] => AppliableTerm[s, t]
    case Object => Term[O]
  }

  case class FunctionSymbol[I <: Object, +O <: Type](name: String) extends AppliableTerm[I, O] {
    def app(arg:I) : IsApplicable[O] = FunApp(this, arg)
  }

  case class FunApp[I<: Object, O <: Type](f: FunctionSymbol[I, O], arg:I) extends IsApplicable[O]{
    def apply()
  }

  FunctionSymbol[Object, |->[Object, Object]]("f").app(x).app(x)
  
  
  /*class PartiallyAppliedFunctionSymbol[I <: Object, +O <: Type](f:FunctionSymbol) extends |->[I, O] {

    
    
    
  }
  class AppliedFunctionSymbol[I <: Object, +O <: Type](f:FunctionSymbol[I, O], arg:I) extends O
*/

/*
class LambdaTerm[I <: Object, +O <: Type](val variable: Variable, val body:O) extends |->[I, O] {
  def app(arg:I):O = body.substitute2(variable, arg)

  def substitute2(v: Variable, t: Object): |->[I, O] = new LambdaTerm[I, O](variable, body.substitute2(v, t))
}

class LambdaApplication[-I<: Object, +O <: Type](lambda: LambdaTerm[I, O], arg: I) extends O {}

type Application[-I, +O <: Type, F <: |->[I, O]] <: O

*/
  trait Global //Type extends Type

  case class Variable(val id:FOL.Identifier) extends Object with Global {
    val underlying = FOL.VariableTerm(FOL.VariableLabel(id))

    override def substitute2(v: Variable, t: Object): Object = if (v.id == id) t else this
  }

  val x = Variable("x")


  abstract class SchematicSymbol

  abstract class LocalTerm(val proof: SetTheoryLibrary.Proof) extends Object {
    val properties = ???
  }
*/
}
