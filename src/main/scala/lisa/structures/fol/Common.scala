package lisa.structures.fol

import lisa.kernel.fol.FOL

import scala.annotation.showAsInfix
import scala.compiletime.ops.int.-

trait Common {

  type Arity = Int & Singleton

  @showAsInfix
  type **[T, N <: Arity] <: Tuple & Matchable = N match {
    case 0 => EmptyTuple
    case _ => T *: (T ** (N - 1))
  }

  extension[T <: Matchable, N <: Arity] (tup: T ** N) {
    def toSeq: Seq[T] = tup.productIterator.toSeq.asInstanceOf
  }

  trait WithArity[N <: Arity] {
    val arity: N
  }

  def isLegalApplication(withArity: WithArity[?], args: Seq[?]): Boolean =
    withArity.arity == -1 || withArity.arity == args.size

  trait LisaObject

  trait Label{
    val underlyingLabel: FOL.Label
    val id: FOL.Identifier
  }
  trait SchematicLabel extends Label {
    override val underlyingLabel : FOL.SchematicLabel
  }
  trait ConstantLabel extends Label {
    override val underlyingLabel : FOL.ConstantLabel
  }
}
