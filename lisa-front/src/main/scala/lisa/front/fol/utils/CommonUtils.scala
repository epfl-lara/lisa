package lisa.front.fol.utils

import lisa.front.fol.definitions.CommonDefinitions
import lisa.front.fol.ops.CommonOps

import scala.annotation.targetName

trait CommonUtils extends CommonDefinitions with CommonOps {

  /**
   * Creates a fresh id with respect to a set of taken ids. A base id can optionally be specified.
   * @param taken the set of taken ids
   * @param base an optional base id
   * @return a fresh id
   */
  def freshId(taken: Set[String], base: String = "x"): String = {
    def findFirst(i: Int): String = {
      val id = s"${base}_$i"
      if(taken.contains(id)) findFirst(i + 1) else id
    }
    findFirst(0)
  }

  /**
   * Creates a sequence of fresh ids with respect to a set of taken ids. A base id can optionally be specified.
   * @param taken the set of taken ids
   * @param base an optional base id
   * @return a sequent of fresh ids
   */
  def freshIds(taken: Set[String], n: Int, base: String = "x"): Seq[String] = {
    require(n >= 0)
    def findMany(i: Int, n: Int, taken: Set[String], acc: Seq[String]): Seq[String] = {
      if(n > 0) {
        val id = s"${base}_$i"
        if(taken.contains(id)) findMany(i + 1, n, taken, acc) else findMany(i + 1, n - 1, taken + id, id +: acc)
      } else {
        acc
      }
    }
    findMany(0, n, taken, Seq.empty).reverse
  }

  /**
   * Represents the renaming of a label.
   * @param from the label that should be renamed
   * @param to the label it should be renamed to
   */
  case class RenamedLabel[L <: Label & WithArity[?], A <: L & SchematicLabel, B <: L] private(from: A, to: B)
  object RenamedLabel {
    @targetName("applySafe")
    def apply[N <: Arity, L <: Label & WithArity[N], A <: L & SchematicLabel, B <: L](from: A, to: B): RenamedLabel[L, A, B] = new RenamedLabel(from, to)
    def unsafe[L <: Label & WithArity[?], A <: L & SchematicLabel, B <: L](from: A, to: B): RenamedLabel[L, A, B] = new RenamedLabel(from, to)
  }
  extension [L <: Label & WithArity[?], A <: L & SchematicLabel](renamed: RenamedLabel[L, A, A]) {
    def swap: RenamedLabel[L, A, A] = RenamedLabel.unsafe(renamed.to, renamed.from)
  }

  /**
   * A lambda definition, namely an anonymous function taking some arguments and returning a result.
   * Arguments are represented as holes, thus the body of the function is known at runtime.
   */
  protected abstract class LambdaDefinition[N <: Arity, S <: SchematicLabel & WithArity[?], T <: LabeledTree[?]] extends WithArity[N] {
    type U <: LabeledTree[? >: S]

    val parameters: Seq[S]
    val body: T

    def apply(args: FillArgs[U, N]): T = unsafe(args.toSeq)
    def unsafe(args: Seq[U]): T = {
      require(args.size == arity)
      instantiate(args)
    }
    protected def instantiate(args: Seq[U]): T

    override val arity: N = parameters.size.asInstanceOf[N]

    require(parameters.forall(_.arity == 0))
    require(parameters.distinct.size == parameters.size)
  }

  /**
   * Represents the instantiation of a schema.
   */
  protected abstract class AssignedSchema[R <: SchematicLabel & WithArity[?], S <: SchematicLabel & WithArity[?]] {
    type L <: LambdaDefinition[?, S, ? <: LabeledTree[? >: R]]

    val schema: R
    val lambda: L

    require(schema.arity == lambda.arity)
  }

}
