package lisa.kernel.fol

/**
 * Definitions that are common to terms and formulas.
 */
private[fol] trait CommonDefinitions {
  val MaxArity: Int = 1000000

  /**
   * An object with arity information for tree-like structures.
   */
  protected trait Arity {
    val arity: Int
  }

  /**
   * An labelled node for tree-like structures.
   */
  protected trait Label[A <: Label[A]] extends Ordered[A] {
    val id: String
  }

  /**
   * Constant label can represent a symbol of a theory
   */
  trait ConstantLabel extends Label

  /**
   * Schematic label in a formula can be substituted by any constant label of the respective
   * kind (predicate or function)
   */
  trait SchematicLabel extends Label

  def freshId(taken: Set[String], base: String): String = {
    var i = 0;
    while (taken contains base + "_" + i) i += 1
    base + "_" + i
  }
}
