package lisa.kernel.fol

/**
 * Definitions that are common to terms and formulas.
 */
private[fol] trait CommonDefinitions {
  val MaxArity: Int = 1000000

  /**
   * A labelled node for tree-like structures.
   */
  protected trait Label {
    val arity: Int
    val id: String
  }

  /**
   * A constant label can represent a fixed symbol of a theory or a logical symbol
   */
  trait ConstantLabel extends Label

  /**
   * A schematic label in a formula or a term can be substituted by any formula or term of the adequate kind.
   */
  trait SchematicLabel extends Label

  /**
   * return am identifier that is different from a set of give identifier.
   * @param taken ids which are not available
   * @param base prefix of the new id
   * @return a fresh id.
   */
  def freshId(taken: Set[String], base: String): String = {
    var i = 0;
    while (taken contains base + "_" + i) i += 1
    base + "_" + i
  }
}
