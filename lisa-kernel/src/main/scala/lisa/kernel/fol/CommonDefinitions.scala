package lisa.kernel.fol

/**
 * Definitions that are common to terms and formulas.
 */
private[fol] trait CommonDefinitions {
  val MaxArity: Int = 1000000

  /**
   * A labelled node for tree-like structures.
   */
  trait Label {
    val arity: Int
    val id: Identifier
  }

  sealed case class Identifier(val name: String, val no: Int) {
    require(no >= 0, "Variable index must be positive")
    require(Identifier.isValidIdentifier(name), "Variable name " + name + "is not valid.")
    override def toString: String = if (no == 0) name else name + Identifier.counterSeparator + no
  }
  object Identifier {
    def unapply(i: Identifier): Option[(String, Int)] = Some((i.name, i.no))
    def apply(name: String): Identifier = new Identifier(name, 0)
    def apply(name: String, no: Int): Identifier = new Identifier(name, no)

    val counterSeparator: Char = '_'
    val delimiter: Char = '`'
    val forbiddenChars: Set[Char] = ("()[]{}?" + delimiter + counterSeparator).toSet
    def isValidIdentifier(s: String): Boolean = s.forall(c => !forbiddenChars.contains(c) && !c.isWhitespace)
  }

  /**
   * return am identifier that is different from a set of give identifier.
   * @param taken ids which are not available
   * @param base prefix of the new id
   * @return a fresh id.
   */
  private[kernel] def freshId(taken: Iterable[Identifier], base: Identifier): Identifier = {
    new Identifier(
      base.name,
      (taken.collect({ case Identifier(base.name, no) =>
        no
      }) ++ Iterable(base.no)).max + 1
    )
  }

  /**
   * A label for constant (non-schematic) symbols in formula and terms
   */
  trait ConstantLabel extends Label

  /**
   * A schematic label in a formula or a term can be substituted by any formula or term of the adequate kind.
   */
  trait SchematicLabel extends Label
}
