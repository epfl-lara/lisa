package lisa.kernel.fol

/**
 * Definitions of term labels.
 */
private[fol] trait TermLabelDefinitions extends CommonDefinitions {

  /**
   * The parent class of term labels.
   * These are labels that can be applied to nodes that form the tree of a term.
   * For example, Powerset is not a term itself, it's a label for a node with a single child in a tree corresponding to a term.
   * In logical terms, those labels are essentially symbols of some language.
   */
  sealed abstract class TermLabel extends Label {
    require(arity >= 0 && arity < MaxArity)
  }

  /**
   * A fixed function symbol. If arity is 0, it is just a regular constant symbol.
   *
   * @param id    The name of the function symbol.
   * @param arity The arity of the function symbol. A function symbol of arity 0 is a constant
   */
  sealed case class ConstantFunctionLabel(id: Identifier, arity: Int) extends TermLabel with ConstantLabel

  /**
   * A schematic symbol which is uninterpreted and can be substituted by functional term of the same arity.
   * We distinguish arity 0 schematic term labels which we call variables and can be bound, and arity>1 schematic symbols.
   */
  sealed trait SchematicTermLabel extends TermLabel with SchematicLabel {}

  /**
   * A schematic function symbol that can be substituted.
   *
   * @param id    The name of the function symbol.
   * @param arity The arity of the function symbol. Must be greater than 1.
   */
  sealed case class SchematicFunctionLabel(id: Identifier, arity: Int) extends SchematicTermLabel {
    require(arity >= 1 && arity < MaxArity)
  }

  /**
   * The label of a term which is a variable. Can be bound in a formulas, or substituted for an arbitrary term.
   *
   * @param id The name of the variable, for example "x" or "y".
   */
  sealed case class VariableLabel(id: Identifier) extends SchematicTermLabel {
    val name: Identifier = id
    val arity = 0
  }

}
