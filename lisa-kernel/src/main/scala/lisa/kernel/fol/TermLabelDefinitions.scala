package lisa.kernel.fol

/**
 * Definitions of term labels.
 */
private[fol] trait TermLabelDefinitions extends CommonDefinitions {

  /**
   * The parent class of term labels.
   * These are labels that can be applied to nodes that form the tree of a term.
   * For example, Powerset is not a term itself, it's a label for a node with a single child in a tree corresponding to a term.
   * In logical terms, those labels are essentially symbols of sme language.
   */
  sealed abstract class TermLabel extends Label with Ordered[TermLabel] {
    def priority: Int = this match {
      case _: VariableLabel => 1
      case _: ConstantFunctionLabel => 2
      case _: SchematicFunctionLabel => 3
    }

    /**
     * Sorts labels according to first whether the term is a variable or function, then according to arity, then to the id.
     */
    def compare(that: TermLabel): Int = (this, that) match {
      case (thi: VariableLabel, tha: VariableLabel) => thi.id compare tha.id
      case (thi: ConstantFunctionLabel, tha: ConstantFunctionLabel) => (2 * (thi.arity compare tha.arity) + (thi.id compare tha.id)).sign
      case (thi: SchematicFunctionLabel, tha: SchematicFunctionLabel) => (2 * (thi.arity compare tha.arity) + (thi.id compare tha.id)).sign
      case _ => this.priority - that.priority
    }
  }

  /**
   * The label of a function-like term. Constants are functions of arity 0.
   * There are two kinds of function symbols: Standards and schematic.
   * Standard function symbols denote a particular function. Schematic function symbols
   * can be instantiated with any term. This is particularly useful to express axiom schemas.
   */
  sealed abstract class FunctionLabel extends TermLabel with Arity {
    require(arity >= 0 && arity < MaxArity)
  }

  /**
   * A function symbol.
   *
   * @param id    The name of the function symbol.
   * @param arity The arity of the function symbol. A function symbol of arity 0 is a constant
   */
  sealed case class ConstantFunctionLabel(id: String, arity: Int) extends FunctionLabel with ConstantLabel

  sealed trait SchematicTermLabel extends TermLabel {}

  /**
   * A schematic function symbol that can be substituted.
   *
   * @param id    The name of the function symbol.
   * @param arity The arity of the function symbol. A function symbol of arity 0 is a constant
   */
  sealed case class SchematicFunctionLabel(id: String, arity: Int) extends FunctionLabel with SchematicTermLabel {
    require(arity >= 1 && arity < MaxArity)
  }

  /**
   * The label of a term which is a variable.
   *
   * @param id The name of the variable, for example "x" or "y".
   */
  sealed case class VariableLabel(id: String) extends SchematicTermLabel {
    val name: String = id
    val arity = 0
  }

  /**
   * A function returning true if and only if the two symbols are considered "the same".
   */
  def isSame(l: TermLabel, r: TermLabel): Boolean = (l compare r) == 0
}
