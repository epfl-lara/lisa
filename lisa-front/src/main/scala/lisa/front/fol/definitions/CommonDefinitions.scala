package lisa.front.fol.definitions

trait CommonDefinitions {

  /**
   * The label of a node.
   */
  private[fol] trait Label {
    val id: String
  }
  /**
   * A label node that is considered schematic (namely one that can be instantiated).
   */
  private[fol] trait SchematicLabel extends Label

  /**
   * A labeled tree.
   * @tparam A the label of that tree
   */
  private[fol] trait LabeledTree[A <: Label] {
    val label: A
  }

  /**
   * Statically typed arity.
   */
  type Arity = Int & Singleton

  /**
   * A node with arity.
   * @tparam N the arity as a static type, or `?` if unknown
   */
  private[fol] trait WithArity[N <: Arity] {
    val arity: N
  }
  
  private[fol] def isLegalApplication(withArity: WithArity[?], args: Seq[?]): Boolean =
    withArity.arity == -1 || withArity.arity == args.size

}
