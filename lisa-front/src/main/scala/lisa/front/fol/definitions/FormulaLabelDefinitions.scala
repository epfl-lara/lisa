package lisa.front.fol.definitions

trait FormulaLabelDefinitions extends CommonDefinitions {

  /** @see [[lisa.kernel.fol.FOL.FormulaLabel]] */
  sealed abstract class FormulaLabel extends Label

  /** @see [[lisa.kernel.fol.FOL.PredicateLabel]] */
  sealed abstract class PredicateLabel[N <: Arity] extends FormulaLabel with WithArity[N]
  /** @see [[lisa.kernel.fol.FOL.ConstantPredicateLabel]] */
  final case class ConstantPredicateLabel[N <: Arity] protected(id: String, arity: N) extends PredicateLabel[N]
  /** @see [[lisa.kernel.fol.FOL.SchematicFormulaLabel]] */
  final case class SchematicPredicateLabel[N <: Arity] protected(id: String, arity: N) extends PredicateLabel[N] with SchematicLabel

  object ConstantPredicateLabel {
    def apply[N <: Arity](id: String)(using v: ValueOf[N]): ConstantPredicateLabel[N] = ConstantPredicateLabel(id, v.value)
    def unsafe(id: String, arity: Int): ConstantPredicateLabel[?] = ConstantPredicateLabel(id, arity)
  }
  object SchematicPredicateLabel {
    def apply[N <: Arity](id: String)(using v: ValueOf[N]): SchematicPredicateLabel[N] = SchematicPredicateLabel(id, v.value)
    def unsafe(id: String, arity: Int): SchematicPredicateLabel[?] = SchematicPredicateLabel(id, arity)
  }

  /** @see [[lisa.kernel.fol.FOL.equality]] */
  val equality: ConstantPredicateLabel[2] = ConstantPredicateLabel("=")

  /**
   * For completeness, the front provides constant & schematic connectors.
   * The kernel only supports constant such labels. The compromise is to only work with those in the front and avoid
   * translating them into the kernel.
   * @see [[PredicateLabel]]
   * @see [[TermLabelDefinitions.TermLabel]]
   */
  sealed abstract class ConnectorLabel[N <: Arity] extends FormulaLabel with WithArity[N]
  /** @see [[lisa.kernel.fol.FOL.ConnectorLabel]] */
  final case class ConstantConnectorLabel[N <: Arity] protected(id: String, arity: N) extends ConnectorLabel[N]
  /**
   * A schematic connector label, exclusive to the front.
   * @see [[ConnectorLabel]]
   */
  final case class SchematicConnectorLabel[N <: Arity] protected(id: String, arity: N) extends ConnectorLabel[N] with SchematicLabel

  object ConstantConnectorLabel {
    private[FormulaLabelDefinitions] def apply[N <: Arity](id: String)(using v: ValueOf[N]): ConstantConnectorLabel[N] = ConstantConnectorLabel(id, v.value)
  }
  object SchematicConnectorLabel {
    def apply[N <: Arity](id: String)(using v: ValueOf[N]): SchematicConnectorLabel[N] = SchematicConnectorLabel(id, v.value)
    def unsafe(id: String, arity: Int): SchematicConnectorLabel[?] = SchematicConnectorLabel(id, arity)
  }

  /** @see [[lisa.kernel.fol.FOL.Neg]] */
  val neg: ConstantConnectorLabel[1] = ConstantConnectorLabel("¬")
  /** @see [[lisa.kernel.fol.FOL.Implies]] */
  val implies: ConstantConnectorLabel[2] = ConstantConnectorLabel("⇒")
  /** @see [[lisa.kernel.fol.FOL.Iff]] */
  val iff: ConstantConnectorLabel[2] = ConstantConnectorLabel("↔")
  /** @see [[lisa.kernel.fol.FOL.And]] */
  val and: ConstantConnectorLabel[2] = ConstantConnectorLabel("∧")
  /** @see [[lisa.kernel.fol.FOL.Or]] */
  val or: ConstantConnectorLabel[2] = ConstantConnectorLabel("∨")

  /** @see [[lisa.kernel.fol.FOL.BinderLabel]] */
  final case class BinderLabel private[FormulaLabelDefinitions](id: String) extends FormulaLabel

  /** @see [[lisa.kernel.fol.FOL.Forall]] */
  val forall: BinderLabel = BinderLabel("∀")
  /** @see [[lisa.kernel.fol.FOL.Exists]] */
  val exists: BinderLabel = BinderLabel("∃")
  /** @see [[lisa.kernel.fol.FOL.ExistsOne]] */
  val existsOne: BinderLabel = BinderLabel("∃!")

}
