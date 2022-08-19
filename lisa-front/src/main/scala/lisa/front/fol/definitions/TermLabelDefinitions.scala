package lisa.front.fol.definitions

trait TermLabelDefinitions extends CommonDefinitions {

  /** @see [[lisa.kernel.fol.FOL.TermLabel]] */
  sealed abstract class TermLabel[N<:Arity] extends Label with WithArity[N]

  /** @see [[lisa.kernel.fol.FOL.ConstantLabel]] */
  final case class ConstantFunctionLabel[N <: Arity] protected(id: String, arity: N) extends TermLabel[N]
  /** @see [[lisa.kernel.fol.FOL.SchematicTermLabel]] */
  final case class SchematicTermLabel[N <: Arity] protected(id: String, arity: N) extends TermLabel[N] with SchematicLabel

  type VariableLabel = SchematicTermLabel[0]
  object VariableLabel {
    def unapply(l:VariableLabel): Option[String] = Some(l.id)
    def apply(l:String): VariableLabel = SchematicTermLabel[0](l)
  }

  object ConstantFunctionLabel {
    def apply[N <: Arity](id: String)(using v: ValueOf[N]): ConstantFunctionLabel[N] = ConstantFunctionLabel(id, v.value)
    def unsafe(id: String, arity: Int): ConstantFunctionLabel[?] = ConstantFunctionLabel(id, arity)
  }

  object SchematicTermLabel {
    def apply[N <: Arity](id: String)(using v: ValueOf[N]): SchematicTermLabel[N] = SchematicTermLabel(id, v.value)
    def unsafe(id: String, arity: Int): SchematicTermLabel[?] = SchematicTermLabel(id, arity)
  }

}
