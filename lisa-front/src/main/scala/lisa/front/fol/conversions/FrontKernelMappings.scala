package lisa.front.fol.conversions

import lisa.front.fol.definitions.FormulaDefinitions

trait FrontKernelMappings extends FormulaDefinitions {

  protected val connectorsTo: Map[ConstantConnectorLabel[?], lisa.kernel.fol.FOL.ConnectorLabel] = Map(
    neg -> lisa.kernel.fol.FOL.Neg,
    implies -> lisa.kernel.fol.FOL.Implies,
    iff -> lisa.kernel.fol.FOL.Iff,
    and -> lisa.kernel.fol.FOL.And,
    or -> lisa.kernel.fol.FOL.Or,
  )
  protected val bindersTo: Map[BinderLabel, lisa.kernel.fol.FOL.BinderLabel] = Map(
    forall -> lisa.kernel.fol.FOL.Forall,
    exists -> lisa.kernel.fol.FOL.Exists,
    existsOne -> lisa.kernel.fol.FOL.ExistsOne,
  )
  protected val predicatesTo: Map[ConstantPredicateLabel[?], lisa.kernel.fol.FOL.ConstantPredicateLabel] = Map(
    equality -> lisa.kernel.fol.FOL.equality.asInstanceOf[lisa.kernel.fol.FOL.ConstantPredicateLabel], // Sadly...
  )

  private def reverseMap[U, V](map: Map[U, V]): Map[V, U] = {
    val newMap = map.map(_.swap)
    assert(newMap.size == map.size)
    newMap
  }

  protected val connectorsFrom: Map[lisa.kernel.fol.FOL.ConnectorLabel, ConstantConnectorLabel[?]] = reverseMap(connectorsTo)
  protected val bindersFrom: Map[lisa.kernel.fol.FOL.BinderLabel, BinderLabel] = reverseMap(bindersTo)
  protected val predicatesFrom: Map[lisa.kernel.fol.FOL.ConstantPredicateLabel, ConstantPredicateLabel[?]] = reverseMap(predicatesTo)

}
