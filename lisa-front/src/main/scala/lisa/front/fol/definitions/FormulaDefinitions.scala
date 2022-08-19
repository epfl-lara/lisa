package lisa.front.fol.definitions

trait FormulaDefinitions extends FormulaLabelDefinitions with TermDefinitions {

  protected def pretty(formula: Formula): String

  /** @see [[lisa.kernel.fol.FOL.Formula]] */
  sealed abstract class Formula extends LabeledTree[FormulaLabel] {
    override def toString: String = pretty(this)
  }

  /** @see [[lisa.kernel.fol.FOL.PredicateFormula]] */
  final case class PredicateFormula protected(label: PredicateLabel[?], args: Seq[Term]) extends Formula {
    require(isLegalApplication(label, args))
  }
  object PredicateFormula {
    def unsafe(label: PredicateLabel[?], args: Seq[Term]): PredicateFormula = PredicateFormula(label, args)
  }

  /** @see [[lisa.kernel.fol.FOL.ConnectorFormula]] */
  final case class ConnectorFormula protected(label: ConnectorLabel[?], args: Seq[Formula]) extends Formula {
    require(isLegalApplication(label, args))
  }
  object ConnectorFormula {
    def unsafe(label: ConnectorLabel[?], args: Seq[Formula]): ConnectorFormula = ConnectorFormula(label, args)
  }

  /** @see [[lisa.kernel.fol.FOL.BinderFormula]] */
  final case class BinderFormula(label: BinderLabel, bound: VariableLabel, inner: Formula) extends Formula

}
