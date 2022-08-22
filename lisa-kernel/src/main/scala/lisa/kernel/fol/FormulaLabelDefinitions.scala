package lisa.kernel.fol

/**
 * Definitions of formula labels. Analogous to [[TermLabelDefinitions]].
 */
private[fol] trait FormulaLabelDefinitions extends CommonDefinitions {

  /**
   * The parent class of formula labels.
   * These are labels that can be applied to nodes that form the tree of a formula.
   * In logical terms, those labels are FOL symbols or predicate symbols, including equality.
   */
  sealed abstract class FormulaLabel extends Label

  /**
   * The label for a predicate, namely a function taking a fixed number of terms and returning a formula.
   * In logical terms it is a predicate symbol.
   */
  sealed trait PredicateLabel extends FormulaLabel {
    require(arity < MaxArity && arity >= 0)
  }
  /**
   * The label for a connector, namely a function taking a fixed number of formulas and returning another formula.
   */
  sealed trait ConnectorLabel extends FormulaLabel {
    require(arity < MaxArity && arity >= -1)
  }

  /**
   * A standard predicate symbol. Typical example are equality (=) and membership (∈)
   */
  sealed case class ConstantPredicateLabel(id: String, arity: Int) extends PredicateLabel with ConstantLabel

  /**
   * The equality symbol (=) for first order logic.
   * It is represented as any other predicate symbol but has unique semantic and deduction rules.
   */
  val equality: ConstantPredicateLabel = ConstantPredicateLabel("=", 2)

  /**
   * The label for a connector, namely a function taking a fixed number of formulas and returning another formula.
   */
  sealed abstract class ConstantConnectorLabel(val id: String, val arity: Int) extends ConnectorLabel with ConstantLabel
  case object Neg extends ConstantConnectorLabel("¬", 1)

  case object Implies extends ConstantConnectorLabel("⇒", 2)

  case object Iff extends ConstantConnectorLabel("↔", 2)

  case object And extends ConstantConnectorLabel("∧", -1)

  case object Or extends ConstantConnectorLabel("∨", -1)



  /**
   * A predicate symbol that can be instantiated with any formula.
   * We distinguish arity-0 schematic formula labels, arity->1 schematic predicates and arity->1 schematic connectors.
   */
  sealed trait SchematicFormulaLabel extends FormulaLabel with SchematicLabel
  sealed trait SchematicVarOrPredLabel extends SchematicFormulaLabel with PredicateLabel

  /**
   * A predicate symbol of arity 0 that can be instantiated with any formula.
   */
  sealed case class VariableFormulaLabel(id: String) extends SchematicVarOrPredLabel {
    val arity = 0
  }


  /**
   * A predicate symbol of non-zero arity that can be instantiated with any functional formula taking term arguments.
   */
  sealed case class SchematicPredicateLabel(id: String, arity: Int) extends SchematicVarOrPredLabel
  /**
   * A predicate symbol of non-zero arity that can be instantiated with any functional formula taking formula arguments.
   */
  sealed case class SchematicConnectorLabel(id: String, arity: Int) extends SchematicFormulaLabel with ConnectorLabel



  /**
   * The label for a binder, namely an object with a body that has the ability to bind variables in it.
   */
  sealed abstract class BinderLabel(val id: String) extends FormulaLabel {
    val arity = 1
  }

  case object Forall extends BinderLabel(id = "∀")

  case object Exists extends BinderLabel(id = "∃")

  case object ExistsOne extends BinderLabel(id = "∃!")

  def isSame(l: FormulaLabel, r: FormulaLabel): Boolean = l == r

}
