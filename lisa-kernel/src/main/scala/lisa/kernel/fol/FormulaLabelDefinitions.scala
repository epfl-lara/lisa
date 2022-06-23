package lisa.kernel.fol

/**
 * Definitions of formula labels. Analogous to [[TermLabelDefinitions]].
 */
private[fol] trait FormulaLabelDefinitions extends CommonDefinitions {

  /**
   * The parent class of formula labels.
   * It similar as with terms; they denote the Predicates and logical connector themselves, and not the terms they help forming.
   * They label the nodes of a tree that defines a formula.
   */
  sealed abstract class FormulaLabel extends Label with Ordered[FormulaLabel] {
    def priority: Int = this match {
      case _: ConstantPredicateLabel => 1
      case _: SchematicPredicateLabel => 2
      case _: ConnectorLabel => 3
      case _: BinderLabel => 4
    }

    /**
     * Compare two formula labels by type, then by arity, then by id.
     */
    def compare(that: FormulaLabel): Int = (this, that) match {
      case (thi: ConstantPredicateLabel, tha: ConstantPredicateLabel) => (2 * (thi.arity compare tha.arity) + (thi.id compare tha.id)).sign
      case (thi: SchematicPredicateLabel, tha: SchematicPredicateLabel) => (2 * (thi.arity compare tha.arity) + (thi.id compare tha.id)).sign
      case (thi: ConnectorLabel, tha: ConnectorLabel) => thi.id compare tha.id
      case (thi: BinderLabel, tha: BinderLabel) => thi.id compare tha.id
      case _ => this.priority - that.priority
    }
  }

  /**
   * The label for a predicate, namely a function taking a fixed number of terms and returning a formula.
   * In logical terms it is a predicate symbol.
   */
  sealed abstract class PredicateLabel extends FormulaLabel with Arity {
    require(arity < MaxArity && arity >= 0)
  }

  /**
   * A standard predicate symbol. Typical example are equality (=) and membership (∈)
   */
  sealed case class ConstantPredicateLabel(id: String, arity: Int) extends PredicateLabel with ConstantLabel

  /**
   * The equality symbol (=) for first order logic.
   */
  val equality: ConstantPredicateLabel = ConstantPredicateLabel("=", 2)

  /**
   * A predicate symbol that can be instantiated with any formula.
   */
  sealed case class SchematicPredicateLabel(id: String, arity: Int) extends PredicateLabel

  /**
   * The label for a connector, namely a function taking a fixed number of formulas and returning another formula.
   */
  sealed abstract class ConnectorLabel(val id: String, val arity: Int) extends FormulaLabel with Arity {
    require(arity < MaxArity && arity >= -1)
  }

  case object Neg extends ConnectorLabel("¬", 1)

  case object Implies extends ConnectorLabel("⇒", 2)

  case object Iff extends ConnectorLabel("↔", 2)

  case object And extends ConnectorLabel("∧", -1)

  case object Or extends ConnectorLabel("∨", -1)

  /**
   * The label for a binder, namely an object with a body that has the ability to bind variables in it.
   */
  sealed abstract class BinderLabel(val id: String) extends FormulaLabel

  case object Forall extends BinderLabel(id = "∀")

  case object Exists extends BinderLabel(id = "∃")

  case object ExistsOne extends BinderLabel(id = "∃!")

  def isSame(l: FormulaLabel, r: FormulaLabel): Boolean = (l compare r) == 0

}
