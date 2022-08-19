package lisa.front.fol.ops

import lisa.front.fol.definitions.FormulaDefinitions

trait FormulaOps extends FormulaDefinitions with CommonOps {

  // lampepfl/dotty#14907

  //extension[N <: Arity] (label: PredicateLabel[N])
  //  def apply(args: FillArgs[Term, N]): PredicateFormula = PredicateFormula.unsafe(label, tuple2seq(args))
  extension (label: PredicateLabel[2]) { def apply(a: Term, b: Term): PredicateFormula = PredicateFormula.unsafe(label, Seq(a, b)) }
  extension (label: PredicateLabel[1]) { def apply(a: Term): PredicateFormula = PredicateFormula.unsafe(label, Seq(a)) }
  extension (label: PredicateLabel[0]) { def apply(): PredicateFormula = PredicateFormula.unsafe(label, Seq.empty) }

  //extension[N <: Arity] (label: ConnectorLabel[N])
  //  def apply(args: FillArgs[Formula, N]): ConnectorFormula = ConnectorFormula.unsafe(label, tuple2seq(args))
  extension (label: ConnectorLabel[2]) { def apply(a: Formula, b: Formula): ConnectorFormula = ConnectorFormula.unsafe(label, Seq(a, b)) }
  extension (label: ConnectorLabel[1]) { def apply(a: Formula): ConnectorFormula = ConnectorFormula.unsafe(label, Seq(a)) }
  extension (label: ConnectorLabel[0]) { def apply(): ConnectorFormula = ConnectorFormula.unsafe(label, Seq.empty) }

  extension[N <: Arity] (label: BinderLabel) { def apply(bound: VariableLabel, inner: Formula): BinderFormula = BinderFormula(label, bound, inner) }

  given Conversion[ConstantPredicateLabel[0], PredicateFormula] = PredicateFormula.unsafe(_, Seq.empty)
  given Conversion[SchematicPredicateLabel[0], PredicateFormula] = PredicateFormula.unsafe(_, Seq.empty)
  given Conversion[PredicateLabel[0], PredicateFormula] = PredicateFormula.unsafe(_, Seq.empty)

  given Conversion[ConstantConnectorLabel[0], ConnectorFormula] = ConnectorFormula.unsafe(_, Seq.empty)
  given Conversion[SchematicConnectorLabel[0], ConnectorFormula] = ConnectorFormula.unsafe(_, Seq.empty)
  given Conversion[ConnectorLabel[0], ConnectorFormula] = ConnectorFormula.unsafe(_, Seq.empty)

  @deprecated
  given Conversion[Formula, FormulaLabel] = _.label

  extension (f: Formula) {
    def unary_! : ConnectorFormula = ConnectorFormula.unsafe(neg, Seq(f))
    infix def ==>(g: Formula): ConnectorFormula = ConnectorFormula.unsafe(implies, Seq(f, g))
    infix def <=>(g: Formula): ConnectorFormula = ConnectorFormula.unsafe(iff, Seq(f, g))
    infix def /\(g: Formula): ConnectorFormula = ConnectorFormula.unsafe(and, Seq(f, g))
    infix def \/(g: Formula): ConnectorFormula = ConnectorFormula.unsafe(or, Seq(f, g))
  }

  extension (t: Term) {
    infix def ===(u: Term): PredicateFormula = PredicateFormula.unsafe(equality, Seq(t, u))
  }

  // Extractors

  object ! {
    def unapply(f: Formula): Option[Formula] = f match {
      case ConnectorFormula(`neg`, Seq(g)) => Some(g)
      case _ => None
    }
  }

  sealed abstract class UnapplyBinaryConnector(label: ConnectorLabel[2]) {
    def unapply(f: Formula): Option[(Formula, Formula)] = f match {
      case ConnectorFormula(`label`, Seq(a, b)) => Some((a, b))
      case _ => None
    }
  }

  object ==> extends UnapplyBinaryConnector(implies)
  object <=> extends UnapplyBinaryConnector(iff)
  object /\ extends UnapplyBinaryConnector(and)
  object \/ extends UnapplyBinaryConnector(or)

  sealed abstract class UnapplyBinaryPredicate(label: PredicateLabel[2]) {
    def unapply(f: Formula): Option[(Term, Term)] = f match {
      case PredicateFormula(`label`, Seq(a, b)) => Some((a, b))
      case _ => None
    }
  }

  object === extends UnapplyBinaryPredicate(equality)

}
