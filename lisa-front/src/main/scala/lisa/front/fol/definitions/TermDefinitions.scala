package lisa.front.fol.definitions

trait TermDefinitions extends TermLabelDefinitions {

  protected def pretty(term: Term): String

  /** @see [[lisa.kernel.fol.FOL.Term]] */
  final case class Term protected(label: TermLabel[?], args: Seq[Term]) extends LabeledTree[TermLabel[?]] {
    require(isLegalApplication(label, args))
    override def toString: String = pretty(this)
  }
  object Term {
    def unsafe(label: TermLabel[?], args: Seq[Term]): Term = Term(label, args)
  }

  /** @see [[lisa.kernel.fol.FOL.VariableTerm]] */
  object VariableTerm extends (VariableLabel => Term){
    def apply(label:VariableLabel): Term = Term.unsafe(label, Seq())
    def unapply(t:Term):Option[VariableLabel] = t.label match {
      case l:SchematicTermLabel[?] if l.arity == 0 => Some(l.asInstanceOf[VariableLabel])
      case _ => None
    }
  }

}
