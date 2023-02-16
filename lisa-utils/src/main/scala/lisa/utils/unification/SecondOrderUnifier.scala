package lisa.utils.unification

import lisa.kernel.fol.FOL.*
import lisa.utils.KernelHelpers.{_, given}

object SecondOrderUnifier {

  type Substitution = Option[Map[VariableLabel, Term]]
  type FormulaSubstitution = Option[(Map[VariableFormulaLabel, Formula], Map[VariableLabel, Term])]

  def matchFormula(first: Formula, second: Formula, subst: FormulaSubstitution, vars: Option[Set[VariableLabel | VariableFormulaLabel]]): FormulaSubstitution = ???
  def matchTerm(first: Term, second: Term, subst: Substitution, vars: Option[Set[VariableLabel | VariableFormulaLabel]]): Substitution = ???

  def unifyFormula(first: Formula, second: Formula, subst: FormulaSubstitution): FormulaSubstitution = ???
  def unifyTerm(first: Term, second: Term, subst: Substitution): Substitution = ???
    
}
