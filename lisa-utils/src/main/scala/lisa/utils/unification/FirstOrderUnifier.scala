package lisa.utils.unification

import lisa.kernel.fol.FOL.*
import lisa.utils.KernelHelpers.{_, given}

/**
 * Provides complete first-order matching and unification utilities for formulas
 * and terms. Methods return most general substitutions when available.
 */
object FirstOrderUnifier {

  type Substitution = Option[Map[VariableLabel, Term]]
  type FormulaSubstitution = Option[(Map[VariableFormulaLabel, Formula], Map[VariableLabel, Term])]

  /**
   * Performs first-order matching for two formulas. Returns a (most-general)
   * substitution from variables to terms such that `first` substituted is
   * equal to `second`, if one exists. Attempts to match formula variables to
   * formulas, and calls [[matchTerm]] to match any free term variables to
   * terms.
   *
   * @param first the reference formula
   * @param second the formula to match
   * @param subst the current substitution pair (Option), defaults to a pair of
   * empty Maps
   * @return substitution pair (Option) from formula variables to formulas,
   * and variables to terms. `None` if a substitution does not exist.
   */
  def matchFormula(first: Formula, second: Formula, subst: FormulaSubstitution = Some((Map.empty, Map.empty)), vars: Option[Set[VariableLabel | VariableFormulaLabel]] = None): FormulaSubstitution =
    if (subst.isEmpty) subst
    else {
      (first, second) match {
        case (BinderFormula(l1, b1, i1), BinderFormula(l2, b2, i2)) if l1 == l2 => {
          val t = VariableLabel(freshId((i1.freeVariables ++ i2.freeVariables + b1 + b2).map(_.id), b1.id))

          // add a safety substitution to make sure bound variable isn't substituted, and check instantiated bodies
          val innerSubst = matchFormula(
            substituteVariablesInFormula(i1, Map[VariableLabel, Term](b1 -> t)),
            substituteVariablesInFormula(i2, Map[VariableLabel, Term](b2 -> t)),
            Some((subst.get._1, subst.get._2 + ((t -> t): (VariableLabel, Term))))
          )

          innerSubst match {
            case None => innerSubst
            case Some(sf, st) => {
              val cleanSubst = (sf, st - t) // remove the safety substitution we added

              // were any formula substitutions involving the bound variable required?
              // if yes, not matchable
              if (cleanSubst._1.exists((k, v) => v.freeVariables.contains(t))) None
              else Some(cleanSubst)
            }
          }

        }
        case (ConnectorFormula(l1, arg1), ConnectorFormula(l2, arg2)) if l1 == l2 => {
          if (arg1.length != arg2.length) None
          else (arg1 zip arg2).foldLeft(subst) { case (subs: FormulaSubstitution, (f: Formula, s: Formula)) => matchFormula(f, s, subs) }
        }
        // predicate
        case (PredicateFormula(l1, arg1), PredicateFormula(l2, arg2)) if l1 == l2 => {
          // if the label is the same, no issues, move on with term unification
          if (arg1.length != arg2.length) None
          else {
            val termSubst = (arg1 zip arg2).foldLeft(Some(subst.get._2): Substitution) { case (subs: Substitution, (f: Term, s: Term)) => matchTerm(f, s, subs) }
            if (termSubst.isDefined) Some(subst.get._1, termSubst.get)
            else None
          }
        }
        case (PredicateFormula(l1: VariableFormulaLabel, arg1), _) if (vars.isEmpty || vars.get.contains(l1)) => {
          if (second == subst.get._1.getOrElse(l1, second)) Some(subst.get._1 + (l1 -> second), subst.get._2)
          else if (first.label == second.label && second == subst.get._1.getOrElse(l1, second)) subst
          else None
        }
        case _ => None
      }
    }

  /**
   * Performs first-order matching for two terms. Returns a (most-general)
   * substitution from variables to terms such that `first` substituted is
   * equal to `second`, if one exists.
   *
   * @param first the reference term
   * @param second the term to match
   * @param subst the current substitution (Option), defaults to an empty Map
   * @return substitution (Option) from variables to terms
   */
  def matchTerm(first: Term, second: Term, subst: Substitution = Some(Map.empty), vars: Option[Set[VariableLabel]] = None): Substitution =
    if (subst.isEmpty) subst
    else {
      first.label match {
        case v @ VariableLabel(id) if (vars.isEmpty || vars.get.contains(v)) =>
          if (first.label != second.label && second == subst.get.getOrElse(v, second)) Some(subst.get + (v -> second))
          else if (first.label == second.label && first == subst.get.getOrElse(v, first)) subst
          else None
        case _ => // {Constant, Schematic} FunctionLabel
          if (first.label != second.label) None
          else if (first.args.length != second.args.length) None
          else (first.args zip second.args).foldLeft(subst) { case (subs: Substitution, (f: Term, s: Term)) => matchTerm(f, s, subs) }
      }
    }

    /**
     * Performs first-order unification for two formulas. Returns a
     * (most-general) substitution from variables to terms such that `first` and
     * `second` when substituted are equal, if one exists. Attempts to unify
     * formula variables with formulas, and calls [[unifyTerm]] to unify any free
     * term variables with terms.
     *
     * @param first formula to unify
     * @param second formula to unify
     * @param subst the current substitution pair (Option), defaults to a pair of
     * empty Maps
     * @return substitution pair (Option) from formula variables to formulas, and
     * variables to terms. `None` if a substitution does not exist.
     */
  def unifyFormula(first: Formula, second: Formula, subst: FormulaSubstitution = Some((Map.empty, Map.empty))): FormulaSubstitution =
    if (subst.isEmpty) subst
    else {
      (first, second) match {
        case (BinderFormula(l1, b1, i1), BinderFormula(l2, b2, i2)) if l1 == l2 => {
          val t = VariableLabel(freshId((i1.freeVariables ++ i2.freeVariables + b1 + b2).map(_.id), b1.id))

          // add a safety substitution to make sure bound variable isn't substituted, and check instantiated bodies
          val innerSubst = unifyFormula(
            substituteVariablesInFormula(i1, Map[VariableLabel, Term](b1 -> t)),
            substituteVariablesInFormula(i2, Map[VariableLabel, Term](b2 -> t)),
            Some((subst.get._1, subst.get._2 + ((t -> t): (VariableLabel, Term))))
          )

          innerSubst match {
            case None => innerSubst
            case Some(sf, st) => {
              val cleanSubst = (sf, st - t) // remove the safety substitution we added

              // were any formula substitutions involving the bound variable required?
              // if yes, not matchable
              if (cleanSubst._1.exists((k, v) => v.freeVariables.contains(t))) None
              else Some(cleanSubst)
            }
          }

        }
        case (ConnectorFormula(l1, arg1), ConnectorFormula(l2, arg2)) if l1 == l2 => {
          if (arg1.length != arg2.length) None
          else (arg1 zip arg2).foldLeft(subst) { case (subs: FormulaSubstitution, (f: Formula, s: Formula)) => unifyFormula(f, s, subs) }
        }
        // predicate
        case (PredicateFormula(l1, arg1), PredicateFormula(l2, arg2)) if l1 == l2 => {
          // if the label is the same, no issues, move on with term unification
          if (arg1.length != arg2.length) None
          else {
            val termSubst = (arg1 zip arg2).foldLeft(Some(subst.get._2): Substitution) { case (subs: Substitution, (f: Term, s: Term)) => unifyTerm(f, s, subs) }
            if (termSubst.isDefined) Some(subst.get._1, termSubst.get)
            else None
          }
        }
        case (PredicateFormula(l1: VariableFormulaLabel, arg1), _) => {
          if (second == subst.get._1.getOrElse(l1, second) && !second.freeVariableFormulaLabels.contains(l1)) Some(subst.get._1 + (l1 -> second), subst.get._2)
          else if (first.label == second.label && second == subst.get._1.getOrElse(l1, second)) subst
          else None
        }
        case (_, PredicateFormula(l2: VariableFormulaLabel, arg2)) => {
          if (first == subst.get._1.getOrElse(l2, first) && !first.freeVariableFormulaLabels.contains(l2)) Some(subst.get._1 + (l2 -> first), subst.get._2)
          else if (first.label == second.label && first == subst.get._1.getOrElse(l2, first)) subst
          else None
        }
        case _ => None
      }
    }

  /**
   * Performs first-order unification for two terms. Returns a (most-general)
   * substitution from variables to terms such that `first` and `second`
   * substituted are equal, if one exists.
   *
   * @param first term to unify
   * @param second term to unify
   * @param subst the current substitution (Option), defaults to an empty Map
   * @return substitution (Option) from variables to terms
   */
  def unifyTerm(first: Term, second: Term, subst: Substitution = Some(Map.empty)): Substitution =
    if (subst.isEmpty) subst
    else {
      first.label match {
        case v @ VariableLabel(id) =>
          if (first.label != second.label && second == subst.get.getOrElse(v, second) && !second.freeVariables.contains(v)) Some(subst.get + (v -> second))
          else if (first.label == second.label && first == subst.get.getOrElse(v, first)) subst
          else None
        case _ => // {Constant, Schematic} FunctionLabel
          second.label match {
            case v @ VariableLabel(id) =>
              if (first.label != second.label && first == subst.get.getOrElse(v, first) && !first.freeVariables.contains(v)) Some(subst.get + (v -> first))
              else if (first.label == second.label && second == subst.get.getOrElse(v, second)) subst
              else None
            case _ => // {Constant, Schematic} FunctionLabel
              if (first.label != second.label) None
              else if (first.args.length != second.args.length) None
              else (first.args zip second.args).foldLeft(subst) { case (subs: Substitution, (f: Term, s: Term)) => unifyTerm(f, s, subs) }
          }
      }
    }
}
