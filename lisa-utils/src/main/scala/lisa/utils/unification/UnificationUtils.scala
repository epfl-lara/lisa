package lisa.utils.unification

import lisa.kernel.fol.FOL.*
import lisa.utils.KernelHelpers.{_, given}

/**
 * General utilities for unification, substitution, and rewrites
 */
object UnificationUtils {

  /**
   * Helper function for [[canReachOneStepTerm]]
   *
   * @param first term
   * @param second term
   * @param subst list of possible substitutions, with assigned identifiers
   */
  def canReachOneStepTerm2(first: Term, second: Term, subst: Seq[((Term, Term), Identifier)]): Option[Term] = {
    lazy val validSubst = subst.find { case ((l, r), _) => isSameTerm(first, l) && isSameTerm(second, r) }

    if (isSameTerm(first, second)) Some(first)
    else if (validSubst.isDefined) Some(VariableLabel(validSubst.get._2))
    else if (first.label == second.label && first.args.length == second.args.length) {
      val argCan = (first.args zip second.args).map { case (f, s) => canReachOneStepTerm2(f, s, subst) }

      if (argCan.exists(_.isEmpty)) None
      else Some(Term(first.label, argCan.map(_.get)))
    } else None
  }

  /**
   * Helper function for [[canReachOneStepTermFormula]]
   *
   * @param first formula
   * @param second formula
   * @param subst list of term substitutions, with assigned identifiers
   * @param takenIds list of taken identifiers for instantiation
   */
  def canReachOneStepTerm2(first: Formula, second: Formula, subst: Seq[((Term, Term), Identifier)], takenIds: Set[Identifier]): Option[Formula] = {
    if (isSame(first, second)) Some(first)
    else if (first.label != second.label) None
    else
      first match {
        case PredicateFormula(l1, arg1) =>
          second match {
            case PredicateFormula(l2, arg2) => {
              val argCan = (arg1 zip arg2).map { case (f, s) => canReachOneStepTerm2(f, s, subst) }

              if (argCan.exists(_.isEmpty)) None
              else Some(PredicateFormula(l1, argCan.map(_.get)))
            }
            case _ => None
          }
        case ConnectorFormula(l1, arg1) => {
          second match {
            case ConnectorFormula(l2, arg2) => {
              val argCan = (arg1 zip arg2).map { case (f, s) => canReachOneStepTerm2(f, s, subst, takenIds) }

              if (argCan.exists(_.isEmpty)) None
              else Some(ConnectorFormula(l1, argCan.map(_.get)))
            }
            case _ => None
          }
        }
        case BinderFormula(l1, x1: VariableLabel, inner1) => {
          second match {
            case BinderFormula(l2, x2: VariableLabel, inner2) => {
              val newx = VariableLabel(freshId(takenIds, x1.id))
              val newInner1 = substituteVariables(inner1, Map[VariableLabel, Term](x1 -> newx))
              val newInner2 = substituteVariables(inner2, Map[VariableLabel, Term](x2 -> newx))

              canReachOneStepTerm2(newInner1, newInner2, subst, takenIds + newx.id)
            }
            case _ => None
          }
        }
      }
  }

  /**
   * Decides a one-step word problem for two given terms and a set of ground
   * rewrites modulo OL. If possible, returns a context corresponding to the
   * substitution.
   *
   * @param first term
   * @param second term
   * @param subst list of possible substitutions
   * @return
   */
  def canReachOneStepTerm(first: Term, second: Term, subst: List[(Term, Term)]): Option[LambdaTermTerm] = {
    val freeids = (first.freeVariables ++ second.freeVariables).map(_.id)
    val substWithVar = subst
      .foldLeft((freeids, Nil: Seq[((Term, Term), Identifier)])) {
        case ((frs, l), s) => {
          val x = freshId(frs, "x")
          (frs + x, l :+ (s, x))
        }
      }
      ._2
    val body = canReachOneStepTerm2(first, second, substWithVar)

    if (body.isEmpty) None
    else Some(lambda(substWithVar.map(s => VariableLabel(s._2)), body.get))
  }

  /**
   * Decides a one-step word problem for two given formulas and a set of ground
   * term rewrites modulo OL. If possible, returns a context corresponding to
   * the substitution.
   *
   * @param first formula
   * @param second formula
   * @param subst list of possible substitutions
   * @return a lambda term -> formula if the word problem is affirmative
   */
  def canReachOneStepTermFormula(first: Formula, second: Formula, subst: List[(Term, Term)]): Option[LambdaTermFormula] = {
    val takenids = (first.freeVariables ++ second.freeVariables).map(_.id)
    val substWithVar = subst
      .foldLeft((takenids, Nil: Seq[((Term, Term), Identifier)])) {
        case ((frs, l), s) => {
          val x = freshId(frs, "x")
          (frs + x, l :+ (s, x))
        }
      }
      ._2
    val body = canReachOneStepTerm2(first, second, substWithVar, takenids ++ substWithVar.map(_._2))

    if (body.isEmpty) None
    else Some(lambda(substWithVar.map(s => VariableLabel(s._2)), body.get))
  }

  /**
   * Internal function for [[canReachOneStepOLFormula]]
   *
   * @param first formula
   * @param second formula
   * @param subst list of formula substitutions with an assigned identifier
   * @param takenIds list of taken identifiers for instantiation
   */
  def canReachOneStepOLFormula2(first: Formula, second: Formula, subst: Seq[((Formula, Formula), Identifier)], takenIds: Set[Identifier]): Option[Formula] = {
    lazy val validSubst = subst.find { case ((l, r), _) => isSame(first, l) && isSame(second, r) }

    if (isSame(first, second)) Some(first)
    else if (validSubst.isDefined) Some(VariableFormulaLabel(validSubst.get._2))
    else if (first.label != second.label) None
    else
      first match {
        case ConnectorFormula(l1, arg1) => {
          second match {
            case ConnectorFormula(l2, arg2) => {
              val argCan = (arg1 zip arg2).map { case (f, s) => canReachOneStepOLFormula2(f, s, subst, takenIds) }

              if (argCan.exists(_.isEmpty)) None
              else Some(ConnectorFormula(l1, argCan.map(_.get)))
            }
            case _ => None
          }
        }
        case BinderFormula(l1, x1: VariableLabel, inner1) => {
          second match {
            case BinderFormula(l2, x2: VariableLabel, inner2) => {
              val newx = VariableLabel(freshId(takenIds, x1.id))
              val newInner1 = substituteVariables(inner1, Map[VariableLabel, Term](x1 -> newx))
              val newInner2 = substituteVariables(inner2, Map[VariableLabel, Term](x2 -> newx))

              canReachOneStepOLFormula2(newInner1, newInner2, subst, takenIds + newx.id)
            }
            case _ => None
          }
        }
        case _ => None
      }
  }

  /**
   * Decides a one-step word problem for two given formulas and a set of ground
   * formula rewrites modulo OL. If possible, returns a context corresponding to
   * the substitution.
   *
   * @param first formula
   * @param second formula
   * @param subst list of possible formula substitutions
   * @return a lambda formula -> formula if the word problem is affirmative
   */
  def canReachOneStepOLFormula(first: Formula, second: Formula, subst: List[(Formula, Formula)]): Option[LambdaFormulaFormula] = {
    val takenids = (first.freeVariables ++ second.freeVariables).map(_.id)
    val substWithVar = subst
      .foldLeft((takenids, Nil: Seq[((Formula, Formula), Identifier)])) {
        case ((frs, l), s) => {
          val x = freshId(frs, "x")
          (frs + x, l :+ (s, x))
        }
      }
      ._2
    val body = canReachOneStepOLFormula2(first, second, substWithVar, takenids ++ substWithVar.map(_._2))

    if (body.isEmpty) None
    else Some(lambda(substWithVar.map(s => VariableFormulaLabel(s._2)), body.get))
  }

  /**
   * Performs a single step parallel rewrite on a term from given ground term
   * substitutions
   *
   * @param first term to substitute in
   * @param subst list containing pairs representing rewrite rules (l -> r)
   */
  def rewriteOneStepTerm(first: Term, subst: List[(Term, Term)]): Term = {
    val foundSubst = subst.find { case (l, r) => isSameTerm(first, l) }

    if (foundSubst.isDefined) foundSubst.get._2
    else Term(first.label, first.args.map(rewriteOneStepTerm(_, subst)))
  }

  /**
   * Performs a single step parallel rewrite on a formula from given ground term
   * substitutions
   *
   * @param first formula to substitute in
   * @param subst list containing pairs representing rewrite rules (l -> r)
   */
  def rewriteOneStepTermInFormula(first: Formula, subst: List[(Term, Term)], freeVars: Option[Set[Identifier]] = None): Formula = {
    val freeVarsInner =
      if (freeVars.isDefined) freeVars else Some((first.freeVariables ++ subst.foldLeft(Set[VariableLabel]()) { case (frs, (k, v)) => frs ++ k.freeVariables ++ v.freeVariables }).map(_.id))
    first match {
      case PredicateFormula(l, arg) => PredicateFormula(l, arg.map(rewriteOneStepTerm(_, subst)))
      case ConnectorFormula(l, arg) => ConnectorFormula(l, arg.map(rewriteOneStepTermInFormula(_, subst, freeVarsInner)))
      case BinderFormula(l, x: VariableLabel, inner) => {
        val newx = VariableLabel(freshId(freeVarsInner.get, x.id))
        val newInner = substituteVariables(inner, Map[VariableLabel, Term](x -> newx))

        BinderFormula(l, newx, rewriteOneStepTermInFormula(newInner, subst, Some(freeVarsInner.get + newx.id)))
      }
    }
  }

  /**
   * Performs a single step parallel rewrite on a formula from given ground
   * formula substitutions
   *
   * @param first formula to substitute in
   * @param subst list containing pairs representing rewrite rules (l -> r)
   */
  def rewriteOneStepOLFormula(first: Formula, subst: List[(Formula, Formula)], freeVars: Option[Set[Identifier]] = None): Formula = {
    lazy val freeVarsInner =
      if (freeVars.isDefined) freeVars else Some((first.freeVariables ++ subst.foldLeft(Set[VariableLabel]()) { case (frs, (k, v)) => frs ++ k.freeVariables ++ v.freeVariables }).map(_.id))
    val foundSubst = subst.find { case (k, v) => isSame(first, k) }

    if (foundSubst.isDefined) foundSubst.get._2
    else
      first match {
        case PredicateFormula(_, _) => first
        case ConnectorFormula(l, arg) => ConnectorFormula(l, arg.map(rewriteOneStepOLFormula(_, subst, freeVarsInner)))
        case BinderFormula(l, x: VariableLabel, inner) => {
          val newx = VariableLabel(freshId(freeVarsInner.get, x.id))
          val newInner = substituteVariables(inner, Map[VariableLabel, Term](x -> newx))

          BinderFormula(l, newx, rewriteOneStepOLFormula(newInner, subst, Some(freeVarsInner.get + newx.id)))
        }
      }
  }

  /**
   * Extension methods for rewrites
   */
  extension (t: Term) {
    def substituted(subst: (Term, Term)*): Term = rewriteOneStepTerm(t, subst.toList)
  }

  extension (f: Formula) {
    def substitutedTerms(subst: (Term, Term)*): Formula = rewriteOneStepTermInFormula(f, subst.toList)

    def substituted(subst: (Formula, Formula)*): Formula = rewriteOneStepOLFormula(f, subst.toList)
  }
}
