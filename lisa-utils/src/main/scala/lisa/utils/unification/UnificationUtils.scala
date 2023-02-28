package lisa.utils.unification

import lisa.kernel.fol.FOL.*
import lisa.utils.KernelHelpers.{_, given}
import lisa.utils.unification.FirstOrderUnifier.*

/**
 * General utilities for unification, substitution, and rewrites
 */
object UnificationUtils {

  type LambdaTermFormulaFormula = (Seq[VariableFormulaLabel], Seq[VariableLabel], Formula)

  /**
   * Helper function for [[getContextOneStepTerm]]
   *
   * @param first term before substitutions
   * @param second term after substitutions
   * @param subst list of term substitutions, with unique identifiers
   */
  def getContextOneStepTerm2(first: Term, second: Term, subst: Seq[((Term, Term), Identifier)]): Option[Term] = {
    lazy val validSubst = subst.find { case ((l, r), _) => isSameTerm(first, l) && isSameTerm(second, r) }

    if (isSameTerm(first, second)) Some(first)
    else if (validSubst.isDefined) Some(VariableLabel(validSubst.get._2))
    else if (first.label == second.label && first.args.length == second.args.length) {
      val argCan = (first.args zip second.args).map { case (f, s) => getContextOneStepTerm2(f, s, subst) }

      if (argCan.exists(_.isEmpty)) None
      else Some(Term(first.label, argCan.map(_.get)))
    } else None
  }

  /**
   * Finds a unifying context for two given terms and a set of term
   * substitutions if one exists. The context is a lambda term containing
   * uniquely named variables such that for substitutions `{l_i -> r_i}`,
   * `context({l_i}) = first` and `context({r_i}) = second`.
   *
   * @param first term before substitutions
   * @param second term after substitutions
   * @param subst list of term substitutions
   * @return unifying context for `first` and `second`, if one exists
   */
  def getContextOneStepTerm(first: Term, second: Term, subst: List[(Term, Term)]): Option[LambdaTermTerm] = {
    val freeids = (first.freeVariables ++ second.freeVariables).map(_.id)
    val substWithVar = subst
      .foldLeft((freeids, Nil: Seq[((Term, Term), Identifier)])) {
        case ((frs, l), s) => {
          val x = freshId(frs, "x")
          (frs + x, l :+ (s, x))
        }
      }
      ._2
    val body = getContextOneStepTerm2(first, second, substWithVar)

    if (body.isEmpty) None
    else Some(lambda(substWithVar.map(s => VariableLabel(s._2)), body.get))
  }

  /**
   * Internal helper for [[getContextOneStepSingleTerm]].
   *
   * @param first term before substitutions
   * @param subst list of term substitutions with unique identifiers
   */
  def getContextOneStepSingleTerm2(first: Term, subst: List[((Term, Term), Identifier)]): Term = {
    val validSubst = subst.find { case ((l, _), _) => isSameTerm(first, l) }

    if (validSubst.isDefined) VariableLabel(validSubst.get._2)
    else Term(first.label, first.args.map(getContextOneStepSingleTerm2(_, subst)))
  }

  /**
   * Greedily finds a context from a given term, replacing every instance of
   * `l` from a substitution rule `l -> r` with a unique variable and
   * generating a lambda term.
   *
   * @param first term before substitutions
   * @param termSubst list of term substitutions
   * @return lambda term abstracting the substitution positions
   */
  def getContextOneStepSingleTerm(first: Term, termSubst: List[(Term, Term)]): LambdaTermTerm = {
    val takenids = first.freeVariables.map(_.id)
    val substWithVar = termSubst
      .foldLeft((takenids, Nil: List[((Term, Term), Identifier)])) {
        case ((frs, l), s) => {
          val x = freshId(frs, "x")
          (frs + x, l :+ (s, x))
        }
      }

    val body = getContextOneStepSingleTerm2(first, substWithVar._2)

    lambda(
      substWithVar._2.map(s => VariableLabel(s._2)),
      body
    )
  }

  /**
   * Internal Helper for [[getContextOneStepSingleFormula]]
   *
   * @param first formula before substitutions
   * @param formSubst list of formula substitutions with unique identifiers
   * @param termSubst list of term substitutions with unique identifiers
   * @param takenIds list of taken identifiers, for instantiation
   */
  def getContextOneStepSingleFormula2(first: Formula, formSubst: List[((Formula, Formula), Identifier)], termSubst: List[((Term, Term), Identifier)], takenIds: Set[Identifier]): Formula = {
    lazy val validSubst = formSubst.find { case ((l, _), _) => isSame(first, l) }

    if (validSubst.isDefined) VariableFormulaLabel(validSubst.get._2)
    else
      first match {
        case ConnectorFormula(l1, arg1) => ConnectorFormula(l1, arg1.map(getContextOneStepSingleFormula2(_, formSubst, termSubst, takenIds)))
        case BinderFormula(l1, x1: VariableLabel, inner1) => {
          val newx = VariableLabel(freshId(takenIds, x1.id))
          val newInner1 = substituteVariables(inner1, Map[VariableLabel, Term](x1 -> newx))

          BinderFormula(l1, newx, getContextOneStepSingleFormula2(newInner1, formSubst, termSubst, takenIds + newx.id))
        }
        case PredicateFormula(l1, arg1) => PredicateFormula(l1, arg1.map(getContextOneStepSingleTerm2(_, termSubst)))
      }
  }

  /**
   * Greedily finds a context from a given formula, replacing every instance of
   * `l` from a substitution rule `l -> r` with a unique variable and
   * generating a lambda formula.
   *
   * @param first formula before substitutions
   * @param formSubst list of formula substitutions
   * @param termSubst list of term substitutions
   * @return triple (formulaVars, termVars, lambdaBody) abstracting the substitution positions
   */
  def getContextOneStepSingleFormula(first: Formula, formSubst: List[(Formula, Formula)], termSubst: List[(Term, Term)]): LambdaTermFormulaFormula = {
    val takenids = first.freeVariables.map(_.id)
    val formSubstWithVar = formSubst
      .foldLeft((takenids, Nil: List[((Formula, Formula), Identifier)])) {
        case ((frs, l), s) => {
          val x = freshId(frs, "x")
          (frs + x, l :+ (s, x))
        }
      }
    val termSubstWithVar = termSubst
      .foldLeft((formSubstWithVar._1, Nil: List[((Term, Term), Identifier)])) {
        case ((frs, l), s) => {
          val x = freshId(frs, "x")
          (frs + x, l :+ (s, x))
        }
      }

    val body = getContextOneStepSingleFormula2(first, formSubstWithVar._2, termSubstWithVar._2, termSubstWithVar._1)

    (
      formSubstWithVar._2.map(s => VariableFormulaLabel(s._2)),
      termSubstWithVar._2.map(s => VariableLabel(s._2)),
      body
    )
  }

  /**
   * Internal helper for [[getContextOneStep]].
   *
   * @param first formula before substitutions
   * @param second formula after substitutions
   * @param formSubst list of formula substitutions with unique identifiers
   * @param termSubst list of term substitutions with unique identifiers
   * @param takenIds list of taken identifiers, for instantiation
   */
  def getContextOneStep2(
      first: Formula,
      second: Formula,
      formSubst: List[((Formula, Formula), Identifier)],
      termSubst: List[((Term, Term), Identifier)],
      takenIds: Set[Identifier]
  ): Option[Formula] = {
    lazy val validSubst = formSubst.find { case ((l, r), _) => isSame(first, l) && isSame(second, r) }

    if (isSame(first, second)) Some(first)
    else if (validSubst.isDefined) Some(VariableFormulaLabel(validSubst.get._2))
    else if (first.label != second.label) None
    else
      first match {
        case ConnectorFormula(l1, arg1) => {
          second match {
            case ConnectorFormula(l2, arg2) => {
              val argCan = (arg1 zip arg2).map { case (f, s) => getContextOneStep2(f, s, formSubst, termSubst, takenIds) }

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

              val innerRes = getContextOneStep2(newInner1, newInner2, formSubst, termSubst, takenIds + newx.id)

              if (innerRes.isEmpty) innerRes
              else Some(BinderFormula(l1, newx, innerRes.get))
            }
            case _ => None
          }
        }
        case PredicateFormula(l1, arg1) => {
          second match {
            case PredicateFormula(l2, arg2) => {
              val argCan = (arg1 zip arg2).map { case (f, s) => getContextOneStepTerm2(f, s, termSubst) }

              if (argCan.exists(_.isEmpty)) None
              else Some(PredicateFormula(l1, argCan.map(_.get)))
            }
            case _ => None
          }
        }
      }
  }

  /**
   * Finds a unifying context for two given formulas and a set of formula and
   * term substitutions if one exists. The context is a formula containing
   * uniquely named variables such that for substitutions `{l_i -> r_i}`,
   * `context({l_i}) = first` and `context({r_i}) = second`.
   *
   * @param first formula before substitutions
   * @param second formula after substitutions
   * @param formSubst list of formula substitutions
   * @param termSubst list of term substitutions
   * @return unifying context for `first` and `second`, if one exists
   */
  def getContextOneStep(first: Formula, second: Formula, formSubst: List[(Formula, Formula)], termSubst: List[(Term, Term)]): Option[LambdaTermFormulaFormula] = {
    val takenids = (first.freeVariables ++ second.freeVariables).map(_.id)
    val formSubstWithVar = formSubst
      .foldLeft((takenids, Nil: List[((Formula, Formula), Identifier)])) {
        case ((frs, l), s) => {
          val x = freshId(frs, "x")
          (frs + x, l :+ (s, x))
        }
      }
    val termSubstWithVar = termSubst
      .foldLeft((formSubstWithVar._1, Nil: List[((Term, Term), Identifier)])) {
        case ((frs, l), s) => {
          val x = freshId(frs, "x")
          (frs + x, l :+ (s, x))
        }
      }

    val body = getContextOneStep2(first, second, formSubstWithVar._2, termSubstWithVar._2, termSubstWithVar._1)

    if (body.isEmpty) None
    else
      Some(
        (
          formSubstWithVar._2.map(s => VariableFormulaLabel(s._2)),
          termSubstWithVar._2.map(s => VariableLabel(s._2)),
          body.get
        )
      )
  }

  /**
   * Derived utilities
   */

  /**
   * Decides a one-step word problem for two given formulas and a set of ground
   * term rewrites modulo OL. If possible, returns a context corresponding to
   * the substitution. Uses [[getContextOneStep]] for context generation.
   *
   * @param first formula
   * @param second formula
   * @param subst list of possible substitutions
   * @return a lambda term -> formula if the word problem is affirmative
   */
  def getContextOneStepTermFormula(first: Formula, second: Formula, subst: List[(Term, Term)]): Option[LambdaTermFormula] =
    getContextOneStep(first, second, Nil, subst) match {
      case Some(context) => Some(lambda(context._2, context._3))
      case None => None
    }

  /**
   * Decides a one-step word problem for two given formulas and a set of ground
   * formula rewrites modulo OL. If possible, returns a context corresponding to
   * the substitution. Uses [[getContextOneStep]] for context generation.
   *
   * @param first formula
   * @param second formula
   * @param subst list of possible formula substitutions
   * @return a lambda formula -> formula if the word problem is affirmative
   */
  def getContextOneStepFormulaFormula(first: Formula, second: Formula, subst: List[(Formula, Formula)]): Option[LambdaFormulaFormula] =
    getContextOneStep(first, second, subst, Nil) match {
      case Some(context) => Some(lambda(context._1, context._3))
      case None => None
    }

  /**
   * Performs a single step parallel rewrite on a term from given ground term
   * substitutions
   *
   * @param first term to substitute in
   * @param subst list containing pairs representing rewrite rules (l -> r)
   */
  def rewriteOneStepTerm(first: Term, subst: List[(Term, Term)]): Term = {
    val context = getContextOneStepSingleTerm(first, subst)

    context(subst.map(_._2))
  }

  /**
   * Performs a single step parallel rewrite on a formula from given ground
   * formula and term substitutions
   *
   * @param first formula to substitute in
   * @param formSubst list containing formula pairs representing rewrite rules (l -> r)
   * @param termSubst list containing term pairs representing rewrite rules (l -> r)
   */
  def rewriteOneStepFormula(first: Formula, formSubst: List[(Formula, Formula)], termSubst: List[(Term, Term)]): Formula = {
    val context = getContextOneStepSingleFormula(first, formSubst, termSubst)

    // first, substitute term variables, and then formula variables in the
    // context. While safe either way due to unique variable naming above,
    // imitates the order term/formula substitutions *should* be done by hand
    substituteFormulaVariables(
      substituteVariables(
        context._3,
        (context._2 zip termSubst.map(_._2)).toMap
      ),
      (context._1 zip formSubst.map(_._2)).toMap
    )
  }
}
