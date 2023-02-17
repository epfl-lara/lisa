package lisa.utils.unification

import lisa.kernel.fol.FOL.*
import lisa.utils.KernelHelpers.{_, given}

/**
 * General utilities for unification, substitution, and rewrites
 */
object UnificationUtils {

  def canReachOneStepOLTerm2(first: Term, second: Term, subst: Seq[((Term, Term), Identifier)]): Option[Term] = {
    lazy val validSubst = subst.find { case ((l, r), _) => isSame(first, l) && isSame(second, r) }

    if (isSame(first, second)) Some(first)
    else if (validSubst.isDefined) Some(VariableLabel(validSubst.get._2))
    else if (first.label == second.label && first.args.length == second.args.length) {
      val argCan = (first.args zip second.args).map { case (f, s) => canReachOneStepOLTerm2(f, s, subst) }

      if (argCan.exists(_.isEmpty)) None
      else Some(Term(first.label, argCan.map(_.get)))
    } else None
  }

  def canReachOneStepOLTerm2(first: Formula, second: Formula, subst: Seq[((Term, Term), Identifier)], takenIds: Set[Identifier]): Option[Formula] = {
    if (isSame(first, second)) Some(first)
    else if (first.label != second.label) None
    else
      first match {
        case PredicateFormula(l1, arg1) =>
          second match {
            case PredicateFormula(l2, arg2) => {
              val argCan = (arg1 zip arg2).map { case (f, s) => canReachOneStepOLTerm2(f, s, subst) }

              if (argCan.exists(_.isEmpty)) None
              else Some(PredicateFormula(l1, argCan.map(_.get)))
            }
            case _ => None
          }
        case ConnectorFormula(l1, arg1) => {
          second match {
            case ConnectorFormula(l2, arg2) => {
              val argCan = (arg1 zip arg2).map { case (f, s) => canReachOneStepOLTerm2(f, s, subst, takenIds) }

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

              canReachOneStepOLTerm2(newInner1, newInner2, subst, takenIds + newx.id)
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
  def canReachOneStepOLTerm(first: Term, second: Term, subst: List[(Term, Term)]): Option[LambdaTermTerm] = {
    val freeids = (first.freeVariables ++ second.freeVariables).map(_.id)
    val substWithVar = subst
      .foldLeft((freeids, Nil: Seq[((Term, Term), Identifier)])) {
        case ((frs, l), s) => {
          val x = freshId(frs, "x")
          (frs + x, l :+ (s, x))
        }
      }
      ._2
    val body = canReachOneStepOLTerm2(first, second, substWithVar)

    if (body.isEmpty) None
    else Some(lambda(substWithVar.map(s => VariableLabel(s._2)), body.get))
  }

  def canReachOneStepOLTermFormula(first: Formula, second: Formula, subst: List[(Term, Term)]): Option[LambdaTermFormula] = {
    val takenids = (first.freeVariables ++ second.freeVariables).map(_.id)
    val substWithVar = subst
      .foldLeft((takenids, Nil: Seq[((Term, Term), Identifier)])) {
        case ((frs, l), s) => {
          val x = freshId(frs, "x")
          (frs + x, l :+ (s, x))
        }
      }
      ._2
    val body = canReachOneStepOLTerm2(first, second, substWithVar, takenids ++ substWithVar.map(_._2))

    if (body.isEmpty) None
    else Some(lambda(substWithVar.map(s => VariableLabel(s._2)), body.get))
  }

}
