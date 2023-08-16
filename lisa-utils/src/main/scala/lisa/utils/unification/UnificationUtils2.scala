package lisa.utils.unification

import lisa.kernel.fol.FOL.*
import lisa.utils.KernelHelpers.{_, given}
import lisa.utils.unification.FirstOrderUnifier.*

/**
 * General utilities for unification, substitution, and rewriting
 */
object UnificationUtils2 {

  /**
   * All the information required for performing rewrites.
   */
  case class RewriteContext(
      freeFormulaRules: Seq[(Formula, Formula)] = Seq.empty,
      freeTermRules: Seq[(Term, Term)] = Seq.empty,
      confinedFormulaRules: Seq[(Formula, Formula)] = Seq.empty,
      confinedTermRules: Seq[(Term, Term)] = Seq.empty,
      takenFormulaVars: Set[VariableFormulaLabel] = Set.empty,
      takenTermVars: Set[VariableLabel] = Set.empty
  ) {
    private var lastID: Identifier = freshId((takenFormulaVars ++ takenTermVars).map(_.id), "__rewriteVar__")

    def freshIdentifier = {
      lastID = freshId(Seq(lastID), "__rewriteVar__")
      lastID
    }

    def isFreeVariable(v: VariableLabel) = !takenTermVars.contains(v)
    def isFreeVariable(v: VariableFormulaLabel) = !takenFormulaVars.contains(v)

    def updateTo(other: RewriteContext) =
      lastID = if (other.lastID.no > lastID.no) other.lastID else lastID
  }

  object RewriteContext {
    def empty = RewriteContext()
  }

  type TermSubstitution = Map[VariableLabel, Term]
  val TermSubstitution = Map // don't abuse pls O.o

  type FormulaSubstitution = Map[VariableFormulaLabel, Formula]
  val FormulaSubstitution = Map

  def matchTerm(reference: Term, template: Term, takenVariables: Iterator[VariableLabel] = Iterator.empty): Option[TermSubstitution] = {
    val context = RewriteContext(takenTermVars = takenVariables.toSet)
    matchTermRecursive(using context)(reference, template, TermSubstitution.empty)
  }

  private def matchTermRecursive(using context: RewriteContext)(reference: Term, template: Term, substitution: TermSubstitution): Option[TermSubstitution] =
    if (reference == template)
      Some(substitution)
    else
      template.label match {
        case v @ VariableLabel(id) if context.isFreeVariable(v) =>
          // different label but substitutable or already correctly set
          if (reference.label != template.label && reference == substitution.getOrElse(v, reference)) Some(substitution + (v -> reference))
          // same and not already substituted to something else
          else if (reference.label == template.label && reference == substitution.getOrElse(v, reference)) Some(substitution)
          // unsat
          else None
        // {Constant, Schematic} FunctionLabel
        case _ =>
          if (reference.label != template.label) None
          else
            (reference.args zip template.args).foldLeft(Option(substitution)) {
              case (Some(subs), (r, t)) => matchTermRecursive(r, t, subs)
              case (None, _) => None
            }
      }

  def matchFormula(
      reference: Formula,
      template: Formula,
      takenTermVariables: Iterator[VariableLabel] = Iterator.empty,
      takenFormulaVariables: Iterator[VariableFormulaLabel] = Iterator.empty
  ): Option[(FormulaSubstitution, TermSubstitution)] = {
    val context = RewriteContext(
      takenTermVars = takenTermVariables.toSet,
      takenFormulaVars = takenFormulaVariables.toSet
    )
    matchFormulaRecursive(using context)(reference, template, FormulaSubstitution.empty, TermSubstitution.empty)
  }

  private def matchFormulaRecursive(using
      context: RewriteContext
  )(reference: Formula, template: Formula, formulaSubstitution: FormulaSubstitution, termSubstitution: TermSubstitution): Option[(FormulaSubstitution, TermSubstitution)] = {
    if (isSame(reference, template))
      Some((formulaSubstitution, termSubstitution))
    else
      (reference, template) match {
        case (BinderFormula(labelR, boundR, innerR), BinderFormula(labelT, boundT, innerT)) if labelR == labelT => {
          val freshVar = VariableLabel(context.freshIdentifier)

          // add a safety substitution to make sure bound variable isn't substituted, and check instantiated bodies
          val innerSubst = matchFormulaRecursive(
            substituteVariables(innerR, Map[VariableLabel, Term](boundR -> freshVar)),
            substituteVariables(innerT, Map[VariableLabel, Term](boundT -> freshVar)),
            formulaSubstitution,
            termSubstitution + (freshVar -> freshVar) // dummy substitution to make sure we don't attempt to match this as a variable
          )

          innerSubst match {
            case None => innerSubst
            case Some((sf, st)) => {
              val cleanSubst = (sf, st - freshVar) // remove the dummy substitution we added

              // were any formula substitutions involving the bound variable required?
              // if yes, not matchable
              if (cleanSubst._1.exists((k, v) => v.freeVariables.contains(freshVar))) None
              else Some(cleanSubst)
            }
          }
        }

        case (ConnectorFormula(labelR, argsR), ConnectorFormula(labelT, argsT)) if labelR == labelT =>
          if (argsR.length != argsT.length)
            // quick discard
            None
          else {
            // recursively check inner formulas
            val newSubstitution = (argsR zip argsT).foldLeft(Option(formulaSubstitution, termSubstitution)) {
              case (Some(substs), (ref, temp)) => matchFormulaRecursive(ref, temp, substs._1, substs._2)
              case (None, _) => None
            }
            newSubstitution
          }

        case (_, PredicateFormula(labelT: VariableFormulaLabel, _)) =>
          // can this variable be matched with the reference based on previously known or new substitutions?
          if (reference == formulaSubstitution.getOrElse(labelT, reference)) Some(formulaSubstitution + (labelT -> reference), termSubstitution)
          else if (template.label == reference.label && reference == formulaSubstitution.getOrElse(labelT, reference)) Some(formulaSubstitution, termSubstitution)
          else None

        case (PredicateFormula(labelR, argsR), PredicateFormula(labelT, argsT)) if labelR == labelT =>
          if (argsR.length != argsT.length)
            // quick discard
            None
          else {
            // our arguments are terms, match them recursively
            val newTermSubstitution = (argsR zip argsT).foldLeft(Option(termSubstitution)) {
              case (Some(tSubst), (ref, temp)) => matchTermRecursive(ref, temp, tSubst)
              case (None, _) => None
            }
            if (newTermSubstitution.isEmpty) None
            else Some(formulaSubstitution, newTermSubstitution.get)
          }
        case _ => None
      }
  }

  type TermRule = ((Term, Term), TermSubstitution)
  type FormulaRule = ((Formula, Formula), (FormulaSubstitution, TermSubstitution))

  case class TermRewriteLambda(
      termVars: Seq[VariableLabel] = Seq.empty,
      termRules: Map[VariableLabel, TermRule] = Map.empty,
      body: Term
  ) {}

  case class FormulaRewriteLambda(
      termVars: Seq[VariableLabel] = Seq.empty,
      formulaVars: Seq[VariableFormulaLabel] = Seq.empty,
      termRules: Map[VariableLabel, TermRule] = Map.empty,
      formulaRules: Map[VariableFormulaLabel, FormulaRule] = Map.empty,
      body: Formula
  ) {}

  /**
   * Dummy connector used to combine formulas for convenience during rewriting
   */
  val formulaRewriteConnector = SchematicConnectorLabel(Identifier("__rewritesTo__"), 2)

  /**
   * Dummy function symbol used to combine terms for convenience during rewriting
   */
  val termRewriteConnector = ConstantFunctionLabel(Identifier("__rewritesTo__"), 2)

  private def canRewrite(using context: RewriteContext)(first: Term, second: Term, rule: (Term, Term)): Option[TermSubstitution] =
    matchTermRecursive(termRewriteConnector(first, second), termRewriteConnector(rule._1, rule._2), TermSubstitution.empty)

  private def canRewrite(using context: RewriteContext)(first: Formula, second: Formula, rule: (Formula, Formula)): Option[(FormulaSubstitution, TermSubstitution)] =
    matchFormulaRecursive(formulaRewriteConnector(first, second), formulaRewriteConnector(rule._1, rule._2), FormulaSubstitution.empty, TermSubstitution.empty)

  def getContextTerm(
      first: Term,
      second: Term,
      freeTermRules: Seq[(Term, Term)],
      confinedTermRules: Seq[(Term, Term)] = Seq.empty,
      takenTermVariables: Set[VariableLabel] = Set.empty
  ): Option[TermRewriteLambda] = {
    val context = RewriteContext(
      takenTermVars = takenTermVariables,
      freeTermRules = freeTermRules,
      confinedTermRules = confinedTermRules
    )
    getContextRecursive(using context)(first, second)
  }

  private def getContextRecursive(using context: RewriteContext)(first: Term, second: Term): Option[TermRewriteLambda] = {
    // check if there exists a substitution
    val validSubstitution =
      context.confinedTermRules
        .collectFirst { case (l, r) =>
          val subst = canRewrite(using context)(first, second, (l, r))
          subst match {
            case Some(s) => ((l, r), s)
          }
        }
        .orElse {
          // free all variables for substitution
          // matchTermRecursive does not generate any free variables
          // so it cannot affect global state, so this is safe to do
          val freeContext = context.copy(takenTermVars = Set.empty)
          freeContext.freeTermRules.collectFirst { case (l, r) =>
            val subst = canRewrite(using freeContext)(first, second, (l, r))
            subst match {
              case Some(s) => ((l, r), s)
            }
          }
        }

    if (first == second) Some(TermRewriteLambda(body = first))
    else if (validSubstitution.isDefined) {
      val newVar = VariableLabel(context.freshIdentifier)
      val body = Term(newVar, Seq.empty) // newVar()
      Some(
        TermRewriteLambda(
          Seq(newVar),
          Map(newVar -> validSubstitution.get),
          body
        )
      )
    } else if (first.label != second.label || first.args.length == second.args.length) None
    else {
      // recurse
      // known: first.label == second.label
      // first.args.lnegth == second.args.length
      // and first cannot be rewritten into second
      val innerSubstitutions = (first.args zip second.args).map(arg => getContextRecursive(using context)(arg._1, arg._2))

      if (innerSubstitutions.exists(_.isEmpty)) None
      else {
        val retrieved = innerSubstitutions.map(_.get)
        val body = Term(first.label, retrieved.map(_.body))
        val lambda =
          retrieved.foldLeft(TermRewriteLambda(body = body)) { case (currentLambda, nextLambda) =>
            TermRewriteLambda(
              currentLambda.termVars ++ nextLambda.termVars,
              currentLambda.termRules ++ nextLambda.termRules,
              currentLambda.body
            )
          }
        Some(lambda)
      }
    }
  }

  def getContextFormula(
      first: Formula,
      second: Formula,
      freeTermRules: Seq[(Term, Term)],
      freeFormulaRules: Seq[(Formula, Formula)],
      confinedTermRules: Seq[(Term, Term)] = Seq.empty,
      takenTermVariables: Set[VariableLabel] = Set.empty,
      confinedFormulaRules: Seq[(Formula, Formula)] = Seq.empty,
      takenFormulaVariables: Set[VariableFormulaLabel] = Set.empty
  ): Option[FormulaRewriteLambda] = {
    val context = RewriteContext(
      takenTermVars = takenTermVariables,
      takenFormulaVars = takenFormulaVariables,
      freeTermRules = freeTermRules,
      confinedTermRules = confinedTermRules,
      freeFormulaRules = freeFormulaRules,
      confinedFormulaRules = confinedFormulaRules
    )
    getContextRecursive(using context)(first, second)
  }

  private def getContextRecursive(using context: RewriteContext)(first: Formula, second: Formula): Option[FormulaRewriteLambda] = {
    // check if there exists a substitution
    val validSubstitution =
      context.confinedFormulaRules
        .collectFirst { case (l, r) =>
          val subst = canRewrite(using context)(first, second, (l, r))
          subst match {
            case Some(s) => ((l, r), s)
          }
        }
        .orElse {
          // free all variables for substitution
          // matchFormulaRecursive generates but does not expose any new variables
          // It cannot affect global state, so this is safe to do
          val freeContext = context.copy(takenTermVars = Set.empty)
          freeContext.freeFormulaRules.collectFirst { case (l, r) =>
            val subst = canRewrite(using freeContext)(first, second, (l, r))
            subst match {
              case Some(s) => ((l, r), s)
            }
          }
        }

    if (first == second) Some(FormulaRewriteLambda(body = first))
    else if (validSubstitution.isDefined) {
      val newVar = VariableFormulaLabel(context.freshIdentifier)
      val body = PredicateFormula(newVar, Seq.empty) // newVar()
      Some(
        FormulaRewriteLambda(
          Seq.empty,
          Seq(newVar),
          Map(),
          Map(newVar -> validSubstitution.get),
          body
        )
      )
    } else if (first.label != second.label)
      None
    else {
      // recurse
      // known: first.label == second.label
      // and first cannot be rewritten into second
      (first, second) match {
        case (BinderFormula(labelF, boundF, innerF), BinderFormula(labelS, boundS, innerS)) => {
          val freshVar = VariableLabel(context.freshIdentifier)
          val freeContext = context.copy(takenTermVars = context.takenTermVars + freshVar)

          // add a safety substitution to make sure bound variable isn't substituted, and check instantiated bodies
          val innerSubst = getContextRecursive(using freeContext)(
            substituteVariables(innerF, Map[VariableLabel, Term](boundF -> freshVar)),
            substituteVariables(innerS, Map[VariableLabel, Term](boundS -> freshVar))
          )

          context.updateTo(freeContext)

          innerSubst.map(s => s.copy(body = BinderFormula(labelF, boundF, s.body)))
        }

        case (ConnectorFormula(labelF, argsF), ConnectorFormula(labelS, argsS)) =>
          if (argsF.length != argsS.length)
            // quick discard
            None
          else {
            // recursively check inner formulas
            val innerSubstitutions = (argsF zip argsS).map(arg => getContextRecursive(using context)(arg._1, arg._2))

            if (innerSubstitutions.exists(_.isEmpty)) None
            else {
              val retrieved = innerSubstitutions.map(_.get)
              val body = ConnectorFormula(labelF, retrieved.map(_.body))
              val lambda =
                retrieved.foldLeft(FormulaRewriteLambda(body = body)) { case (currentLambda, nextLambda) =>
                  FormulaRewriteLambda(
                    currentLambda.termVars ++ nextLambda.termVars,
                    currentLambda.formulaVars ++ nextLambda.formulaVars,
                    currentLambda.termRules ++ nextLambda.termRules,
                    currentLambda.formulaRules ++ nextLambda.formulaRules,
                    currentLambda.body
                  )
                }
              Some(lambda)
            }
          }

        case (PredicateFormula(labelF, argsF), PredicateFormula(labelS, argsS)) =>
          if (argsF.length != argsS.length)
            // quick discard
            None
          else {
            // our arguments are terms, get contexts from them recursively
            val innerSubstitutions = (argsF zip argsS).map(arg => getContextRecursive(using context)(arg._1, arg._2))

            if (innerSubstitutions.exists(_.isEmpty)) None
            else {
              val retrieved = innerSubstitutions.map(_.get)
              val body = PredicateFormula(labelF, retrieved.map(_.body))
              val lambda =
                retrieved.foldLeft(FormulaRewriteLambda(body = body)) { case (currentLambda, nextLambda) =>
                  FormulaRewriteLambda(
                    currentLambda.termVars ++ nextLambda.termVars,
                    currentLambda.formulaVars,
                    currentLambda.termRules ++ nextLambda.termRules,
                    currentLambda.formulaRules,
                    currentLambda.body
                  )
                }
              Some(lambda)
            }
          }
        case _ => None
      }
    }
  }
}
