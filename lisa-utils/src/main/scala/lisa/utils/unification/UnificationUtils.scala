package lisa.utils.unification

import lisa.fol.FOL.{_, given}
//import lisa.fol.FOLHelpers.*

//import lisa.kernel.fol.FOL.*
//import lisa.utils.KernelHelpers.{_, given}

/**
 * General utilities for unification, substitution, and rewriting
 */
object UnificationUtils {

  extension [A](seq: Seq[A]) {

    /**
     * Seq.collectFirst, but for a function returning an Option. Evaluates the
     * function only once per argument. Returns when the first non-`None` value
     * is found.
     *
     * @param T output type under option
     * @param f the function to evaluate
     */
    def getFirst[T](f: A => Option[T]): Option[T] = {
      var res: Option[T] = None
      val iter = seq.iterator
      while (res.isEmpty && iter.hasNext) {
        res = f(iter.next())
      }
      res
    }

  }

  /**
   * All the information required for performing rewrites.
   */
  case class RewriteContext(
      freeFormulaRules: Seq[(Formula, Formula)] = Seq.empty,
      freeTermRules: Seq[(Term, Term)] = Seq.empty,
      confinedFormulaRules: Seq[(Formula, Formula)] = Seq.empty,
      confinedTermRules: Seq[(Term, Term)] = Seq.empty,
      takenFormulaVars: Set[VariableFormula] = Set.empty,
      takenTermVars: Set[Variable] = Set.empty
  ) {
    private var lastID: Identifier = freshId((takenFormulaVars ++ takenTermVars).map(_.id), "@@rewriteVar@@")

    /**
     * Generates a fresh identifier with an internal label `__rewriteVar__`.
     * Mutates state.
     *
     * @return fresh identifier
     */
    def freshIdentifier = {
      lastID = freshId(Seq(lastID), "@@rewriteVar@@")
      lastID
    }

    def isFreeVariable(v: Variable) = !takenTermVars.contains(v)
    def isFreeVariable(v: VariableFormula) = !takenFormulaVars.contains(v)

    /**
     * Update the last generated fresh ID to that of another context if it is
     * larger, otherwise retain the previous value. Mutates state.
     *
     * @param other another context
     */
    def updateTo(other: RewriteContext) =
      lastID = if (other.lastID.no > lastID.no) other.lastID else lastID
  }

  object RewriteContext {
    def empty = RewriteContext()
  }

  // substitutions

  type TermSubstitution = Map[Variable, Term]
  val TermSubstitution = Map // don't abuse pls O.o

  type FormulaSubstitution = Map[VariableFormula, Formula]
  val FormulaSubstitution = Map

  /**
   * Performs first-order matching for two terms. Returns a (most-general)
   * substitution from variables to terms such that `first` substituted is equal  TODO: Fix `first`and `second`
   * to `second`, if one exists. Uses [[matchTermRecursive]] as the actual
   * implementation.
   *
   * @param reference the reference term
   * @param template the term to match
   * @param takenVariables any variables in the template which cannot be
   * substituted, i.e., treated as constant
   * @return substitution (Option) from variables to terms. `None` iff a
   * substitution does not exist.
   */
  def matchTerm(reference: Term, template: Term, takenVariables: Iterable[Variable] = Iterable.empty): Option[TermSubstitution] = {
    val context = RewriteContext(takenTermVars = takenVariables.toSet)
    matchTermRecursive(using context)(reference, template, TermSubstitution.empty)
  }

  /**
   * Implementation for matching terms. See [[matchTerm]] for the interface.
   *
   * @param context all information about restricted variables and fresh name
   * generation state
   * @param reference the reference terms
   * @param template the terms to match
   * @param substitution currently accumulated susbtitutions to variables
   * @return substitution (Option) from variables to terms. `None` if a
   * substitution does not exist.
   */
  private def matchTermRecursive(using context: RewriteContext)(reference: Term, template: Term, substitution: TermSubstitution): Option[TermSubstitution] =
    if (reference == template)
      Some(substitution)
    else
      template match {
        case v @ Variable(id) if context.isFreeVariable(v) =>
          // different label but substitutable or already correctly set
          if (reference != template && reference == substitution.getOrElse(v, reference)) Some(substitution + (v -> reference))
          // same and not already substituted to something else
          else if (reference == template && reference == substitution.getOrElse(v, reference)) Some(substitution)
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

  /**
   * Performs first-order matching for two formulas. Returns a (most-general)
   * substitution from variables to terms such that `first` substituted is equal
   * to `second`, if one exists. Uses [[matchFormulaRecursive]] as the actual
   * implementation.
   *
   * @param reference the reference formula
   * @param template the formula to match
   * @param takenTermVariables any variables in the template which cannot be
   * substituted, i.e., treated as constant
   * @param takenFormulaVariables any formula variables in the template which
   * cannot be substituted, i.e., treated as constant
   * @return substitution pair (Option) from formula variables to formulas, and
   * variables to terms. `None` if a substitution does not exist.
   */
  def matchFormula(
      reference: Formula,
      template: Formula,
      takenTermVariables: Iterable[Variable] = Iterable.empty,
      takenFormulaVariables: Iterable[VariableFormula] = Iterable.empty
  ): Option[(FormulaSubstitution, TermSubstitution)] = {
    val context = RewriteContext(
      takenTermVars = takenTermVariables.toSet,
      takenFormulaVars = takenFormulaVariables.toSet
    )
    matchFormulaRecursive(using context)(reference, template, FormulaSubstitution.empty, TermSubstitution.empty)
  }

  /**
   * Implementation for matching formulas. See [[matchFormula]] for the
   * interface.
   *
   * @param context all information about restricted variables and fresh name generation state
   * @param reference the reference formula
   * @param template the formula to match
   * @param formulaSubstitution currently accumulated susbtitutions to formula variables
   * @param termSubstitution currently accumulated susbtitutions to term variables
   * @return substitution pair (Option) from formula variables to formulas, and
   * variables to terms. `None` if a substitution does not exist.
   */
  private def matchFormulaRecursive(using
      context: RewriteContext
  )(reference: Formula, template: Formula, formulaSubstitution: FormulaSubstitution, termSubstitution: TermSubstitution): Option[(FormulaSubstitution, TermSubstitution)] = {
    if (isSame(reference, template))
      Some((formulaSubstitution, termSubstitution))
    else
      (reference, template) match {
        case (BinderFormula(labelR, boundR, innerR), BinderFormula(labelT, boundT, innerT)) if labelR == labelT => {
          val freshVar = Variable(context.freshIdentifier)

          // add a safety substitution to make sure bound variable isn't substituted, and check instantiated bodies
          val innerSubst = matchFormulaRecursive(
            innerR.substitute(boundR := freshVar),
            innerT.substitute(boundT := freshVar),
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

        case (_, template: VariableFormula) =>
          // can this variable be matched with the reference based on previously known or new substitutions?
          if (reference == formulaSubstitution.getOrElse(template, reference)) Some(formulaSubstitution + (template -> reference), termSubstitution)
          else if (template == reference && reference == formulaSubstitution.getOrElse(template, reference)) Some(formulaSubstitution, termSubstitution)
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
  // rewrites

  /**
   * A term rewrite rule (`l -> r`) with an accompanying instantiation, given
   * by a term substitution.
   *
   * @example A rule without any instantiation would be `((l -> r),
   * TermSubstitution.empty)`.
   * @example Commutativity of a function with instantiation can be `((f(x, y)
   * -> f(y, x)), Map(x -> pair(a, b), y -> c))`
   */
  type TermRule = ((Term, Term), TermSubstitution)

  /**
   * A formula rewrite rule (`l -> r`) with an accompanying instantiation,
   * given by a formula and a term substitution.
   *
   * @example A rule without any instantiation would be `((l -> r),
   * FormulaSubstitution.empty)`.
   * @example `((P(x) \/ Q -> Q /\ R(x)), Map(Q -> A \/ B, x -> f(t)))`
   */
  type FormulaRule = ((Formula, Formula), (FormulaSubstitution, TermSubstitution))

  /**
   * A lambda representing a term, with inputs as terms. Carries extra
   * information about rewrite rules used in its construction for proof
   * genration later.
   *
   * @param termVars variables in the body to be treated as parameters closed
   * under this function
   * @param termRules mapping to the rules (with instantiations) used to
   * construct this function; used for proof construction
   * @param body the body of the function
   */
  case class TermRewriteLambda(
      termVars: Seq[Variable] = Seq.empty,
      termRules: Seq[(Variable, TermRule)] = Seq.empty,
      body: Term
  ) {}

  /**
   * A lambda representing a formula, with inputs as terms or formulas. Carries
   * extra information about rewrite rules used in its construction for proof
   * geenration later.
   *
   * @param termVars variables in the body to be treated as parameters closed
   * under this function
   * @param formulaVars formula variables in the body to be treated as
   * parameters closed under this function
   * @param termRules mapping to the term rewrite rules (with instantiations)
   * used to construct this function; used for proof construction
   * @param formulaRules mapping to the formula rewrite rules (with
   * instantiations) used to construct this function; used for proof
   * construction
   * @param body the body of the function
   */
  case class FormulaRewriteLambda(
      termRules: Seq[(Variable, TermRule)] = Seq.empty,
      formulaRules: Seq[(VariableFormula, FormulaRule)] = Seq.empty,
      body: Formula
  ) {

    /**
     * **Unsafe** conversion to a term lambda, discarding rule and formula information
     *
     * Use if **know that only term rewrites were applied**.
     */
    def toLambdaTF: LambdaExpression[Term, Formula, ?] = LambdaExpression(termRules.map(_._1), body, termRules.size)

    /**
     * **Unsafe** conversion to a formula lambda, discarding rule and term information
     *
     * Use if **know that only formula rewrites were applied**.
     */
    def toLambdaFF: LambdaExpression[Formula, Formula, ?] = LambdaExpression(formulaRules.map(_._1), body, formulaRules.size)
  }

  /**
   * Dummy connector used to combine formulas for convenience during rewriting
   */
  val formulaRewriteConnector = SchematicConnectorLabel(Identifier("@@rewritesTo@@"), 2)

  /**
   * Dummy function symbol used to combine terms for convenience during rewriting
   */
  val termRewriteConnector = ConstantFunctionLabel(Identifier("@@rewritesTo@@"), 2)

  /**
   * Decides whether a term `first` be rewritten into `second` at the top level
   * using the provided rewrite rule (with instantiation).
   *
   * Reduces to matching using [[matchTermRecursive]].
   */
  private def canRewrite(using context: RewriteContext)(first: Term, second: Term, rule: (Term, Term)): Option[TermSubstitution] =
    matchTermRecursive(termRewriteConnector(first, second), termRewriteConnector(rule._1, rule._2), TermSubstitution.empty)

  /**
   * Decides whether a formula `first` be rewritten into `second` at the top
   * level using the provided rewrite rule (with instantiation). Produces the
   * instantiation as output, if one exists.
   *
   * Reduces to matching using [[matchFormulaRecursive]].
   */
  private def canRewrite(using context: RewriteContext)(first: Formula, second: Formula, rule: (Formula, Formula)): Option[(FormulaSubstitution, TermSubstitution)] =
    matchFormulaRecursive(formulaRewriteConnector(first, second), formulaRewriteConnector(rule._1, rule._2), FormulaSubstitution.empty, TermSubstitution.empty)

  /**
   * Decides whether a term `first` can be rewritten into another term `second`
   * under the given rewrite rules and restrictions.
   *
   * Calls [[getContextRecursive]] as its actual implementation.
   *
   * @param first source term
   * @param second destination term
   * @param freeTermRules rewrite rules with unrestricted instantiations
   * @param confinedTermRules rewrite rules with restricted instantiations wrt takenTermVariables
   * @param takenTermVariables variables to *not* instantiate, i.e., treat as constant, for confined rules
   */
  def getContextTerm(
      first: Term,
      second: Term,
      freeTermRules: Seq[(Term, Term)],
      confinedTermRules: Seq[(Term, Term)] = Seq.empty,
      takenTermVariables: Set[Variable] = Set.empty
  ): Option[TermRewriteLambda] = {
    val context = RewriteContext(
      takenTermVars = takenTermVariables,
      freeTermRules = freeTermRules,
      confinedTermRules = confinedTermRules
    )
    getContextRecursive(using context)(first, second)
  }

  /**
   * Inner implementation for [[getContextTerm]].
   *
   * @param context all information about rewrite rules and allowed instantiations
   * @param first source term
   * @param second destination term
   */
  private def getContextRecursive(using context: RewriteContext)(first: Term, second: Term): Option[TermRewriteLambda] = {
    // check if there exists a substitution
    lazy val validSubstitution =
      context.confinedTermRules
        .getFirst { case (l, r) =>
          val subst = canRewrite(using context)(first, second, (l, r))
          subst.map(s => ((l, r), s))
        }
        .orElse {
          // free all variables for substitution
          // matchTermRecursive does not generate any free variables
          // so it cannot affect global state, so this is safe to do
          val freeContext = context.copy(takenTermVars = Set.empty)
          freeContext.freeTermRules.getFirst { case (l, r) =>
            val subst = canRewrite(using freeContext)(first, second, (l, r))
            subst.map(s => ((l, r), s))
          }
        }

    if (first == second) Some(TermRewriteLambda(body = first))
    else if (validSubstitution.isDefined) {
      val newVar = Variable(context.freshIdentifier)
      val body = newVar // newVar()
      Some(
        TermRewriteLambda(
          Seq(newVar),
          Seq(newVar -> validSubstitution.get),
          body
        )
      )
    } else if (first.label != second.label || first.args.length != second.args.length) None
    else {
      // recurse
      // known: first.label == second.label
      // first.args.length == second.args.length
      // and first cannot be rewritten into second
      val innerSubstitutions = (first.args zip second.args).map(arg => getContextRecursive(using context)(arg._1, arg._2))

      if (innerSubstitutions.exists(_.isEmpty)) None
      else {
        val retrieved = innerSubstitutions.map(_.get)
        val body = first.label(retrieved.map(_.body))
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

  /**
   * Decides whether a formula `first` can be rewritten into another formula
   * `second` under the given rewrite rules and restrictions.
   *
   * Calls [[getContextRecursive]] as its actual implementation.
   *
   * @param first source formula
   * @param second destination formula
   * @param freeTermRules term rewrite rules with unrestricted instantiations
   * @param freeFormulaRules formula rewrite rules with unrestricted
   * instantiations
   * @param confinedTermRules term rewrite rules with restricted instantiations
   * wrt takenTermVariables
   * @param confinedTermRules formula rewrite rules with restricted
   * instantiations wrt takenTermVariables
   * @param takenTermVariables term variables to *not* instantiate, i.e., treat
   * as constant, for confined rules
   * @param takenFormulaVariables formula variables to *not* instantiate, i.e.,
   * treat as constant, for confined rules
   */
  def getContextFormula(
      first: Formula,
      second: Formula,
      freeTermRules: Seq[(Term, Term)] = Seq.empty,
      freeFormulaRules: Seq[(Formula, Formula)] = Seq.empty,
      confinedTermRules: Seq[(Term, Term)] = Seq.empty,
      takenTermVariables: Set[Variable] = Set.empty,
      confinedFormulaRules: Seq[(Formula, Formula)] = Seq.empty,
      takenFormulaVariables: Set[VariableFormula] = Set.empty
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

  def getContextFormulaSet(
      first: Seq[Formula],
      second: Seq[Formula],
      freeTermRules: Seq[(Term, Term)],
      freeFormulaRules: Seq[(Formula, Formula)],
      confinedTermRules: Seq[(Term, Term)] = Seq.empty,
      takenTermVariables: Set[Variable] = Set.empty,
      confinedFormulaRules: Seq[(Formula, Formula)] = Seq.empty,
      takenFormulaVariables: Set[VariableFormula] = Set.empty
  ): Option[Seq[FormulaRewriteLambda]] = {
    val context = RewriteContext(
      takenTermVars = takenTermVariables,
      takenFormulaVars = takenFormulaVariables,
      freeTermRules = freeTermRules,
      confinedTermRules = confinedTermRules,
      freeFormulaRules = freeFormulaRules,
      confinedFormulaRules = confinedFormulaRules
    )

    val substSeq = first.map { f =>
      second.getFirst { s =>
        val newContext = context.copy()
        val subst = getContextRecursive(using newContext)(f, s)
        subst.foreach { _ => context.updateTo(newContext) }
        subst
      }
    }

    // Seq[Option[_]] -> Option[Seq[_]]
    substSeq.foldLeft(Option(Seq.empty[FormulaRewriteLambda]))((f, s) => f.flatMap(f1 => s.map(s1 => f1 :+ s1)))
  }

  /**
   * Inner implementation for [[getContextFormula]].
   *
   * @param context all information about rewrite rules and allowed instantiations
   * @param first source formula
   * @param second destination formula
   */
  private def getContextRecursive(using context: RewriteContext)(first: Formula, second: Formula): Option[FormulaRewriteLambda] = {
    // check if there exists a substitution
    lazy val validSubstitution =
      context.confinedFormulaRules
        .getFirst { (l: Formula, r: Formula) =>
          val subst = canRewrite(using context)(first, second, (l, r))
          subst.map(s => ((l, r), s))
        }
        .orElse {
          // free all variables for substitution
          // matchFormulaRecursive generates but does not expose any new variables
          // It cannot affect global state, so this is safe to do
          val freeContext = context.copy(takenTermVars = Set.empty)
          freeContext.freeFormulaRules.getFirst { case (l, r) =>
            val subst = canRewrite(using freeContext)(first, second, (l, r))
            subst.map(s => ((l, r), s))
          }
        }

    if (isSame(first, second)) Some(FormulaRewriteLambda(body = first))
    else if (validSubstitution.isDefined) {
      val newVar = VariableFormula(context.freshIdentifier)
      val body = newVar // newVar()
      Some(
        FormulaRewriteLambda(
          Seq(),
          Seq(newVar -> validSubstitution.get),
          body
        )
      )
    } // else if (first.label != second.label) None //Should not pass the next match anyway
    else {
      // recurse
      // known: first.label == second.label
      // and first cannot be rewritten into second
      (first, second) match {
        case (BinderFormula(labelF, boundF, innerF), BinderFormula(labelS, boundS, innerS)) => {
          val freshVar = Variable(context.freshIdentifier)
          val freeContext = context.copy(takenTermVars = context.takenTermVars + freshVar)

          // add a safety substitution to make sure bound variable isn't substituted, and check instantiated bodies
          val innerSubst = getContextRecursive(using freeContext)(
            innerF.substitute(boundF := freshVar),
            innerS.substitute(boundS := freshVar)
          )

          context.updateTo(freeContext)

          innerSubst.map(s => s.copy(body = BinderFormula(labelF, freshVar, s.body)))
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
