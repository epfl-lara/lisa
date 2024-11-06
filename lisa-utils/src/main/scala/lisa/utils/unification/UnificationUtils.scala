package lisa.utils.unification

import lisa.utils.fol.FOL.{_, given}
import lisa.utils.prooflib.Library
import lisa.utils.prooflib.SimpleDeducedSteps
import lisa.utils.K
import lisa.utils.memoization.memoized
import lisa.utils.collection.Extensions.*
import lisa.utils.collection.{VecSet => Set}
import lisa.utils.fol.FOL

/**
 * General utilities for unification, substitution, and rewriting
 */
object UnificationUtils:

  /**
    * Chosen equality for terms in matching and rewriting.
    */
  inline def eq[A](l: Expr[A], r: Expr[A]) = isSame(l, r)

  /**
   * Context containing information and constraints pertaining to matching,
   * unification, and rewriting.
   *
   * @param boundVariables variables in terms that cannot be substituted
   */
  case class RewriteContext(
      boundVariables: Set[Variable[?]],
      freeRules: Set[RewriteRule],
      confinedRules: Set[RewriteRule],
  ):
    // when a context is constructed, update the global ID counter to make sure
    // we aren't conflicting with variable names in the rewrite rules
    RewriteContext.updateIDCounts(this)

    /**
      * Checks if a variable is free under this context.
      */
    def isFree[A](v: Variable[A]) = !isBound(v)

    /**
      * Checks if a variable is bound under this context.
      */
    def isBound[A](v: Variable[A]) = boundVariables.contains(v)

    /**
      * A copy of this context with the given variable additionally bound.
      */
    def withBound[A](v: Variable[A]) = 
      this.copy(boundVariables = boundVariables + v)

    /**
      * A copy of this context with the given variables additionally bound.
      */
    def withBound(vs: Iterable[Variable[?]]) = 
      this.copy(boundVariables = boundVariables ++ vs)

    /**
      * A copy of this context with the given pair added as a _free_ rewrite
      * rule, whose variables may be instantiated during rewriting.
      */
    def withFreeRule[A](rule: RewriteRule) =
      this.copy(freeRules = freeRules + rule)

    /**
      * A copy of this context with the given pair added as a _confined_ rewrite
      * rule, whose variables may *not* be instantiated during rewriting.
      */
    def withConfinedRule[A](rule: RewriteRule) =
      this.copy(confinedRules = confinedRules + rule)
  
    /**
      * All rules (free + confined) in this context.
      */
    def allRules: Set[RewriteRule] = freeRules ++ confinedRules

    val representativeVariable = memoized(__representativeVariable)

    private def __representativeVariable(rule: InstantiatedRewriteRule): Variable[?] = 
      val id = RewriteContext.freshRepresentative
      rule.rule match
        case TermRewriteRule(_, _) => Variable[Term](id) 
        case FormulaRewriteRule(_, _) => Variable[Formula](id)
        // should not reach under general use, but why not:
        case r: InstantiatedRewriteRule => representativeVariable(r)

  object RewriteContext:
    /**
      * The empty rewrite context.
      */
    def empty = RewriteContext(Set.empty, Set.empty, Set.empty)

    /**
      * A rewrite context with the given variables considered bound.
      */
    def withBound(vars: Iterable[Variable[?]]) =
      RewriteContext(vars.to(Set), Set.empty, Set.empty)

    private object IDCounter:
      val reprName = "@@internalRewriteVar@@"
      private var current = 0
      def setIDCountTo(limit: Int): Unit = 
        current = math.max(limit, current)
      def nextIDCount: Int =
        current += 1
        current
       
    import IDCounter.{reprName, setIDCountTo, nextIDCount}

    private def freshRepresentative: Identifier =
      Identifier(reprName, nextIDCount)

    private def maxVarId[A](expr: Expr[A]): Int = 
      expr match
        case Variable(id: Identifier) => id.no
        case Constant(id) => 0
        case App(f, arg) => math.max(maxVarId(f), maxVarId(arg))
        case Abs(v: Variable[?], body: Expr[?]) => math.max(maxVarId(v), maxVarId(body))

    private def updateIDCounts(ctx: RewriteContext): Unit =
      val max = ctx.allRules.map(r => maxVarId(r.toFormula)).maxOption.getOrElse(0) + 1
      setIDCountTo(max)

  /**
   * Immutable representation of a typed variable substitution.
   * 
   * Wraps an immutable map while preserving variable types.
   *
   * Types are discarded for storage but are guaranteed to be sound by
   * construction.
   *
   * @param assignments mappings to initialize the substitution with
   */
  class Substitution private (
      protected val assignments: Map[Variable[?], Expr[?]], 
      protected val freeVariables: Set[Variable[?]]
    ):
    // invariant:
    // require(
    //   freeVariables == assignments.keySet ++ assignments.values.flatMap(_.freeVars)
    // )

    /**
     * (Optionally) retrieves a variable's mapping
     */
    def apply[A](v: Variable[A]): Option[Expr[A]] =
      assignments.get(v).map(_.asInstanceOf[Expr[A]])

    /**
     * Creates a new substitution with a new mapping added
     */
    def +[A](mapping: (Variable[A], Expr[A])): Substitution =
      val newfree = mapping._2.freeVars + mapping._1
      Substitution(assignments + mapping, freeVariables ++ newfree)

    /**
     * Checks whether a variable is assigned by this substitution
     */
    def contains[A](v: Variable[A]): Boolean =
      assignments.contains(v)

    /**
     * Checks whether any substitution contains the given variable. Needed for
     * verifying ill-formed substitutions containing bound variables.
     *
     * Eg: if `v` is externally bound, then `x` and `f(v)` have no matcher under
     * capture avoiding substitution.
     */
    def substitutes[A](v: Variable[A]): Boolean =
      freeVariables(v)

    def asSubstPair: Seq[SubstPair] =
      assignments.map((v, e) => v := e.asInstanceOf).toSeq

  object Substitution:
    /**
     * The empty substitution
     */
    def empty: Substitution = Substitution(Map.empty, Set.empty)

  /**
   * Performs first-order matching for two terms. Returns a (most-general)
   * substitution from variables to terms such that `expr` substituted is equal
   * to `pattern`, if one exists.
   * 
   * Does not use rewrite rules provided by `ctx`, if any.
   *
   * @param expr the reference term (to substitute in)
   * @param pattern the pattern to match against
   * @param subst partial substitution to match under
   * @param ctx (implicit) context to match under
   * @return substitution (Option) from variables to terms. `None` iff a
   * substitution does not exist.
   */
  def matchExpr[A](using ctx: RewriteContext)(expr: Expr[A], pattern: Expr[A], subst: Substitution = Substitution.empty): Option[Substitution] =
    // chosen equality: ortholattice equivalence
    inline def eq(l: Expr[A], r: Expr[A]) = isSame(l, r)

    if eq(expr, pattern) then
      // trivial, done
      Some(subst)
    else
      (expr, pattern) match
        case (v @ Variable(_), _) if ctx.isFree(v) =>
          subst(v) match
            case Some(e) =>
              // this variable has been assigned before.
              // is that subst compatible with this instance?
              if eq(e, pattern) then Some(subst) else None
            case None =>
              // first encounter
              Some(subst + (v -> pattern))
        case (App(fe, arge), App(fp, argp)) if fe.sort == fp.sort =>
          // the sort of fp is already runtime checked here; the sort of argp
          // is implied by combination of static and runtime checks
          matchExpr(fe, fp.asInstanceOf, subst)
            .flatMap(subst => matchExpr(arge, argp.asInstanceOf, subst))

        case (Abs(ve, fe), Abs(vp, fp)) =>
          val freshVar = ve.freshRename(Seq(fe, fp))
          matchExpr(using ctx.withBound(freshVar))(
            fe.substitute(ve := freshVar),
            fp.substitute(vp := freshVar),
            subst
          ).filterNot(_.substitutes(freshVar))

        case _ => None

  
  sealed trait RewriteRule:
    type Base
    
    def l: Expr[Base]
    
    def r: Expr[Base]
    
    /**
     * Flip this rewrite rule
     */
    def swap: RewriteRule
    
    /** 
     * The trivial hypothesis step that can be used as a source for this rewrite 
     */
    def source(using lib: Library, proof: lib.Proof): proof.Fact =
      val form = toFormula
      lib.have(using proof)(form |- form) by SimpleDeducedSteps.Restate
    
    /**
      * Reduce this rewrite rule to a formula representing the equivalence.
      */
    def toFormula: Expr[Formula]
    
    /**
      * The sort of the terms in this rewrite rule.
      */
    def sort: K.Sort = l.sort
  

  case class TermRewriteRule(l: Expr[Term], r: Expr[Term]) extends RewriteRule:
    type Base = Term
    def swap: TermRewriteRule = TermRewriteRule(r, l)
    def toFormula: Expr[Formula] = l === r

  case class FormulaRewriteRule(l: Expr[Formula], r: Expr[Formula]) extends RewriteRule:
    type Base = Formula
    def swap: FormulaRewriteRule = FormulaRewriteRule(r, l)
    def toFormula: Expr[Formula] = l <=> r

  case class InstantiatedRewriteRule(rule: RewriteRule, subst: Substitution) extends RewriteRule:
    type Base = rule.Base
    def l: Expr[rule.Base] = rule.l.substitute(subst.asSubstPair*)
    def r: Expr[rule.Base] = rule.r.substitute(subst.asSubstPair*)
    def toFormula: Expr[Formula] = rule.toFormula.substitute(subst.asSubstPair*)
    def swap: RewriteRule = InstantiatedRewriteRule(rule.swap, subst)

  
  /**
    * Given a single *free* rewrite rule, checks whether it rewrite `from` to
    * `to` under this context. If the rewrite succeeds, returns the rule and
    * the instantiation of the rule corresponding to the rewrite step.
    *
    * @param from term to rewrite from
    * @param to term to rewrite into
    * @param rule *free* rewrite rule to use
    */
  private def rewriteOneWithFree[A](from: Expr[A], to: Expr[A], rule: RewriteRule {type Base = A}): Option[InstantiatedRewriteRule] =
    val ctx = RewriteContext.empty
    // attempt to rewrite with all bound variables discarded
    rewriteOneWith(using ctx)(from, to, rule)

  /**
    * Given a single rewrite rule, checks whether it rewrite `from` to `to`
    * under this context. The rewrite rule is considered *confined* by the
    * context. See [[rewriteOneWithFree]] for free rules. If the rewrite
    * succeeds, returns the rule and the instantiation of the rule
    * corresponding to the rewrite step.
    *
    * @param ctx (implicit) context to rewrite under
    * @param from term to rewrite from
    * @param to term to rewrite into
    * @param rule *free* rewrite rule to use
    */
  private def rewriteOneWith[A](using ctx: RewriteContext)(from: Expr[A], to: Expr[A], rule: RewriteRule {type Base = A}): Option[InstantiatedRewriteRule] =
      val (l: Expr[A], r: Expr[A]) = (rule.l, rule.r)
      // match the left side
      matchExpr(l, from, Substitution.empty)
        // based on this partial substitution, try to match the right side
        // note: given that first match succeeded, any extension of it is still a successful matcher for l -> from
        .flatMap(partialSubst => matchExpr(r, to, partialSubst))
        // if succeeded, pair the rule together and ship out
        .map(finalSubst => InstantiatedRewriteRule(rule, finalSubst)) 

  /**
    * Tries to find a *top-level* rewrite from `from` to `to` using the
    * rewrite rules in the implicit context. The rewrite rule unifying the two
    * terms is returned if one exists.
    * 
    * @param from term to rewrite from
    * @param to term to rewrite into
    */
  private def rewriteOne[A]
    (using ctx: RewriteContext)
    (from: Expr[A], to: Expr[A]): Option[InstantiatedRewriteRule] =
      // rule sort is runtime checked
      lazy val confinedRewrite = ctx.confinedRules
                                  .filter(_.sort == from.sort)
                                  .collectFirstDefined(rule => rewriteOneWith(from, to, rule.asInstanceOf))
      lazy val freeRewrite      = ctx.freeRules
                                  .filter(_.sort == from.sort)
                                  .collectFirstDefined(rule => rewriteOneWithFree(from, to, rule.asInstanceOf))
    
      // confined rules take precedence
      // local rewrites are more likely to succeed than global ones
      // (anecdotally) :)
      confinedRewrite.orElse(freeRewrite)

  case class RewriteResult[A](ctx: RewriteContext, usedRules: Set[InstantiatedRewriteRule], context: Expr[A]):
    def toLeft: Expr[A] = 
      context.substitute((vars `lazyZip` rules.map(_.l)).map((v, e) => v := e.asInstanceOf)*)
    def toRight: Expr[A] = 
      context.substitute((vars `lazyZip` rules.map(_.r)).map((v, e) => v := e.asInstanceOf)*)
    def vars: Seq[Variable[?]] = usedRules.map(ctx.representativeVariable).toSeq
    def lambda: Expr[A] = context
    def rules: Set[InstantiatedRewriteRule] = usedRules
    def substitutes(v: Variable[?]): Boolean =
      usedRules.exists(_.subst.substitutes(v))

    // invariant:
    // require( (vars `zip` rules).forall((v, e) => v.Sort == rule.Base ) ) // equality is over types

  type FormulaRewriteResult = RewriteResult[Formula]

  def rewrite[A](using ctx: RewriteContext)(from: Expr[A], to: Expr[A]): Option[RewriteResult[A]] =
    lazy val rule = rewriteOne(from, to)

    if eq(from, to) then
      Some(RewriteResult(ctx, Set.empty, from))
    else if rule.isDefined then
      val irule = rule.get
      Some(RewriteResult(ctx, Set(irule), ctx.representativeVariable(irule).asInstanceOf))
    else 
      (from, to) match 
        case (App(fe, arge), App(fp, argp)) if fe.sort == fp.sort =>
          lazy val fun = rewrite(fe, fp.asInstanceOf)
          lazy val arg = rewrite(arge, argp.asInstanceOf)

          for 
            f <- fun
            a <- arg
          yield RewriteResult(ctx, f.rules ++ a.rules, f.context #@ a.context)

        case (Abs(ve, fe), Abs(vp, fp)) =>
          val freshVar = ve.freshRename(Seq(fe, fp))
          rewrite(fe.substitute(ve := freshVar), fp.substitute(vp := freshVar))
            .filterNot(_.substitutes(freshVar))
            .map:
              case RewriteResult(c, r, e) => 
                RewriteResult(c, r, Abs(freshVar, e))
        case _ => None

end UnificationUtils

// object UnificationUtils {
/*
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
      freeFormulaRules: Seq[(Expr[Formula], Expr[Formula])] = Seq.empty,
      freeTermRules: Seq[(Expr[Term], Expr[Term])] = Seq.empty,
      confinedFormulaRules: Seq[(Expr[Formula], Expr[Formula])] = Seq.empty,
      confinedTermRules: Seq[(Expr[Term], Expr[Term])] = Seq.empty,
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

  type TermSubstitution = Map[Variable, Expr[Term]]
  val TermSubstitution = Map // don't abuse pls O.o

  type FormulaSubstitution = Map[VariableFormula, Expr[Formula]]
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
  def matchTerm(reference: Expr[Term], template: Expr[Term], takenVariables: Iterable[Variable] = Iterable.empty): Option[TermSubstitution] = {
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
 * @param substitution currently accumulated substitutions to variables
 * @return substitution (Option) from variables to terms. `None` if a
 * substitution does not exist.
 */
  private def matchTermRecursive(using context: RewriteContext)(reference: Expr[Term], template: Expr[Term], substitution: TermSubstitution): Option[TermSubstitution] =
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
      reference: Expr[Formula],
      template: Expr[Formula],
      takenTermVariables: Iterable[Variable] = Iterable.empty,
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
 * @param formulaSubstitution currently accumulated substitutions to formula variables
 * @param termSubstitution currently accumulated substitutions to term variables
 * @return substitution pair (Option) from formula variables to formulas, and
 * variables to terms. `None` if a substitution does not exist.
 */
  private def matchFormulaRecursive(using
      context: RewriteContext
  )(reference: Expr[Formula], template: Expr[Formula], formulaSubstitution: FormulaSubstitution, termSubstitution: TermSubstitution): Option[(FormulaSubstitution, TermSubstitution)] = {
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

        case (AppliedConnector(labelR, argsR), AppliedConnector(labelT, argsT)) if labelR == labelT =>
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

        case (AppliedPredicate(labelR, argsR), AppliedPredicate(labelT, argsT)) if labelR == labelT =>
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
  type TermRule = ((Expr[Term], Expr[Term]), TermSubstitution)

  /**
 * A formula rewrite rule (`l -> r`) with an accompanying instantiation,
 * given by a formula and a term substitution.
 *
 * @example A rule without any instantiation would be `((l -> r),
 * FormulaSubstitution.empty)`.
 * @example `((P(x) \/ Q -> Q /\ R(x)), Map(Q -> A \/ B, x -> f(t)))`
 */
  type FormulaRule = ((Expr[Formula], Expr[Formula]), (FormulaSubstitution, TermSubstitution))

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
      body: Expr[Term]
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
      body: Expr[Formula]
  ) {

    /**
 * **Unsafe** conversion to a term lambda, discarding rule and formula information
 *
 * Use if **know that only term rewrites were applied**.
 */
    def toLambdaTF: LambdaExpression[Expr[Term], Expr[Formula], ?] = LambdaExpression(termRules.map(_._1), body, termRules.size)

    /**
 * **Unsafe** conversion to a formula lambda, discarding rule and term information
 *
 * Use if **know that only formula rewrites were applied**.
 */
    def toLambdaFF: LambdaExpression[Expr[Formula], Expr[Formula], ?] = LambdaExpression(formulaRules.map(_._1), body, formulaRules.size)
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
  private def canRewrite(using context: RewriteContext)(first: Expr[Term], second: Expr[Term], rule: (Expr[Term], Expr[Term])): Option[TermSubstitution] =
    matchTermRecursive(termRewriteConnector(first, second), termRewriteConnector(rule._1, rule._2), TermSubstitution.empty)

  /**
 * Decides whether a formula `first` be rewritten into `second` at the top
 * level using the provided rewrite rule (with instantiation). Produces the
 * instantiation as output, if one exists.
 *
 * Reduces to matching using [[matchFormulaRecursive]].
 */
  private def canRewrite(using context: RewriteContext)(first: Expr[Formula], second: Expr[Formula], rule: (Expr[Formula], Expr[Formula])): Option[(FormulaSubstitution, TermSubstitution)] =
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
      first: Expr[Term],
      second: Expr[Term],
      freeTermRules: Seq[(Expr[Term], Expr[Term])],
      confinedTermRules: Seq[(Expr[Term], Expr[Term])] = Seq.empty,
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
  private def getContextRecursive(using context: RewriteContext)(first: Expr[Term], second: Expr[Term]): Option[TermRewriteLambda] = {
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
        val body = first.label.applySeq(retrieved.map(_.body))
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
      first: Expr[Formula],
      second: Expr[Formula],
      freeTermRules: Seq[(Expr[Term], Expr[Term])] = Seq.empty,
      freeFormulaRules: Seq[(Expr[Formula], Expr[Formula])] = Seq.empty,
      confinedTermRules: Seq[(Expr[Term], Expr[Term])] = Seq.empty,
      takenTermVariables: Set[Variable] = Set.empty,
      confinedFormulaRules: Seq[(Expr[Formula], Expr[Formula])] = Seq.empty,
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
      first: Seq[Expr[Formula]],
      second: Seq[Expr[Formula]],
      freeTermRules: Seq[(Expr[Term], Expr[Term])],
      freeFormulaRules: Seq[(Expr[Formula], Expr[Formula])],
      confinedTermRules: Seq[(Expr[Term], Expr[Term])] = Seq.empty,
      takenTermVariables: Set[Variable] = Set.empty,
      confinedFormulaRules: Seq[(Expr[Formula], Expr[Formula])] = Seq.empty,
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
  private def getContextRecursive(using context: RewriteContext)(first: Expr[Formula], second: Expr[Formula]): Option[FormulaRewriteLambda] = {
    // check if there exists a substitution
    lazy val validSubstitution =
      context.confinedFormulaRules
        .getFirst { (l: Expr[Formula], r: Expr[Formula]) =>
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

        case (AppliedConnector(labelF, argsF), AppliedConnector(labelS, argsS)) =>
          if (argsF.length != argsS.length)
            // quick discard
            None
          else {
            // recursively check inner formulas
            val innerSubstitutions = (argsF zip argsS).map(arg => getContextRecursive(using context)(arg._1, arg._2))

            if (innerSubstitutions.exists(_.isEmpty)) None
            else {
              val retrieved = innerSubstitutions.map(_.get)
              val body = AppliedConnector(labelF, retrieved.map(_.body))
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

        case (AppliedPredicate(labelF, argsF), AppliedPredicate(labelS, argsS)) =>
          if (argsF.length != argsS.length)
            // quick discard
            None
          else {
            // our arguments are terms, get contexts from them recursively
            val innerSubstitutions = (argsF zip argsS).map(arg => getContextRecursive(using context)(arg._1, arg._2))

            if (innerSubstitutions.exists(_.isEmpty)) None
            else {
              val retrieved = innerSubstitutions.map(_.get)
              val body = AppliedPredicate(labelF, retrieved.map(_.body))
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
 */
// }
