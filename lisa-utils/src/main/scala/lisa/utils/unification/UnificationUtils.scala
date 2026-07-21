package lisa.utils.unification

import lisa.utils.K
import lisa.utils.collection.Extensions.{*, given}
import lisa.utils.collection.{VecSet => Set}
import lisa.utils.fol.FOL
import lisa.utils.fol.FOL.{_, given}
import lisa.utils.prooflib.{BasicStep, Library, Thm}

import scala.collection.mutable

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
      confinedRules: Set[RewriteRule]
  ):
    // when a context is constructed, update the global ID counter to make sure
    // we aren't conflicting with variable names in the rewrite rules
    RewriteContext.updateIDCounts(this)

    private val representativeCache = mutable.HashMap.empty[InstantiatedRewriteRule, Variable[?]]

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

    def representativeVariable(rule: InstantiatedRewriteRule): Variable[?] =
      representativeCache.getOrElseUpdate(rule, __representativeVariable(rule))

    private def __representativeVariable(rule: InstantiatedRewriteRule): Variable[?] =
      val id = RewriteContext.freshRepresentative
      rule.rule match
        case TermRewriteRule(_, _) => Variable[Ind](id)
        case FormulaRewriteRule(_, _) => Variable[Prop](id)
        case GenericRewriteRule(l, _) => variable(id, l.sort)
        // should not happen under intended use, but why not:
        // deconstruct recursively for completeness
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
      def nextIDCount(): Int =
        current += 1
        current

    import IDCounter.{reprName, setIDCountTo, nextIDCount}

    private def freshRepresentative: Identifier =
      Identifier(reprName, nextIDCount())

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
  case class Substitution private (
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
     * Checks whether this substitution is empty.
     */
    def isEmpty: Boolean =
      assignments.isEmpty

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
    def source(using lib: Library, file: sourcecode.File, line: sourcecode.Line): Thm =
      val form = toFormula
      BasicStep.Hypothesis(form |- form).destruct._1

    /**
     * Reduce this rewrite rule to a formula representing the equivalence.
     */
    def toFormula: Expr[Prop]

    /**
     * The sort of the terms in this rewrite rule.
     */
    def sort: K.Sort = l.sort

  case class TermRewriteRule(l: Expr[Ind], r: Expr[Ind]) extends RewriteRule:
    type Base = Ind
    def swap: TermRewriteRule = TermRewriteRule(r, l)
    def toFormula: Expr[Prop] = l === r

  case class FormulaRewriteRule(l: Expr[Prop], r: Expr[Prop]) extends RewriteRule:
    type Base = Prop
    def swap: FormulaRewriteRule = FormulaRewriteRule(r, l)
    def toFormula: Expr[Prop] = l <=> r

  /**
   * Generic rewrite rule for higher-order heads, mainly produced from lifted
   * equalities such as ∀x. f(x) = g(x).
   */
  case class GenericRewriteRule[S](l: Expr[S], r: Expr[S]) extends RewriteRule:
    type Base = S
    def swap: GenericRewriteRule[S] = GenericRewriteRule(r, l)
    def toFormula: Expr[Prop] = makeEq(l, r)

  case class InstantiatedRewriteRule(rule: RewriteRule, subst: Substitution) extends RewriteRule:
    type Base = rule.Base
    def l: Expr[rule.Base] = rule.l.substitute(subst.asSubstPair*)
    def r: Expr[rule.Base] = rule.r.substitute(subst.asSubstPair*)
    def toFormula: Expr[Prop] = rule.toFormula.substitute(subst.asSubstPair*)
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
  private def rewriteOneWithFree[A](from: Expr[A], to: Expr[A], rule: RewriteRule { type Base = A }): Option[InstantiatedRewriteRule] =
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
  private def rewriteOneWith[A](using ctx: RewriteContext)(from: Expr[A], to: Expr[A], rule: RewriteRule { type Base = A }): Option[InstantiatedRewriteRule] =
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
  private def rewriteOne[A](using ctx: RewriteContext)(from: Expr[A], to: Expr[A]): Option[InstantiatedRewriteRule] =
    // rule sort is runtime checked
    lazy val confinedRewrite = ctx.confinedRules
      .filter(_.sort == from.sort)
      .collectFirstDefined(rule => rewriteOneWith(from, to, rule.asInstanceOf))
    lazy val freeRewrite = ctx.freeRules
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

  type FormulaRewriteResult = RewriteResult[Prop]

  def rewrite[A](using ctx: RewriteContext)(from: Expr[A], to: Expr[A]): Option[RewriteResult[A]] =
    lazy val rule = rewriteOne(from, to)

    if eq(from, to) then Some(RewriteResult(ctx, Set.empty, from))
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

  /** Keeps the first occurrence of each instantiated rewrite rule. */
  def distinctRules(rules: Iterable[InstantiatedRewriteRule]): Vector[InstantiatedRewriteRule] =
    val seen = mutable.LinkedHashSet.empty[InstantiatedRewriteRule]
    val out = Vector.newBuilder[InstantiatedRewriteRule]
    rules.foreach: rule =>
      if seen.add(rule) then out += rule
    out.result()

  /** Matches every base formula to some target formula by rewriting. */
  def rewritingPairs(using ctx: RewriteContext)(base: scala.collection.immutable.Set[Expr[Prop]], target: scala.collection.immutable.Set[Expr[Prop]]): Option[Seq[FormulaRewriteResult]] =
    base.iterator
      .map(formula => target.iterator.collectFirstDefined(target => rewrite(betaReduce(formula), betaReduce(target))))
      .toOptionSeq
