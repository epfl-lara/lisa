package lisa.utils.prooflib

import lisa.utils.fol.FOL.*
import lisa.utils.prooflib.Helpers.withParams
import lisa.utils.prooflib.ProofHelpers.{SequentTactic, of}
import lisa.utils.unification.UnificationUtils.*
import sourcecode.File
import sourcecode.Line

object Substitute extends SequentTactic, DerivedFromPremises:
  /**
   * Extracts a raw formula substitution into a `RewriteRule`.
   */
  def extractRule(formula: Expr[Prop]): Option[RewriteRule] =
    def generic(l: Expr[?], r: Expr[?]): Option[RewriteRule] =
      if l.sort == r.sort then Some(GenericRewriteRule(l.asInstanceOf[Expr[Any]], r.asInstanceOf[Expr[Any]])) else None

    formula match
      case l === r => generic(l, r)
      case l <=> r => generic(l, r)
      case _ =>
        Helpers.unliftEquality(formula.underlying).flatMap { case (l, r) =>
          generic(liftExpression(l), liftExpression(r))
        }

  /**
   * Extracts a theorem substitution into a `RewriteRule`.
   */
  def extractRule(thm: Thm): Option[RewriteRule] =
    if thm.right.size == 1 then extractRule(thm.right.head) else None

  /**
   * Checks if a raw substitution input can be used as a rewrite rule (is === or
   * <=>, basically). Lifted equalities are accepted too.
   */
  def validSubstitutionRule(rule: Expr[Prop]): Boolean =
    extractRule(rule).nonEmpty

  /**
   * Checks if a theorem can be used as a rewrite rule.
   */
  def validSubstitutionRule(rule: Thm): Boolean =
    extractRule(rule).nonEmpty

  /**
   * Partitions raw substitution rules into free and confined rules, also
   * creating a source map, mapping each rule to the theorem it was derived
   * from, for proof construction.
   */
  private def partition(using file: File, line: Line)(using library: Library)(
      theoremRules: Seq[Thm],
      formulaRules: Seq[Expr[Prop]]
  ): (Map[RewriteRule, Thm], RewriteContext) =
    var sourceMap = Map.empty[RewriteRule, Thm]
    var ctx = RewriteContext.empty
    theoremRules.foreach: thm =>
      val rule = extractRule(thm).get
      sourceMap += rule -> thm
      sourceMap += rule.swap -> thm
      ctx =
        if thm.isSchema then ctx.withFreeRule(rule).withFreeRule(rule.swap)
        else ctx.withConfinedRule(rule).withConfinedRule(rule.swap)
    formulaRules.foreach: formula =>
      val rule = extractRule(formula).get
      val source = rule.source
      sourceMap += rule -> source
      sourceMap += rule.swap -> source
      ctx = ctx.withConfinedRule(rule).withConfinedRule(rule.swap)
    sourceMap -> ctx

  private def invalid(using file: File, line: Line)(using Library)(conclusion: Sequent, message: String, params: (String, Any)*): ProofJudgement =
    ProofCarrier(Set(SoftError(withParams(message, params*), file, line)), conclusion, None, ())

  private def firstInvalid(conclusion: Sequent, steps: ProofJudgement*)(using file: File, line: Line, library: Library): ProofJudgement =
    steps.find(!_.isValid).getOrElse(invalid(conclusion, "Substitute proof construction failed unexpectedly."))

  private def instantiateSource(using file: File, line: Line)(using library: Library)(source: Thm, rule: InstantiatedRewriteRule): Thm =
    if rule.subst.isEmpty then source else source.of(rule.subst.asSubstPair*)

  private def distinctDischarges(rules: Iterable[InstantiatedRewriteRule]): Vector[InstantiatedRewriteRule] =
    val seen = scala.collection.mutable.LinkedHashSet.empty[Expr[Prop]]
    rules.iterator.filter(rule => seen.add(rule.toFormula)).toVector

  private def cutDischarges(using file: File, line: Line)(using library: Library)(
      conclusion: Sequent,
      start: Thm,
      discharges: Vector[(InstantiatedRewriteRule, Thm)]
  ): ProofJudgement =
    var current = start
    var failure: Option[ProofJudgement] = None
    val iterator = discharges.iterator
    while iterator.hasNext && failure.isEmpty do
      val (rule, source) = iterator.next()
      val formula = rule.toFormula
      val removed = current.statement -<? formula
      val next = removed.copy(left = removed.left ++ source.left)
      val judgement = BasicStep.Cut.withParameters(formula)(source.kernel, current.kernel)(next)
      if judgement.isValid then current = judgement.destruct._1
      else failure = Some(judgement)
    failure.getOrElse:
      val restated = BasicStep.Restate(conclusion, current.kernel)
      if restated.isValid then restated else BasicStep.Weakening(conclusion, current.kernel)

  private def rewriteWithRules(using file: File, line: Line)(using library: Library)(
      conclusion: Sequent,
      premise: Thm,
      theoremRules: Seq[Thm],
      formulaRules: Seq[Expr[Prop]]
  ): ProofJudgement =
    // are all substitution rules actually valid?
    // if not, exit early
    val invalidTheorems = theoremRules.filter(!validSubstitutionRule(_))
    if invalidTheorems.nonEmpty then
      invalid(conclusion, "Substitute theorem rules must prove exactly one equality or equivalence.", "Rules" -> invalidTheorems.map(_.statement))
    else
      val invalidFormulas = formulaRules.filter(!validSubstitutionRule(_))
      if invalidFormulas.nonEmpty then
        invalid(conclusion, "Substitute formula rules must be equalities or equivalences.", "Rules" -> invalidFormulas)
      else
        // metadata:
        // maintain a list of where substitutions come from
        // and categorize them for the rewrite context
        val (sourceMap, prectx) = partition(theoremRules, formulaRules)

        val rewriteCtx = prectx.withBound(premise.left.flatMap(_.freeVars))

        // check whether this rewrite is even possible.
        // if it is, get the context (term with holes) corresponding to the
        // single-step simultaneous rewrite.
        //
        // for each formula in the premise left (resp. right), there must be a
        // corresponding formula in the conclusion left (resp. right) that it
        // can be rewritten into.
        val leftRewrites = rewritingPairs(using rewriteCtx)(premise.left, conclusion.left)
        val rightRewrites = rewritingPairs(using rewriteCtx)(premise.right, conclusion.right)
        if leftRewrites.isEmpty then
          invalid(conclusion, "Could not rewrite LHS of premise into conclusion with given substitutions.", "Premise" -> premise.statement, "Conclusion" -> conclusion)
        else if rightRewrites.isEmpty then
          invalid(conclusion, "Could not rewrite RHS of premise into conclusion with given substitutions.", "Premise" -> premise.statement, "Conclusion" -> conclusion)
        else
          buildProof(conclusion, premise, leftRewrites.get, rightRewrites.get, sourceMap)

  private def buildProof(using file: File, line: Line)(using library: Library)(
      conclusion: Sequent,
      premise: Thm,
      leftRewrites: Seq[FormulaRewriteResult],
      rightRewrites: Seq[FormulaRewriteResult],
      sourceMap: Map[RewriteRule, Thm]
  ): ProofJudgement =
    val leftRules = distinctRules(leftRewrites.flatMap(_.rules))
    val rightRules = distinctRules(rightRewrites.flatMap(_.rules))
    val allRules = distinctDischarges(leftRules ++ rightRules)
    val discharges = allRules.map(rule => rule -> instantiateSource(sourceMap(rule.rule), rule))

    // start proof
    val leftFormulas = leftRules.map(_.toFormula).toSet
    // Reuse the input side: reconstructing it from rewrite contexts is
    // redundant and may choose a different OL-equivalent representative.
    val preLeft = premise.left
    val postLeft = leftRewrites.map(_.toRight).toSet
    val leftCtx = leftRewrites.headOption.map(_.ctx).getOrElse(RewriteContext.empty)
    val leftVars = leftRules.map(leftCtx.representativeVariable)
    val leftLambda = andAllOrTrue(leftRewrites.map(_.lambda))
    val start = andAllOrTrue(premise.left) |- premise.right
    val leftTarget = leftFormulas + andAllOrTrue(postLeft) |- premise.right

    val s1 = BasicStep.Restate(start, premise.kernel)
    if !s1.isValid then s1
    else
      // left rewrites
      val s2 = BasicStep.Restate(andAllOrTrue(preLeft) |- premise.right, s1.destruct._1.kernel)
      val s3 = if s2.isValid then BasicStep.Weakening(leftFormulas + andAllOrTrue(preLeft) |- premise.right, s2.destruct._1.kernel) else s2
      val s4 =
        if s3.isValid then BasicStep.LeftSubstEq.withParameters(leftRules.map(r => r.l -> r.r), leftVars -> leftLambda)(s3.destruct._1.kernel)(leftTarget)
        else s3
      if !s4.isValid then firstInvalid(conclusion, s2, s3, s4)
      else
        val leftThm = s4.destruct._1

        // right rewrites
        val rightFormulas = rightRules.map(_.toFormula).toSet
        val preRight = premise.right
        val postRight = rightRewrites.map(_.toRight).toSet
        val rightCtx = rightRewrites.headOption.map(_.ctx).getOrElse(RewriteContext.empty)
        val rightVars = rightRules.map(rightCtx.representativeVariable)
        val rightLambda = orAllOrFalse(rightRewrites.map(_.lambda))
        val rightStart = leftThm.left |- orAllOrFalse(preRight)
        val rightTarget = rightFormulas ++ leftThm.left |- orAllOrFalse(postRight)

        val r1 = BasicStep.Restate(rightStart, leftThm.kernel)
        val r2 = if r1.isValid then BasicStep.Weakening(rightFormulas ++ leftThm.left |- orAllOrFalse(preRight), r1.destruct._1.kernel) else r1
        val r3 =
          if r2.isValid then BasicStep.RightSubstEq.withParameters(rightRules.map(r => r.l -> r.r), rightVars -> rightLambda)(r2.destruct._1.kernel)(rightTarget)
          else r2
        if !r3.isValid then firstInvalid(conclusion, r1, r2, r3)
        else
          // rewrite to destruct sequent
          val postRewrite = postLeft ++ leftFormulas ++ rightFormulas |- postRight
          val restated = BasicStep.Restate(postRewrite, r3.destruct._1.kernel)
          if !restated.isValid then restated
          // discharge assumptions
          else cutDischarges(conclusion, restated.destruct._1, discharges)

  protected def prove(using file: File, line: Line)(using library: Library)(conclusion: Sequent, premises: Seq[Thm]): ProofJudgement =
    premises match
      case Seq() => Tautology(conclusion)
      case Seq(premise) =>
        val direct = BasicStep.Restate(conclusion, premise.kernel)
        if direct.isValid then direct else Tautology.from(premise)(conclusion)
      case premise +: rules =>
        val direct = BasicStep.Restate(conclusion, premise.kernel)
        if direct.isValid then direct else rewriteWithRules(conclusion, premise, rules, Nil)

  final class WithEqualities(equalities: Seq[Expr[Prop]])(using file: File, line: Line, library: Library) extends ((Sequent, Thm) => ProofJudgement):
    def apply(conclusion: Sequent, lastStep: Thm): ProofJudgement =
      rewriteWithRules(conclusion, lastStep, Nil, equalities)

    def apply(premise: Thm): Sequent => ProofJudgement =
      conclusion => rewriteWithRules(conclusion, premise, Nil, equalities)

  def apply(using file: File, line: Line)(using library: Library)(equality: Expr[Prop], equalities: Expr[Prop]*): WithEqualities =
    WithEqualities(equality +: equalities)
