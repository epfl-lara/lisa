package lisa.automation.superposition

import lisa.automation.clausification.Clausification
import Core.WeightScheme
import lisa.automation.superposition.ordering.*

/** One point in the search parameter space, over the axes E and Vampire vary across their competition
  * schedules. Several run in parallel and the first refutation wins. Only the search parameters live here; the
  * per-call limits, the goal clauses and equality detection are supplied at solve time.
  *
  * A strategy is refutation-complete when its age ratio is at least one and its selection is
  * [[LiteralSelection.Complete]]. The others trade completeness for speed and are safe only because a complete
  * strategy runs alongside them. */
case class Strategy(
    name: String,
    opts: SearchOptions,                 // every search knob; see [[SearchOptions]]
    sine: Option[SineConfig] = None,     // SInE axiom selection (preprocessing, before clausification; None = off)
    orthologic: Boolean = false):        // replace each axiom/¬conjecture by its orthologic normal form
                                         // (`reducedNNFForm`, one step each) after negating the conjecture, before naming/clausification

  /** Run this strategy on an already-clausal `problem` to a raw [[Bridge.Outcome]] (no kernel proof). `goal` =
   *  indices of the negated-conjecture clauses (for goal-directed selection). */
  def solveOutcome(problem: Clausification.Problem, maxMillis: Long = Long.MaxValue, maxGiven: Int = Int.MaxValue, goal: Set[Int] = Set.empty): Bridge.Outcome =
    Clausal.solveOutcome(problem, maxGiven = maxGiven, maxMillis = maxMillis, opts = opts, goal = goal)

object Strategy:
  import LiteralSelection.{Complete, BestLiteral, FirstNegative}

  // SInE is active in seven of the eight strategies, at *varied* tolerance/depth for portfolio diversity. Even
  // where active it fires only if [[Sine.shouldFilter]]'s gates pass on the actual problem (large + genuinely prunable);
  // otherwise the strategy runs unfiltered (#1 `balanced` carries no filter at all). The tolerances below are
  // the tunable "gate-3 aggression" knob, chosen from
  // Vampire's CASC band (tol ∈ {5,3,2,1.5}, the values that dominate its schedule; higher = keeps more =
  // safer; depth ∈ {0=∞,1,2,3}) and kept deliberately conservative given we can't fully calibrate.

  /** The portfolio's shared baseline. It is the engine default **except** that general subsumption resolution
    * is pinned off, which is what makes "full simplification" a real axis for #6/#7 rather than a no-op. The
    * engine default has SR on ([[SearchOptions.forwardSubsumptionResolution]]) and the portfolio has never been
    * re-derived against that, so pinning it off here is what keeps these eight strategies the eight that were
    * actually measured. */
  private val base = SearchOptions(forwardSubsumptionResolution = false, backwardSubsumptionResolution = false)

  /** #1 balanced champion: 1:1, complete selection, inv-frequency precedence, goal-biased. The portfolio's
   *  first slice and the one strategy that is **never** SInE-filtered: the completeness /
   *  (Counter)Satisfiable-verdict backstop. Not the same as the *engine* default `SearchOptions()`, which it
   *  differs from in exactly one knob; see [[base]]. */
  val balanced = Strategy("balanced", base)

  /** #2 weight-greedy: weight-heavy selection (awr 1:16) + incomplete best-literal: speed over fairness.
   *  Δ balanced: age:weight, literal selection. */
  val weightGreedy = Strategy("weight-greedy",
    base.copy(weightRatio = 16, selection = BestLiteral),
    sine = Some(SineConfig(tolerance = 1.5, depth = 2)))

  /** #3 age-fair: age-heavy (awr 8:1) + no goal bias (nwc 1): the fairest / most complete config.
   *  Δ balanced: age:weight, nwc. Orthologic normalisation on. */
  val ageFair = Strategy("age-fair",
    base.copy(ageRatio = 8, nonGoalWeightCoefficient = 1),
    sine = Some(SineConfig(tolerance = 5.0, depth = 0)), orthologic = true)

  /** #4 occurrence: occurrence precedence (Vampire's single most common) + moderately weighty (awr 1:4).
   *  Δ balanced: precedence, age:weight. Orthologic normalisation on. */
  val occurrence = Strategy("occurrence",
    base.copy(weightRatio = 4, precedenceScheme = PrecedenceScheme.Occurrence),
    sine = Some(SineConfig(tolerance = 3.0, depth = 0)), orthologic = true)

  /** #5 equational: arity precedence + arity KBO weights: a distinct term ordering, for rewriting problems.
   *  Δ balanced: precedence, weight scheme. */
  val equational = Strategy("equational",
    base.copy(precedenceScheme = PrecedenceScheme.Arity, weightScheme = WeightScheme.Arity),
    sine = Some(SineConfig(tolerance = 3.0, depth = 3)))

  /** #6 unary-redundancy: unary-first precedence + full simplification (subsumption-resolution + condensation).
   *  Δ balanced: precedence, simplification. Orthologic normalisation on. */
  val unaryRedundancy = Strategy("unary-redundancy",
    base.copy(precedenceScheme = PrecedenceScheme.UnaryFirst,
      forwardSubsumptionResolution = true, backwardSubsumptionResolution = true, condensation = true),
    sine = Some(SineConfig(tolerance = 2.0, depth = 0)), orthologic = true)

  /** #7 subsumption-light: light goal bias (nwc 3) + full simplification.
   *  Δ balanced: nwc, simplification. */
  val subsumptionLight = Strategy("subsumption-light",
    base.copy(nonGoalWeightCoefficient = 3,
      forwardSubsumptionResolution = true, backwardSubsumptionResolution = true, condensation = true),
    sine = Some(SineConfig(tolerance = 2.0, depth = 3)))

  /** #8 first-negative: first-negative literal selection + moderate goal bias (nwc 5).
   *  Δ balanced: literal selection, nwc. Orthologic normalisation on. */
  val firstNegative = Strategy("first-negative",
    base.copy(selection = FirstNegative, nonGoalWeightCoefficient = 5),
    sine = Some(SineConfig(tolerance = 1.5, depth = 1)), orthologic = true)

  /** The default portfolio: eight strategies, one per core, run independently (first refutation wins). Each of
   *  #2 to #8 each differ from #1 `balanced` in exactly two search knobs (SInE excluded) for even coverage of the
   *  configuration space; seven carry a SInE filter at varied tolerance (self-gated per invocation by
   *  [[Sine.shouldFilter]]); `balanced` runs unfiltered. */
  val portfolio: Seq[Strategy] =
    Seq(balanced, weightGreedy, ageFair, occurrence, equational, unaryRedundancy, subsumptionLight, firstNegative)

  def byName(name: String): Option[Strategy] = portfolio.find(_.name == name)
