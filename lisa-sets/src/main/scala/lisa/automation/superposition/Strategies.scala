package lisa.automation.superposition

import lisa.automation.clausification.Clausification
import Core.WeightScheme

/**
 * A single prover **strategy**: one point in the search-heuristic parameter space — the axes E and Vampire vary
 * across their CASC schedules (see [[PortfolioStrategy.md]]). A CASC entry runs several of these **in parallel**
 * (one per core, first refutation wins). Only the *search* knobs live here; the per-call limits (`maxGiven`,
 * `maxMillis`), the goal-clause set, and equality auto-detection are supplied at solve time.
 *
 * `ageRatio ≥ 1` together with a BG-complete `selection` ([[LiteralSelection.Complete]] /
 * [[LiteralSelection.FirstNegative]]) keeps the strategy refutation-complete; [[LiteralSelection.BestLiteral]]
 * trades completeness for early speed.
 */
case class Strategy(
    name: String,
    ageRatio: Int,                       // clause-selection age:weight ratio (age slice ⇒ fairness ⇒ completeness)
    weightRatio: Int,
    selection: LiteralSelection,         // literal selection
    precedence: PrecedenceScheme,        // KBO symbol-precedence generation
    weightScheme: WeightScheme,          // KBO symbol-weight generation
    nonGoalWeightCoefficient: Int,       // goal-directed selection (Vampire's nongoal_weight_coefficient)
    forwardSubsumptionResolution: Boolean = false,
    backwardSubsumptionResolution: Boolean = false,
    condensation: Boolean = false,
    sine: Option[SineConfig] = None,     // SInE axiom selection (preprocessing, before clausification; None = off)
    orthologic: Boolean = false):        // replace each axiom/¬conjecture by its orthologic normal form
                                         // (`reducedNNFForm`, one step each) after negating the conjecture, before naming/clausification

  /** Run this strategy on an already-clausal `problem` to a raw [[Bridge.Outcome]] (no kernel proof). `goal` =
   *  indices of the negated-conjecture clauses (for goal-directed selection). */
  def solveOutcome(problem: Clausification.Problem, maxMillis: Long = Long.MaxValue, maxGiven: Int = Int.MaxValue, goal: Set[Int] = Set.empty): Bridge.Outcome =
    Clausal.solveOutcome(
      problem, maxGiven = maxGiven, maxMillis = maxMillis, goal = goal,
      ageRatio = ageRatio, weightRatio = weightRatio, nonGoalWeightCoefficient = nonGoalWeightCoefficient,
      selection = selection, weightScheme = weightScheme, precedenceScheme = precedence,
      forwardSubsumptionResolution = forwardSubsumptionResolution,
      backwardSubsumptionResolution = backwardSubsumptionResolution, condensation = condensation
    )

object Strategy:
  import LiteralSelection.{Complete, BestLiteral, FirstNegative}

  // SInE is active in seven of the eight strategies, at *varied* tolerance/depth for portfolio diversity. Even
  // where active it fires only if [[SinePolicy]]'s gates pass on the actual problem (large + genuinely prunable);
  // otherwise the strategy runs unfiltered. #1 `balanced` carries no filter — the unfiltered completeness /
  // Satisfiable-verdict backstop. The tolerances below are the tunable "gate-3 aggression" knob, chosen from
  // Vampire's CASC band (tol ∈ {5,3,2,1.5} — the values that dominate its schedule; higher = keeps more =
  // safer; depth ∈ {0=∞,1,2,3}) and kept deliberately conservative given we can't fully calibrate.

  /** #1 balanced champion — 1:1, complete selection, inv-frequency precedence, goal-biased. The default, and the
   *  one strategy that is **never** SInE-filtered: the completeness / (Counter)Satisfiable-verdict backstop. */
  val balanced = Strategy("balanced",
    ageRatio = 1, weightRatio = 1, selection = Complete, precedence = PrecedenceScheme.InvFrequency, weightScheme = WeightScheme.Const, nonGoalWeightCoefficient = 10)

  /** #2 weight-greedy — weight-heavy selection (awr 1:16) + incomplete best-literal: speed over fairness.
   *  Δ balanced: age:weight, literal selection. */
  val weightGreedy = Strategy("weight-greedy",
    ageRatio = 1, weightRatio = 16, selection = BestLiteral, precedence = PrecedenceScheme.InvFrequency, weightScheme = WeightScheme.Const, nonGoalWeightCoefficient = 10,
    sine = Some(SineConfig(tolerance = 1.5, depth = 2)))

  /** #3 age-fair — age-heavy (awr 8:1) + no goal bias (nwc 1): the fairest / most complete config.
   *  Δ balanced: age:weight, nwc. Orthologic normalisation on. */
  val ageFair = Strategy("age-fair",
    ageRatio = 8, weightRatio = 1, selection = Complete, precedence = PrecedenceScheme.InvFrequency, weightScheme = WeightScheme.Const, nonGoalWeightCoefficient = 1,
    sine = Some(SineConfig(tolerance = 5.0, depth = 0)), orthologic = true)

  /** #4 occurrence — occurrence precedence (Vampire's single most common) + moderately weighty (awr 1:4).
   *  Δ balanced: precedence, age:weight. Orthologic normalisation on. */
  val occurrence = Strategy("occurrence",
    ageRatio = 1, weightRatio = 4, selection = Complete, precedence = PrecedenceScheme.Occurrence, weightScheme = WeightScheme.Const, nonGoalWeightCoefficient = 10,
    sine = Some(SineConfig(tolerance = 3.0, depth = 0)), orthologic = true)

  /** #5 equational — arity precedence + arity KBO weights: a distinct term ordering, for rewriting problems.
   *  Δ balanced: precedence, weight scheme. */
  val equational = Strategy("equational",
    ageRatio = 1, weightRatio = 1, selection = Complete, precedence = PrecedenceScheme.Arity, weightScheme = WeightScheme.Arity, nonGoalWeightCoefficient = 10,
    sine = Some(SineConfig(tolerance = 3.0, depth = 3)))

  /** #6 unary-redundancy — unary-first precedence + full simplification (subsumption-resolution + condensation).
   *  Δ balanced: precedence, simplification. Orthologic normalisation on. */
  val unaryRedundancy = Strategy("unary-redundancy",
    ageRatio = 1, weightRatio = 1, selection = Complete, precedence = PrecedenceScheme.UnaryFirst, weightScheme = WeightScheme.Const, nonGoalWeightCoefficient = 10,
    forwardSubsumptionResolution = true, backwardSubsumptionResolution = true, condensation = true,
    sine = Some(SineConfig(tolerance = 2.0, depth = 0)), orthologic = true)

  /** #7 subsumption-light — light goal bias (nwc 3) + full simplification.
   *  Δ balanced: nwc, simplification. */
  val subsumptionLight = Strategy("subsumption-light",
    ageRatio = 1, weightRatio = 1, selection = Complete, precedence = PrecedenceScheme.InvFrequency, weightScheme = WeightScheme.Const, nonGoalWeightCoefficient = 3,
    forwardSubsumptionResolution = true, backwardSubsumptionResolution = true, condensation = true,
    sine = Some(SineConfig(tolerance = 2.0, depth = 3)))

  /** #8 first-negative — first-negative literal selection + moderate goal bias (nwc 5).
   *  Δ balanced: literal selection, nwc. Orthologic normalisation on. */
  val firstNegative = Strategy("first-negative",
    ageRatio = 1, weightRatio = 1, selection = FirstNegative, precedence = PrecedenceScheme.InvFrequency, weightScheme = WeightScheme.Const, nonGoalWeightCoefficient = 5,
    sine = Some(SineConfig(tolerance = 1.5, depth = 1)), orthologic = true)

  /** The default portfolio — eight strategies, one per core, run independently (first refutation wins). Each of
   *  #2–#8 differs from #1 `balanced` in exactly two search knobs (SInE excluded) for even coverage of the
   *  configuration space; seven carry a SInE filter at varied tolerance (self-gated per invocation by
   *  [[SinePolicy]]), while `balanced` runs unfiltered as the completeness / (Counter)Satisfiable-verdict backstop. */
  val portfolio: Seq[Strategy] =
    Seq(balanced, weightGreedy, ageFair, occurrence, equational, unaryRedundancy, subsumptionLight, firstNegative)

  /** Look a strategy up by its [[Strategy.name]] (for the CASC launcher's `--strategy` flag). */
  def byName(name: String): Option[Strategy] = portfolio.find(_.name == name)
