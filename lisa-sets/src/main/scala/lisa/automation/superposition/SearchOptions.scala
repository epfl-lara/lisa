package lisa.automation.superposition

import Core.WeightScheme
import lisa.automation.superposition.ordering.*

/**
 * Every parameter of the search, in one value that each layer forwards whole rather than re-declaring a subset
 * of it, so that a parameter added here reaches all of them and none can pin one to a default of its own.
 * The defaults are the shipped configuration, which the benchmark harnesses also default to.
 *
 * Where a default was chosen by ablation the note below gives the counts. They all come from one run, the
 * seed-42 clausal sample of 2026-08-08, and record why the default is what it is rather than a current score.
 * This is their only home in the source; `Simplifier`, `Strategy` and `DiscountTest` point here.
 *
 * @param ageRatio          clause-selection age:weight ratio. An age slice ≥ 1 gives fairness, hence
 *                          completeness; the weight slice gives speed.
 * @param weightRatio       the weight half of the clause selection ratio.
 * @param nonGoalWeightCoefficient
 *                          goal-directed selection: a clause *not*
 *                          derived from the goal has its weight-queue key multiplied by this, so goal-derived
 *                          clauses activate far earlier. No effect if there is no goal clause.
 * @param selection         literal selection. [[LiteralSelection.Complete]] is BG-complete and the default;
 *                          the others are heuristic.
 * @param precedenceScheme  how the KBO symbol precedence is generated from the input signature; see
 *                          [[Precedence]]. `InvFrequency` (frequent symbols small) is the default.
 * @param weightScheme      how KBO symbol `???` is the default.
 * @param forwardSubsumption   discard a new/just-selected clause subsumed by an active one.
 * @param backwardSubsumption  delete active clauses subsumed by the given.
 * @param forwardUnitDeletion  shrink the given by active unit clauses (the unit case of subsumption resolution).
 * @param backwardUnitDeletion shrink active clauses when the given is a unit.
 * @param forwardSubsumptionResolution
 *                          general (multi-literal side) subsumption resolution, forward. On by default.
 * @param backwardSubsumptionResolution the backward direction of the same.
 * @param condensation      replace a new clause by an equivalent shorter factor of itself. Clause-local,
 *                          applied once at creation. Off by default.
 * @param forwardSimplifyAtGeneration
 *                          also forward-simplify freshly *generated* clauses, not just the given at selection.
 *                          Off by default.
 * @param equality          master equality switch. When off, **every** equality-specific part of the loop is
 *                          skipped and the finer switches below have no effect, reducing it to ordered
 *                          resolution and factoring. [[Clausal.refute]] also turns it off when the input contains
 *                          no `=` at all, where the inferences could never fire.
 * @param superposition     the superposition enumeration itself (the heaviest equality inference).
 * @param forwardDemodulation  normal-form the given against the active positive unit equalities.
 * @param backwardDemodulation rewrite active clauses when the given is a new unit equality.
 * @param forwardUnitDeletionIndexThreshold
 *                          unit count at which forward unit deletion switches from scanning the active-unit
 *                          sublist to querying the index. Purely a performance knob.
 * @param factorAfterCheck  drop a factor whose kept literal is no longer KBO-maximal under the unifier. A
 *                          redundancy pruning; omitting it over-approximates, which is sound and complete.
 * @param sine              SInE axiom selection, applied before clausification; `None` disables it. It only
 *                          ever *removes* hypotheses, so it needs no justification in a proof.
 * @param orthologic        replace each hypothesis and the negated conjecture by its orthologic normal form,
 *                          before clausification. Justified by one step per formula when proofs are on.
 * @param maxGiven          given-clause budget for the saturation loop.
 * @param maxMillis         cooperative wall-clock budget for the saturation loop, in milliseconds.
 * @param onStats           receives the loop instrumentation once the search ends. Being a function, it is the
 *                          one field that makes two `SearchOptions` compare unequal for equal settings;
 *                          nothing compares them.
 */
final case class SearchOptions(
    // ── clause selection ──
    ageRatio: Int = 1,
    weightRatio: Int = 1,
    nonGoalWeightCoefficient: Int = 10,
    // ── literal selection and term ordering ──
    selection: LiteralSelection = LiteralSelection.Complete,
    precedenceScheme: PrecedenceScheme = PrecedenceScheme.InvFrequency,
    weightScheme: WeightScheme = WeightScheme.Const,
    // ── simplification ──
    forwardSubsumption: Boolean = true,
    backwardSubsumption: Boolean = true,
    forwardUnitDeletion: Boolean = true,
    backwardUnitDeletion: Boolean = true,
    forwardSubsumptionResolution: Boolean = true,
    backwardSubsumptionResolution: Boolean = true,
    condensation: Boolean = false,
    forwardSimplifyAtGeneration: Boolean = false,
    // ── equality inferences ──
    equality: Boolean = true,
    superposition: Boolean = true,
    forwardDemodulation: Boolean = true,
    backwardDemodulation: Boolean = true,
    // ── term indexing ──
    forwardUnitDeletionIndexThreshold: Int = 16,
    // ── misc ──
    factorAfterCheck: Boolean = false,
    // ── preprocessing (before clausification) ──
    sine: Option[SineConfig] = None,
    orthologic: Boolean = false,
    // ── budgets and instrumentation ──
    maxGiven: Int = Int.MaxValue,
    maxMillis: Long = Long.MaxValue,
    onStats: Discount.LoopStats => Unit = _ => ()):

  // ── derived switches ──────────────────────────────────────────────────────────────────────────────
  //
  // Conjunctions of the flags above that more than one class needs, computed once here so that `Discount`,
  // `ActiveSet` and `Simplifier` cannot derive them differently. Every consumer does `import opts.*`, so they
  // read unqualified. `val`, not `def`: some are read inside the generating loops.

  /** Superposition runs at all: the rule is on *and* equality is not switched off wholesale. */
  val superpositionOn: Boolean = equality && superposition

  /** Forward demodulation runs at all, which also decides whether the demodulator set is maintained. */
  val forwardDemodulationOn: Boolean = equality && forwardDemodulation

  /** Backward demodulation runs at all. */
  val backwardDemodulationOn: Boolean = equality && backwardDemodulation

  /** Whether any subsumption-based simplification runs, and so whether [[ActiveSet]] maintains the
    * feature-vector index and unit sublist. All six flags, not just the two subsumption ones: unit deletion and
    * subsumption resolution query the same index, so `forwardUnitDeletion` alone still needs it built. */
  val subsumptionEnabled: Boolean =
    forwardSubsumption || backwardSubsumption || forwardUnitDeletion || backwardUnitDeletion ||
      forwardSubsumptionResolution || backwardSubsumptionResolution
