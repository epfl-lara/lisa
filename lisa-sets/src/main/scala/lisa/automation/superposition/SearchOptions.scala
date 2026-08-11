package lisa.automation.superposition

import Core.WeightScheme

/**
 * Every knob of the saturation search, in one value. It is the '''single declaration''': every layer that can
 * configure a search — the [[Discount]] constructor, [[Bridge.solve]], [[Bridge.solveTPTPProblem]],
 * [[Clausal.solveOutcome]], [[Strategy]] — takes and forwards the whole record rather than re-declaring a
 * subset of the knobs positionally, so a knob added here reaches all of them by construction and no layer can
 * silently pin one to a default of its own.
 *
 * Defaults are the shipped configuration. The benchmark harnesses' own defaults track these deliberately, so
 * a run with no flags measures what actually ships.
 *
 * '''On the measurements quoted below.''' Where a default was chosen by ablation, the `@param` note says which
 * way it went. All such counts come from one run — the seed-42 clausal sample, re-ablated 2026-08-08 — and go
 * stale the moment it is re-run; they are here to record *why* the default is what it is, not as a current
 * score. This is their only home in the source: `Simplifier`, `Strategy` and `DiscountTest` point back here
 * rather than repeating them.
 *
 * @param ageRatio          clause-selection age:weight ratio. An age slice ≥ 1 gives fairness, hence
 *                          completeness; the weight slice gives speed.
 * @param weightRatio       the weight half of that ratio.
 * @param nonGoalWeightCoefficient
 *                          goal-directed selection (Vampire's `nongoal_weight_coefficient`): a clause NOT
 *                          derived from the goal has its weight-queue key multiplied by this, so goal-derived
 *                          clauses activate far earlier. With no goal clauses every clause scales equally ⇒
 *                          no effect. Only the weight queue is biased.
 * @param selection         literal selection. [[LiteralSelection.Complete]] is BG-complete and the default;
 *                          the others are heuristic portfolio slices — see [[LiteralSelection]].
 * @param precedenceScheme  how the KBO symbol precedence is generated from the input signature.
 *                          `InvFrequency` (frequent symbols small) is the default; `Occurrence` is the former
 *                          interning-order baseline. See [[Precedence]].
 * @param weightScheme      how KBO symbol weights are generated. Applied at intern time, since term weights
 *                          are cached at construction — so it must be fixed before any clause is built.
 * @param forwardSubsumption   discard a new/just-selected clause subsumed by an active one.
 * @param backwardSubsumption  delete active clauses subsumed by the given.
 * @param forwardUnitDeletion  shrink the given by active unit clauses (the unit case of subsumption resolution).
 * @param backwardUnitDeletion shrink active clauses when the given is a unit.
 * @param forwardSubsumptionResolution
 *                          general (multi-literal side) subsumption resolution, forward. **On by default**:
 *                          80 refuted vs 74 with it off, strictly monotone. Worth knowing if it is ever
 *                          re-measured — it only pays once retrieval is indexed; while the only path was a
 *                          linear active scan (a match search against every non-subsuming active clause) it
 *                          lost, which is why it was originally off.
 * @param backwardSubsumptionResolution the backward direction of the same.
 * @param condensation      replace a new clause by an equivalent shorter factor of itself. Clause-local (no
 *                          active scan), applied once at creation. **Off by default**: 71 refuted vs 74 — it
 *                          loses 3 and gains none.
 * @param forwardSimplifyAtGeneration
 *                          also forward-simplify freshly *generated* clauses, not just the given at
 *                          selection. Governs forward subsumption *and* forward unit deletion at the
 *                          generation point. **Off by default**: 72 refuted vs 74, losing 2 (`FLD060-4`,
 *                          `GRP130-2.003`) and gaining none. Indexing narrowed the gap from 4 problems to 2
 *                          without closing it, so the losses are not simply retrieval cost.
 * @param equality          master equality switch. When off, **every** equality-specific part of the loop is
 *                          skipped — superposition, equality resolution/factoring, and forward/backward
 *                          demodulation with its upkeep — reducing the loop to ordered resolution + factoring.
 *                          The finer switches below then have no effect. [[Bridge.solve]] additionally turns
 *                          it off automatically when the input contains no `=` at all, where the inferences
 *                          could never fire.
 * @param superposition     the superposition enumeration itself (the heaviest equality inference).
 * @param forwardDemodulation  normal-form the given against the active positive unit equalities.
 * @param backwardDemodulation rewrite active clauses when the given is a new unit equality.
 * @param fingerprintIndexing  find generating-inference partners (superposition and ordinary resolution) via
 *                          fingerprint indices over the active set instead of a linear scan. The index is a
 *                          candidate filter confirmed by real unification, so the inference *set* is
 *                          identical and reconstruction is unchanged; only clause ids and the search
 *                          trajectory differ. Kept as a flag so indexed and linear can be A/B-compared.
 * @param subsumptionIndexing  the same A/B switch for the feature-vector subsumption index.
 * @param demodulationIndexing the same for the perfect discrimination tree used by forward demodulation, and
 *                          the subterm index used by backward demodulation.
 * @param forwardUnitDeletionIndexThreshold
 *                          forward unit deletion has two paths deleting the *same* literals: a direct scan of
 *                          the (small) active-unit sublist, and an indexed variant. The scan has near-zero
 *                          fixed overhead when units are few; the index wins when they are many. Dispatch is
 *                          on this count. Purely a performance knob — either path is a complete candidate set
 *                          verified identically, so verdicts agree.
 * @param factorAfterCheck  drop a factor whose kept literal is no longer KBO-maximal under the unifier. A
 *                          redundancy pruning; omitting it over-approximates, which is sound and complete.
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
    fingerprintIndexing: Boolean = true,
    subsumptionIndexing: Boolean = true,
    demodulationIndexing: Boolean = true,
    forwardUnitDeletionIndexThreshold: Int = 16,
    // ── misc ──
    factorAfterCheck: Boolean = false)
