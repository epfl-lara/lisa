# Phase 2 — Redundancy elimination (simplification), still without equality

**Goal.** Make the reasoning engine *smaller and faster* by deleting and shrinking clauses that
add nothing, rather than only deriving new ones. Phase 1 only ever *grows* the search space
(resolution + factoring + canonicalisation); the benchmark shows the cost — 65/100 problems time
out at 15 s because passive fills with redundant clauses. Phase 2 adds the standard
redundancy-elimination layer: **subsumption** (forward + backward), **subsumption resolution**,
**condensation**, on top of the tautology/duplicate deletion we already have. All of it is sound,
all of it is reconstructible into the kernel, and — crucially — all of it is active in the
**equality-free** fragment.

This document reports what Vampire, E and Prover9 do for non-equality simplification, then proposes
exactly what we should build, in priority order, with the loop integration and proof-reconstruction
plan. The yardstick is `Benchmarks.md` (seed 42: `refuted=35 timeout=65`); Phase 2 succeeds if
`refuted` climbs while `saturated`/`bad_proof` stay 0.

---

## 0. Scope decision up front: demodulation is deferred to Phase 3

`PLAN.md` lists *demodulation* under Phase 2, and the task description repeats it. **Demodulation is
an equality rule** — it rewrites terms using unit equations `l = r` oriented by the term ordering. In
a problem with **no equality literals there are zero demodulators, so demodulation never fires**:
implementing it now is untested dead code, and its supporting machinery (a rewrite/demodulator index,
ordered rewriting, encompassment) is exactly the Phase-3 superposition machinery.

**Recommendation:** keep Phase 2 to the redundancy rules that are *live without equality*
(subsumption, subsumption resolution, condensation), and move demodulation (forward + backward) to
Phase 3, where it lands together with superposition, paramodulation and equality ordering. Phase 2
still builds the foundation demodulation will reuse: the one-sided **matcher**, the
**candidate-filtering** signature, and the **backward-simplification** plumbing in the loop. This is
flagged as an open decision in §10 — it is a roadmap change, so it is the user's call.

Everything below assumes that decision; if demodulation is wanted in Phase 2 anyway, it slots in as a
fourth simplification rule reusing the same plumbing, but with no effect on the current benchmark.

---

## 1. What we already have (Phase 1)

- **Tautology deletion** and **duplicate-literal removal**: `Inference.canonicalize`
  ([Inference.scala:67](Inference.scala#L67)) sorts literals, drops duplicates, and returns `None`
  on a complementary pair `L`/`¬L`. For the non-equality fragment this is the *complete* tautology
  test (equational tautologies `t=t`/congruence are a Phase-3 concern). **Nothing to add here.**
- **The DISCOUNT loop** ([Discount.scala](Discount.scala)): passive = two lazy-deletion queues
  (`byAge`/`byWeight` + `livePassive`), active = a linearly-scanned `ArrayBuffer`. New clauses are
  only canonicalised before entering passive — **no simplification against other clauses yet**. This
  is the hook point for Phase 2.
- **Unification + a backtrackable trail** (`Core.Trail`): two scopes, `save`/`restore`,
  `unify`. Subsumption needs *matching* (one-sided), which the trail does **not** yet provide — that
  is the one new Core primitive (§5).
- **KBO** and **literal selection** — unchanged in Phase 2 (selection/ordering are orthogonal to
  redundancy).

---

## 2. Reference survey (non-equality simplification only)

All three provers structure simplification into three buckets, and we adopt the same vocabulary:

| Bucket | When | Effect | Our analogue |
|---|---|---|---|
| **Immediate / trivial** | clause-local, no other clauses | delete or shrink in place | `canonicalize` (have) + condensation (new) |
| **Forward** | new/given clause vs the **kept** set | delete/shrink *the new clause* | new |
| **Backward** | a just-kept clause vs the **kept** set | delete/shrink *kept clauses* | new |

### Vampire (`othersolvers/vampire/`)
- **Forward subsumption + resolution**: `Inferences/ForwardSubsumptionAndResolution.cpp`, delegating
  to a SAT-based engine `SATSubsumption/SATSubsumptionAndResolution.cpp`. Subsumption is multiset
  literal matching under **one** substitution, encoded as SAT (each `(Lᵢ, Mⱼ)` match is a variable;
  clauses enforce "every base literal matched" + "at-most-one base per instance literal"). It is
  preceded by cheap **pruning**: `|C| ≤ |D|` and the predicate-symbol multiset of `C` must be a
  sub-multiset of `D`. Subsumption *resolution* (one literal of the main clause resolved away) reuses
  the same match set with one negatively-matched literal.
- **Backward** (`BackwardSubsumptionAndResolution.cpp`): when a clause is activated it queries the
  index for instances and deletes/shrinks them. Picks the **heaviest literal** to query (fewest
  candidates).
- **Condensation** (`Condensation.cpp`, `FastCondensation.cpp`): an *immediate* engine — unify two
  literals of `C`, and if the resulting (shorter) clause still subsumes `C`, replace `C`.
- **Immediate engines** (`InferenceEngine.hpp`, `CompositeISE`): `DuplicateLiteralRemovalISE`,
  `TautologyDeletionISE` — run first, clause-local. Order: dup-removal → tautology → … → condensation.
- Candidate finding uses substitution-tree literal indexes (`LiteralSubstitutionTree`,
  `getGeneralizations`/`getInstances`). **That indexing is our Phase 4** — Phase 2 scans linearly.

### E (`othersolvers/eprover/`)
- **Subsumption**: `CLAUSES/ccl_subsumption.c` — `clause_subsumes_clause()` does multiset
  literal-to-literal matching with **backtracking** (`eqn_list_rec_subsume`, a `pick_list[]` of used
  target literals), with early rejection by polarity counts and weight, and an ordering-based prune.
  This recursive backtracking matcher is the model for our (non-SAT) implementation.
- **Feature-vector index** `CLAUSES/ccl_fcvindexing.c`: per-clause integer feature vectors
  (per-symbol pos/neg counts, depths, literal counts); a subsumer must be ≤ the candidate on every
  feature. **The features themselves are a cheap, indexing-free pre-filter we can adopt now** (store a
  small signature on each clause); the *tree* over them is Phase 4.
- **Pipeline** `CONTROL/cco_proofproc.c` (`ProcessClause`) + `cco_forward_contraction.c`: forward
  contraction (tautology, forward subsumption, simplify-reflect) on the given clause before insertion;
  then `eliminate_backward_subsumed_clauses` and unit simplify-reflect on the processed set.
- **Subsumption resolution** = E's **contextual simplify-reflect** (`CLAUSES/ccl_context_sr.c`) plus
  the unit special cases `ClausePositiveSimplifyReflect` / `ClauseNegativeSimplifyReflect`.

### Prover9 / LADR (`othersolvers/prover9/`, `othersolvers/ladr-2026/`)
- **Subsumption** `ladr/subsume.c`: `subsumes()` / `subsume_literals()` — the same one-substitution
  multiset matcher with a trail and backtracking. `forward_subsume*` and `back_subsume` differ only in
  index query direction (generalisation vs instance).
- **Unit deletion** `unit_delete()` / `back_unit_del_by_index()` — the **unit special case of
  subsumption resolution**, and the cheapest, highest-value version of it.
- **Otter vs DISCOUNT**: Prover9 is an Otter loop — it back-simplifies **both** `sos` and `usable`.
  A DISCOUNT loop (ours) back-simplifies only against the **active** set, and forward-simplifies the
  given clause when it is selected. We keep DISCOUNT; the only consequence is that passive may hold
  clauses that a later activation would subsume, which we handle by also backward-subsuming passive
  (cheap: it is just a `livePassive` removal).

**Common core, stripped of indexing and equality:** a one-substitution multiset **matcher**;
**subsumption** (fwd/bwd) with cheap count/weight/predicate-signature pre-filters; **subsumption
resolution** (incl. the unit special case); **condensation**. That is Phase 2.

---

## 3. The Phase-2 feature list (priority-ordered)

### P0 — Forward subsumption *(highest value, do first)*
Delete a newly-derived (or just-selected) clause `D` if some kept clause `C` **θ-subsumes** it:
∃σ with `Cσ ⊆ D` (multiset) and `|C| ≤ |D|`. Sound because `C ⊨ D`, so `D` is redundant.
- **Algorithm** (E/LADR style, no SAT): pre-filter, then backtracking multiset match.
  - *Pre-filter* (reject in O(1)): `|C| ≤ |D|`; `#pos(C) ≤ #pos(D)` and `#neg(C) ≤ #neg(D)`;
    `weight(C) ≤ weight(D)`; predicate-symbol signature of `C` ⊑ that of `D` (see §4 signature).
  - *Match*: order `C`'s literals (most constrained first — ground/heaviest), then recursively map
    each `Cᵢ` to an unused `Dⱼ` of equal polarity and predicate via the **matcher** (§5), backtracking
    on failure. Success ⇒ `C` subsumes `D`.
- **Loop integration**: run on every new clause after `canonicalize`, before it enters passive;
  also re-run on the **given** clause when popped (the active set grew since it was added). Candidates
  = linear scan of active with the pre-filter (indexing is Phase 4).
- **Reconstruction**: *none*. A subsumed clause is **discarded**, never enters the proof DAG. Clauses
  already derived from `C` keep their own `Justification`; deleting `D` cannot break them.

### P0 — Backward subsumption
When clause `C` is activated, delete every kept clause `D` (active **and** passive) that `C` subsumes.
- **Algorithm**: same subsumption test, `C` fixed as subsumer; scan active + passive with the
  pre-filter (Vampire's "query by the heaviest literal" is the indexed version; we just scan).
- **Loop integration**: in `activate(C)`, after adding `C` to active. Passive deletion = remove the
  id from `livePassive` (already lazy). Active deletion needs a **liveness marker** for the active set
  (mirror of `livePassive`) so the resolution scan skips dead clauses — see §6.
- **Reconstruction**: *none* (same reasoning as forward).

### P1 — Subsumption resolution (forward + backward), incl. the unit special case
A *simplifying* resolution. Side premise `C = C' ∨ L`, main clause `M = M' ∨ K`. If ∃σ with
`Lσ = ¬K` and `C'σ ⊆ M'`, then **remove `K` from `M`** (replace `M` by `M'`). Sound: the resolvent of
`C` and `M` on `L`/`K` is `C'σ ∨ M'`, which collapses to `M'` because `C'σ ⊆ M'`; and `M' ⊆ M`, so
`M` is subsumed by its own simplification. The **unit case** (`C` a unit, `C' = ∅`) is *unit deletion*
— cheapest and most common; implement it first.
- **Forward**: shrink the new/given clause using kept clauses. **Backward**: when `C` is activated,
  shrink kept clauses (re-insert the shrunk clause, delete the original).
- **Reconstruction**: reduces to **existing** machinery — `M'` is exactly
  `canonicalize(resolve(C, L, M, K))`. So add a `Justification.SubsumptionResolution(C, iL, M, iK)`
  whose reconstruction emits the Phase-1 **Resolution** step followed by **Canonicalisation**
  (dedup), both already kernel-checked. **No new kernel lemma needed.** (See §7.)

### P2 — Condensation
If unifying two literals of `C` yields a strictly shorter clause `C''` that still subsumes `C`,
replace `C` by `C''`. Cheap once subsumption + the matcher exist; an *immediate* (clause-local) rule.
- **Reconstruction**: `C''` is a **factor** of `C`, so reuse `Justification.Factoring` (+ dedup). No
  new machinery.

### Not needed — additional generating rules
**For refutational completeness of first-order logic *without equality*, ordered resolution +
factoring is already complete.** No extra *generating* rule is required in Phase 2. Hyperresolution,
unit-resulting (UR) resolution, and positive/negative resolution are **optional efficiency
refinements**, not completeness requirements; they complicate selection and reconstruction for
marginal benefit relative to redundancy elimination. **Recommendation: skip them in Phase 2** (revisit
in Phase 4 heuristics if the benchmark motivates it). *Unit conflict* (two complementary units ⇒ `□`)
is already found by ordinary resolution; no special rule needed.

### Optional — stronger canonicalisation (variable normalisation)
A canonical variable renaming (number variables by first occurrence in canonical literal order) makes
**variant** clauses syntactically identical, enabling O(1) variant detection and clause hashing.
**But subsumption already removes variants** (mutual subsumption), so this is a *performance* nicety,
not a correctness need — and it complicates reconstruction (a renaming is a real α-step in the kernel,
unlike sort+dedup). **Recommendation: defer**; if added, make it internal-only with a dedicated
reconstruction step, or skip and let subsumption absorb variants.

---

## 4. Candidate filtering without an index (cheap feature signature)

Phase 4 owns real term indexing; Phase 2 keeps the active/passive scan linear but makes each
subsumption *test* O(1)-rejectable. Cache on every `Clause` a small **signature**:
- `posCount`, `negCount` (literal polarity counts);
- `weight` (already cached);
- a compact **predicate-symbol multiset** fingerprint — e.g. a 64-bit OR/zone-count of head symbols,
  or a tiny sorted `(symbol → count)` vector (E's feature vector, minus the tree).

`C` can subsume `D` only if `C`'s signature is dominated by `D`'s on every component. This kills the
vast majority of pairs before any matching. The signature is computed once at clause construction
(extend `TermBank.mkClause`) and is the same data Phase-4 feature-vector indexing will bucket on.

---

## 5. New Core primitive: one-sided matching

Subsumption needs **matching**, not unification: `Cσ ⊆ D` binds only `C`'s variables; `D`'s terms are
rigid. The current `Trail.unify` binds **both** scopes and so is wrong for this. Add a one-sided
matcher, reusing the trail's binding arrays + `save`/`restore`:

- `match(pat: Term, patScope, target: Term, targScope): Boolean` — bind only `patScope` (pattern)
  variables; a pattern variable already bound must deref to a term *identical* to the target subterm;
  a **target** variable matches only a pattern variable that derefs to that very target variable
  (rigid). No occurs check needed (one-sided, target is fixed). Decompose compounds when heads match.
- It records bindings on the same trail, so the clause-level multiset matcher brackets each literal
  attempt with `save()`/`restore()` for backtracking — identical discipline to `unify`.

This is the single new low-level addition; it lives in `Core.Trail` (in-scope), is ~40 lines, and is
reused later by demodulation/superposition matching. (Scope convention: pattern = scope 0, target =
scope 1, matching the resolution convention.)

---

## 6. Loop integration (DISCOUNT, `Discount.scala`)

Make the **active set interreduced** and keep new clauses simplified, the DISCOUNT invariant:

1. **`addPassive(c)`** (new-clause path): `canonicalize` (have) → **forward-subsume / forward
   subsumption-resolution / condense** against active → if subsumed, discard; if shrunk, continue with
   the shrunk clause → else push to passive. (Tautology/`□` handling unchanged.)
2. **`popGiven` → `activate(g)`**: before generating, **re-forward-simplify `g`** against active
   (active grew since `g` entered passive); if now redundant, drop it and pop the next. Then:
3. **Backward simplification in `activate(g)`**: after adding `g` to active, use `g` to **backward
   subsume / subsumption-resolve** active **and** passive. Deleted passive clauses → remove from
   `livePassive`. Deleted active clauses → mark dead.
4. **Active liveness**: add an `IntOpenHashSet liveActive` (mirror of `livePassive`); the resolution
   scan in `activate` skips dead clauses, and `active` is compacted opportunistically when the dead
   fraction grows (avoids unbounded `ArrayBuffer` growth). A shrunk clause (subsumption resolution /
   condensation) is re-added through `addPassive` and its predecessor marked dead.

Ordering of the immediate/forward steps (mirroring Vampire's `CompositeISE`): duplicate/tautology
(`canonicalize`) → condensation → forward subsumption → forward subsumption resolution. Cheapest and
most-deleting first.

---

## 7. Proof reconstruction (`Reconstruction.scala`, `Core.Justification`)

The headline result: **deletion rules need no reconstruction, and the one shrinking rule reduces to
Phase-1 steps.**

- **Subsumption (fwd/bwd) & tautology deletion**: the deleted clause never reaches `□`'s DAG, so
  reconstruction is unaffected. Clauses previously derived from a now-deleted clause keep their parent
  references intact (the `Justification` DAG holds parents by reference, independent of set membership).
- **Subsumption resolution**: add
  `case SubsumptionResolution(side: Clause, sideLit: Int, main: Clause, mainLit: Int)` to
  `Justification`. Reconstruction emits exactly the Phase-1 reconstruction of
  `Resolution(side, sideLit, main, mainLit)` **followed by** the `Canonicalization` (dedup) step —
  both already produce kernel-checked `SCProofStep`s. The conclusion equals the shrunk clause `M'`.
- **Condensation**: the result is a factor; record `Justification.Factoring(parent, i, j)` (iterated
  if more than one literal is merged) — reuses Phase-1 factoring reconstruction.
- **`age` bookkeeping** (`TermBank.mkClause`): extend the `age` rule for the new justification case
  (`SubsumptionResolution` ⇒ `max(side.age, main.age) + 1`, like resolution).

**Soundness invariant for the benchmark is unchanged:** `bad_proof` must stay 0 (every refutation
still reconstructs to a kernel-valid proof of `⊢`) and `saturated` must stay 0. Because the only new
*derivation* is subsumption resolution and it reduces to checked steps, any reconstruction regression
surfaces immediately as `bad_proof`.

---

## 8. Implementation plan (file by file, in build order)

All files are inside `lisa-sets/src/main/scala/lisa/automation/superposition/` (in scope).

1. **`Core.scala`** — add one-sided `match` to `Trail` (§5); add the cheap **signature** fields
   (`posCount`/`negCount`/predicate fingerprint) to `Clause`, populated in `mkClause` (§4); add the
   `Justification.SubsumptionResolution` case and its `age` rule (§7).
2. **`Subsumption.scala`** *(new)* — `subsumes(bank, trail, c, d): Boolean` (pre-filter + backtracking
   multiset matcher), `subsumptionResolvent(...)` (forward/backward, returns the shrunk clause +
   justification), `condense(bank, trail, c): Option[Clause]`. Pure functions over `Core`, mirroring
   `Inference.scala`'s style (restore the trail internally; the loop shares one `Trail`).
3. **`Discount.scala`** — wire forward simplification into `addPassive`/given-selection, backward
   simplification + `liveActive` into `activate`, with compaction (§6). Add config flags
   (`forwardSubsumption`, `backwardSubsumption`, `subsumptionResolution`, `condensation`) defaulting
   on, so the benchmark can A/B each rule.
4. **`Reconstruction.scala`** — handle `SubsumptionResolution` (resolution + dedup); condensation needs
   nothing new (factoring).
5. **`Evaluation.scala` / `Benchmarks.md`** — re-run seed 42 (same 15 s / 100k) and record the new
   `refuted`/`timeout` split as the Phase-2 entry; verify `saturated=bad_proof=0`.

Build order respects the project rule: land the matcher + `Subsumption.scala` with unit tests first,
then loop integration, then reconstruction, each compiling and tested (`sbt lisa-sets/test`) before
the next.

---

## 9. Testing strategy (`src/test/.../superposition/`)

- **Matcher unit tests** (`MatchTest`): `P(x)` matches `P(a)` (binds `x`), `P(a)` does **not** match
  `P(x)`; rigidity of target variables; consistency (`P(x,x)` vs `P(a,b)` fails, vs `P(a,a)` succeeds).
- **Subsumption unit tests** (`SubsumptionTest`): the textbook cases — `P(x)` subsumes `P(a)∨Q`;
  `P(x)∨P(y)` does **not** subsume `P(a)` (length); polarity must match; multiset/injectivity
  (`P(x)∨P(y)` vs `P(a)∨P(a)` — needs two distinct targets); subsumption resolution
  (`P(x)` + `¬P(a)∨Q` ⇒ `Q`); condensation (`P(x)∨P(a)` ⇒ `P(a)`).
- **Reconstruction tests** (extend `ReconstructionTest`): a refutation that *requires* a
  subsumption-resolution step reconstructs to a kernel-valid `⊢` proof; condensation likewise.
- **Loop tests** (extend `DiscountTest`): a problem where forward subsumption strictly shrinks passive
  (assert fewer activations than Phase 1); a problem where backward subsumption deletes an active
  clause; confirm no refutation is lost (every Phase-1 refutation still found).
- **Benchmark regression**: seed 42 must keep `saturated=0`, `bad_proof=0`, and `refuted ≥ 35`.

---

## 10. Out of scope / deferred, and open decisions

**Deferred to later phases (unchanged):**
- **Term/clause indexing** (substitution trees, feature-vector *trees*, fingerprint indexing) →
  **Phase 4**. Phase 2 scans active/passive linearly with the §4 signature pre-filter.
- **Demodulation / rewriting** (forward + backward) → **Phase 3** with equality/superposition (see §0).
- **Clause splitting / AVATAR**, **hyper/UR-resolution**, **literal selection changes** → not in
  Phase 2 (Phase 4 heuristics at most).

**Open decisions for the user:**
1. **Demodulation placement** (§0): defer to Phase 3 (recommended) or implement now as inert-without-
   equality scaffolding? This changes `PLAN.md`, so it is your call.
2. **Variable normalisation** (§3 optional): add canonical renaming + variant detection now, or let
   subsumption absorb variants and defer? (Recommended: defer.)
3. **Subsumption semantics**: multiset (length-respecting, the standard — recommended) vs set
   inclusion. We propose multiset with the `|C| ≤ |D|` filter, matching all three reference provers.
