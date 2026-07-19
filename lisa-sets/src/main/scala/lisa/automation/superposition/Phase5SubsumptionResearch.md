# Phase 5 · Step 3 — Subsumption indexing: how Vampire and Prover9 do it, and our plan

> Research + design for indexing clause **subsumption** (the throughput target — see
> [Phase5.md](Phase5.md) §8 Step 3). Grounded in the actual source of the two reference provers cloned under
> `othersolvers/` (`vampire/`, `prover9/`). The goal: replace our two `O(|active|)` per-given subsumption scans
> (`forwardSimplify`/`backwardSimplify`) with an index, to at least double clause-processing throughput.

## 0. Our current state (what we already have)

Every `Clause` caches a cheap **subsumption signature** (`Core.scala`): `size` (# literals), `posCount`,
`negCount` (polarity counts), `weight` (KBO-ish term weight sum), and `predBits` (a 64-bit mask OR-ing
`1 << (headSymbol & 63)` over its literals). `Subsumption.sigSubsumes(c, d)` is the O(1) **necessary condition**
for `c` to subsume `d`:

```
c.size ≤ d.size  ∧  c.posCount ≤ d.posCount  ∧  c.negCount ≤ d.negCount
                 ∧  c.weight ≤ d.weight       ∧  (c.predBits & d.predBits) == c.predBits
```

All five are **monotone under matching** (a subsumer is smaller/lighter and its head-symbols are a subset), so
they are exactly the kind of features a feature-vector index is built on. The verifier is
`Subsumption.subsumes` — a multiset multi-literal matcher (heaviest-literal-first, with weight-skip pruning).

**The gap:** `sigSubsumes` is applied in a *linear scan* over all active clauses in both `forwardSimplify` and
`backwardSimplify`. So per given clause we pay `O(|active|)` signature checks plus the full matcher on every
candidate that survives the signature. Indexing means: store the active set keyed by these features so forward
subsumption visits only clauses with signature `≤` the query and backward only those `≥` it.

Two design questions the reference provers answer differently: **(A)** organise by *whole-clause feature
vectors* (Prover9, E) or by a *per-literal term index* (Vampire)? **(B)** verify by classic backtracking
multi-literal matching (us, Prover9) or by a *SAT encoding* (Vampire)?

---

## 1. Vampire — literal substitution tree + SAT subsumption (NO feature vector)

**Headline:** Vampire has **no feature-vector / FVIndex** anywhere in its subsumption path (confirmed by an
exhaustive source search — zero hits for `FVIndex`/`FeatureVector`/`feature.?vector` in `Indexing/`,
`Inferences/`, `SATSubsumption/`). Candidate retrieval is a **per-literal substitution tree**; verification is a
**SAT solver with a substitution theory**. Cheap whole-clause filtering is done per-candidate at check time, not
via a stored vector.

### 1a. Candidate retrieval — one maximally-restricting literal per clause
The default engine is `ForwardSubsumptionAndResolution` (wired in
`Saturation/SaturationAlgorithm.cpp:1671`). It keeps two `LiteralIndex<LiteralClause>` indices, each a
`LiteralSubstitutionTree` whose leaves are `{Literal*, Clause*}` pairs
(`Inferences/ForwardSubsumptionAndResolution.cpp:41-42`, `Indexing/LiteralIndex.hpp:65`):

- `_fwIndex : FwSubsSimplifyingLiteralIndex` — for each stored clause of length ≥ 2, inserts **only its single
  least-matchable literal** (`Indexing/LiteralIndex.cpp:58-68`).
- `_unitIndex : UnitClauseLiteralIndex` — the sole literal of every unit clause.

"Least-matchable" = the literal with the most matching constraints, so the index is maximally discriminating.
`LiteralByMatchability::computeRating(lit) = lit->weight() - lit->getDistinctVars()`
(`Kernel/LiteralByMatchability.hpp:48-51`) — non-variable symbols plus repeated-variable occurrences; the
highest-rated literal is indexed.

**Query** (`ForwardSubsumptionAndResolution.cpp:102-104`): to find clauses that could subsume query `cl`,
iterate over **every** literal of `cl` and ask the tree for **generalizations** — stored literals `L` with
`∃σ. σ(L) = lit`. This is correct because if stored `S` subsumes `cl`, `S`'s indexed (least-matchable) literal
must map to *some* literal of `cl`, and we try them all. A `DHSet<unsigned>` of clause numbers
(`checkedClauses`) dedups candidates surfaced through multiple query literals.

### 1b. Verification — SAT with a substitution theory
`SATSubsumption::SATSubsumptionAndResolution::checkSubsumption(side L, main M)`
(`SATSubsumption/SATSubsumptionAndResolution.cpp:835`):
1. **Prune** (the "feature filter", computed per candidate, not stored): `pruneSubsumption` (`:198`) rejects if
   `|L| > |M|` and does a **signed-predicate multiset** subset test — the multiset of `(functor, polarity)`
   headers of `L` must be contained in `M`'s (`:233-247`), via a timestamped counting vector.
2. **`fillMatchesS`** (`:354`): for every literal pair `(l_i, m_j)` with equal functor+polarity, run
   `MatchingUtils::matchArgs` (one-sided syntactic matcher; `matchReversedArgs` for equalities). Each success
   allocates a SAT variable, records a `Match{i,j,polarity,var}` in a sparse i×j `MatchSet`, and commits the
   substitution into a `BindingsManager` keyed by that var. Any `l_i` with **no** match ⇒ bail (impossible).
3. **`cnfForSubsumption`** (`:479`): **completeness** — for each base literal `i`, `⋁_j b_ij` (matched
   somewhere); **multiplicity** — for each instance literal `j`, an **AtMostOne** over `{b_ij}` (each `m_j` used
   once).
4. **Solve** with the embedded `subsat` CDCL solver whose **theory** layer rejects any assignment selecting two
   matches with incompatible substitutions (a variable bound to two terms) — enforcing global substitution
   compatibility the propositional layer can't (`:871`). `Sat` ⇒ subsumption holds.

There is a **unit fast path** (a unit generalization in `_unitIndex` ⇒ immediate subsume, no SAT;
`:77-88`).

### 1c. Subsumption resolution — same index, richer encoding
The retrieval loop additionally fetches **complementary** generalizations (negative matches, `:180`), and
`checkSubsumption(mcl, cl, checkSR=true)` fills the match set with both polarities so the SR check
**reuses the same match set / bindings** and only swaps the CNF (`clear_constraints`, `:897`) — the amortization
the file comments call the "2023/2024 loop optimization". SR CNF adds a "resolved literal" variable `c_j` per
instance literal with Existence/Uniqueness/Completeness/Coherence clauses (`cnfForSubsumptionResolution:572`).
Forward tries subsumption first and only emits an SR conclusion once subsumption is ruled out (subsumption is
the stronger simplification).

### 1d. Backward subsumption — the dual, all-literals index
`BackwardSubsumptionAndResolution` maintains `BackwardSubsumptionIndex` over the active set, indexing **every
literal** of each stored clause (`Indexing/LiteralIndex.cpp:47-55`), not just the least-matchable one. Reason:
in backward the query `cl` is the *subsumer* and stored clauses are the larger *subsumed* candidates, so a
stored clause must be findable by any of its literals. Query = pick `cl`'s heaviest literal and call
`_bwIndex->getInstances(lit, …)` — stored clauses containing an **instance** of `lit`
(`BackwardSubsumptionAndResolution.cpp:127-140`). Verification is the identical SAT check with `cl` as side and
the stored clause as main. So: **forward = many query literals against a one-literal index (`getGeneralizations`);
backward = one query literal against an all-literals index (`getInstances`).**

### 1e. Optional whole-clause code tree (off by default)
`CodeTreeForwardSubsumptionAndResolution` uses a `ClauseCodeTree` (`CodeTreeSubsumptionIndex`) that inserts the
**whole clause** compiled to matching bytecode and returns candidate premises directly; the SAT check is then
only a debug-time `ASS` confirmation. Enabled by `--code_tree_subsumption`, off by default.

**Vampire takeaway for us.** A per-literal term index (indexing the single most-restricting literal) is an
alternative to a feature-vector index. It reuses the *same substitution-tree machinery a term index needs* — but
we don't yet have a literal *matching* index (our Step-1/2 fingerprint indices are for *unification*, and
retrieve entries, not owner-clauses). The SAT verifier is a big engineering item (an embedded CDCL solver with a
theory) and is overkill unless multi-literal matching is itself the bottleneck; our `Subsumption.subsumes`
backtracking matcher already fills that role.

---

## 2. Prover9 / LADR — feature-vector discrimination trie (`Di_tree`)

**Headline:** Prover9's live subsumption path (`provers.src/index_lits.c`, *not* the dead `forward_subsume.c`
whose `#define FEATURES` is commented out) uses a **feature-vector index** for non-unit clauses — an integer-vector
discrimination trie — plus separate term indexes for the unit cases. This is the design we adopt.

### 2a. The feature vector — `features()` (`ladr/features.c:113-171`)
A fixed-length `Ilist` of ints, in order:
1. `#positive_literals`, `#negative_literals`;
2. for each **relation** symbol in a fixed `Feature_symbols` set: `(pos_occurrences, neg_occurrences)`;
3. for each **function** symbol: `(pos_occ, neg_occ, pos_maxdepth, neg_maxdepth)`.

Length `= 2 + 2·#rel + 4·#func`. **Variables are not counted** (`fill_in_arrays` skips `VARIABLE(t)`), and depth
at a variable position is 0 — this is exactly what makes the vector monotone. The symbol set is fixed once at
search start; symbols interned later are silently skipped (`sn ≥ Work_size`) — sound (less discrimination, never a
missed match).

### 2b. The trie — `Di_tree` (`ladr/di_tree.h:32-39`)
An integer-vector discrimination trie: each internal node's `label` is one feature-component value, **siblings are
kept sorted ascending**, and a leaf holds a `Plist` of all clauses whose vector is exactly that root-to-leaf path.
Insert (`di_tree.c:175-203`) walks the vector creating/reusing the sorted child per level; delete
(`di_tree.c:215-244`) descends the exact path, removes the clause at the leaf, and prunes emptied nodes.

### 2c. Retrieval — the `≤` / `≥` descents
- **Forward** (find stored `C` subsuming new `D`): `di_tree_forward` visits only children with `label ≤ D_feature`
  at each level (`di_tree.c:377`: `while (kid && kid->label <= vec->i) …`), because a subsumer must have
  `feature(C) ≤ feature(D)`. At the leaf it runs the real matcher `subsumes_di` and returns the **first** verified
  subsumer.
- **Backward** (find stored `D` that new `C` subsumes): `di_tree_back` skips children with `label < C_feature` then
  visits **all** the rest (`di_tree.c:429-434`), since a subsumee needs `feature(D) ≥ feature(C)`. It collects
  **all** verified subsumees (backward disables every one).

### 2d. Monotonicity (why the descents are sound) — `features.c:185-192`
`C` subsumes `D` ⇒ `Cθ ⊆ D` (literal multisets), and: literal-polarity counts can only grow; per-symbol
occurrence counts can only grow (θ replaces uncounted variables with ≥0 counted symbols; extra `D`-literals only
add); max depths can only grow (instantiation pushes symbols deeper). So `feature(C) ≤ feature(D)` componentwise —
no real subsumer/subsumee is ever pruned. Distinct clauses can share a vector (filter is incomplete), so the leaf
still runs full matching.

### 2e. Units, verify, lifecycle
- **Units** get dedicated term indexes, not the feature tree: `Unit_discrim_idx` (a `DISCRIM_BIND` discrimination
  tree) for forward unit subsumption / unit deletion via `GENERALIZATION` queries; `Unit_fpa_idx` (FPA path index)
  for backward via `INSTANCE`. (`index_lits.c:23-27`, `subsume.c`.)
- **Verifier** at every leaf is one-way multi-literal matching `subsume_di_literals` / `subsume_literals`
  (`di_tree.c:310-334`, `subsume.c:120-138`) — recursive, map each `C`-literal onto a same-sign `D`-literal under a
  single substitution, backtracking; guarded by `nc ≤ nd`. This is our `Subsumption.subsumes`.
- **Lifecycle**: one façade `index_literals(c, INSERT|DELETE)` (`index_lits.c:82-100`) maintains all indexes as
  clauses enter/leave the usable/sos lists. Forward subsumption is a retention test before keeping a new clause;
  backward runs after keeping, disabling all returned subsumees.

---

## 3. Comparison and our design choice

| | **Prover9 / E** | **Vampire** |
|---|---|---|
| Candidate retrieval | whole-clause **feature-vector trie** (`≤`/`≥` descent) | **one literal** per clause in a substitution tree; query all of the other clause's literals |
| Verify | recursive multi-literal matcher at leaves | **SAT** solver with a substitution theory (subsat) |
| Cheap filter | the feature vector itself (stored) | per-candidate multiset/set prune, computed at check time |
| Units | separate discrimination / path indexes | same literal index (unit fast paths) |

**We follow Prover9 / E (feature-vector trie).** Reasons, specific to our codebase:
1. **We already have the monotone features and the verifier.** `posCount`/`negCount`/`weight` are cached on every
   `Clause`, are exactly Prover9's leading features, and `Subsumption.subsumes` is exactly its leaf matcher. The
   feature-vector index is a thin structure *over what we already compute* — the smallest possible new surface.
2. **Vampire's path needs machinery we don't have and don't want yet.** Its retrieval needs a *matching* literal
   index (substitution/discrimination tree); our Step-1/2 fingerprint indices are *unification* indices that return
   sub-entries, not owner clauses — reusing them for subsumption doesn't fit. And its verifier is an embedded CDCL
   SAT solver with a custom theory — a large engineering item justified only when multi-literal matching itself is
   the bottleneck, which ours isn't.
3. **It maps 1:1 onto the scans we're replacing.** `forwardSimplify`'s subsumption arm → forward `≤`-descent;
   `backwardSimplify`'s → backward `≥`-descent. Nothing else in the loop changes.

`predBits` (our 64-bit head-symbol mask) is a *set* test, not a scalar `≤`, so it is **not** a trie dimension; we
keep it as part of the O(1) leaf pre-check (`sigSubsumes`) before calling `subsumes`. Its discrimination role is
better served, when we need more pruning, by Prover9-style **per-symbol occurrence counts** (see the plan's
refinement).

---


## 4. Implementation plan (Phase 5 Step 3) — feature-vector index with adaptive ordering

**Goal:** replace the two `O(|active|)` subsumption scans with a feature-vector index; target ≥2× given-clause
throughput. The index is a candidate *superset* filter that `Subsumption.subsumes` verifies, so results are
identical (completeness = feature monotonicity, §3), reconstruction is untouched, and everything sits behind a
`subsumptionIndexing` flag for A/B, like Steps 1–2.

### 4.0 Design decisions (efficiency rationale)
- **D1 — trie features are low-cardinality counts only; `weight` and `predBits` are leaf checks.** A trie level's
  cost is its fan-out (children in the `≤`/`≥` cone). `weight` has huge cardinality ⇒ a bad level. So the trie is
  built over `posCount`, `negCount`, and **per-symbol occurrence counts** (all small); `weight` (`≤`) and
  `predBits` (`⊆`) — already cached, monotone — become the O(1) residual check at the leaf, just before the
  matcher. `size` needs no check (implied by `posCount+negCount`).
- **D2 — full permuted vector = trie depth (E-faithful).** All trie features are low-cardinality, so two clauses
  share a leaf only if they agree on every trie feature ⇒ leaves stay small without any secondary leaf scan.
- **D3 — sorted parallel arrays for children** (`int[] keys` + `Node[] kids`, binary-search boundary), not
  hashmaps (can't range-iterate) or per-node tree-maps (alloc + pointer-chase). Matches Prover9's sorted siblings /
  E's ordered `IntMap`; cache-friendly; fan-out per node is small so insert `arraycopy` is cheap.
- **D4 — vector recomputed per phase**, not cached on `Core.Clause` (keeps the change inside the new file +
  `Discount`); O(clause size), the same class as the fingerprint indices' remove. To avoid recomputing *within* a
  phase, `activate` uses `FeatureVectorIndex.backwardCandidatesThenInsert` — the backward-subsumption query and
  the insert of the given share **one** `fillVector` (the given is queried before it is placed, so it is not its
  own candidate, and nothing touches the reused buffer between the two). This mirrors E, which threads one packed
  feature vector through its forward-subsumption check and the insert, and recomputes at other phases (deletion,
  the backward pass). The forward-subsumption query at selection stays separate (it precedes the survive gate and
  runs on a possibly-not-yet-shrunk clause).
- **D5 — adaptive permutation computed once per `saturate`, then frozen.** Adapted to *this* problem's clause/symbol
  distribution (E's `use_perm_vectors`), not continuously re-adapted. Superposition invents no new symbols, so the
  featured-symbol set derived from the initial clauses is stable for the run.

### 4.1 Feature vector & layout
Fixed-length `Array[Int]` of length `D` (~8, tunable). Each slot's *source* is `POS` (posCount), `NEG` (negCount),
or `SYM(s)` (total occurrences of symbol `s`). The **permutation** is the ordered list of `D` sources — it *is* the
trie level order and the vector layout. Per-symbol counts are **total occurrences** in v1 (monotone, §3);
polarity-split `(pos_occ, neg_occ)` is the first refinement if pruning is weak.

Vector fill (per clause): zero the buffer, set the `POS`/`NEG` slots from the cached counts, then one recursive walk
over each literal atom incrementing `out(symbolSlot(code))` for featured symbols (`symbolSlot: Array[Int]` indexed
by symbol code, `-1` = not featured ⇒ O(1) per symbol occurrence). O(clause size), same cost class as `predBits`.

### 4.2 Adaptive permutation (the E part)
At `saturate` start, over the initial clause set `S`:
1. **Doc-frequency pass:** one walk per clause collecting its *distinct* symbol codes (timestamp-marked to avoid
   re-clearing), incrementing `docFreq[s]`. O(|S|·avg size), O(#symbols) memory.
2. **Score symbols by binary-presence entropy** `H(docFreq[s]/|S|)` — maximised near 50 % presence (the best split
   at that trie level), and `0` for symbols in *all* or *no* clauses (dropped — E's `eliminate_uninformative`).
3. **Order:** `POS`, `NEG` first (the standard leading features), then the top `D-2` symbols by descending score.
   Result is the `sources` array + `symbolSlot`. Fully adaptive in *which* symbols and *in what order*; a fixed
   permutation (`POS, NEG`, symbols by global frequency) stays selectable as the A/B baseline for "does adaptivity
   pay". (Refinement noted: entropy-rank `POS`/`NEG` too; cap per-level cardinality.)

### 4.3 `FeatureVectorIndex` (trie)
`Node { int[] keys; Node[] kids; int nkids; ObjectOpenHashSet[Clause] bucket }` — internal nodes use the sorted
`keys`/`kids`, depth-`D` leaves use `bucket`; the traversal knows the level so no per-node leaf flag is needed. One
reused vector buffer per index (as `fpBuf` in Steps 1–2; index ops never nest). Ops:
- `insert(c)`: fill vector; descend, binary-search-or-create the child per level; add to the leaf bucket.
- `remove(c)`: fill vector; descend the exact path; `bucket.remove`; prune emptied nodes up the path.
- `forwardCandidates(q)(visit)`: fill `q`'s vector; **≤-cone** descent — at each level iterate the sorted prefix
  `keys(i) ≤ q(d)`. Allocation-free callback.
- `backwardCandidates(q)(visit)`: **≥-cone** — binary-search the first `keys(i) ≥ q(d)`, iterate the suffix.
- `clear()`.

### 4.4 Verify at the leaf (three-stage filter)
`forwardCandidates(m){ c => if c.weight ≤ m.weight && (c.predBits & m.predBits) == c.predBits &&
Subsumption.subsumes(c, m) then …discard m… }` — the trie guarantees the count features are `≤`, so the leaf only
re-checks the two non-trie monotone features then the exact matcher. Backward is the dual.

### 4.5 Loop integration & scope
Flag `subsumptionIndexing`; field `subsumptionIndex`; permutation built in `saturate` from `initial`; `insert` on
activation, `remove` in `backwardSimplify`/`removeFromActive`, `clear()` in `saturate`.
- **forwardSimplify:** subsumption arm → `forwardCandidates(m)`; **unit-deletion arm** iterates a maintained
  `activeUnits` sublist (few clauses), not all of `active`.
- **backwardSimplify:** subsumption arm → `backwardCandidates(gc)`. With backward-SR off by default, a *non-unit*
  given then does **zero** active scanning; a *unit* given still scans for backward unit deletion (a matching
  query, deferred to Step 4's discrimination tree).

### 4.6 Testing
Index-vs-scan A/B equivalence (toggle the flag; identical verdicts) across clausal/fof/eq; `SubsumptionTest`
unchanged; a **feature-monotonicity** property test (`c` subsumes `d` ⇒ `vector(c) ≤ vector(d)`); and
`FeatureVectorIndex` micro-tests against a brute-force `≤`/`≥`-cone oracle (retrieval exactness, insert/remove/
prune, permutation selection: constants dropped, best-first order).

### 4.7 Measurement & tuning
Re-run `BaselineBench` (seed 42) with the flag on/off on clausal + fof (subsumption-dominated). Success =
given-clause throughput ≥ 2×. Knobs, in order: `D`; adaptive vs fixed permutation; total vs polarity-split symbol
counts; shallow-trie + leaf-vector-scan fallback if leaves are fat.

### 4.8 Implementation order (each independently testable)
1. `Permutation` (scoring/selection) — **done as sub-step 1**.
2. `FeatureVectorIndex` (trie, descent, insert/remove/clear) + oracle micro-tests — **sub-step 2**, standalone, no
   loop wiring (exactly how `Fingerprint.scala` was built).
3. Monotonicity property test.
4. Wire into `Discount` behind the flag + `activeUnits`; A/B equivalence test.
5. Benchmark, then tune.

### 4.9 Risks / fallbacks
Degenerate pruning (non-discriminating features → fat leaves): the adaptive permutation is the primary mitigation,
the flag falls back to the linear scan, and D2's shallow-trie variant is the structural fallback. Permutation cost
on huge axiom sets: sample `S`. Correctness: the index can only ever be a superset filter, so a bug surfaces as a
*missed* subsumption ⇒ a different verdict, caught by the A/B test.
