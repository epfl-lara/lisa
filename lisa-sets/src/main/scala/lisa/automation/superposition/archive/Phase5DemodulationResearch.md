# Phase 5 · Step 4 — Demodulation indexing: how Vampire, E and Prover9 do it, and our plan

> Research + design for indexing **demodulation** (rewriting by active positive unit equations) — the last
> full-active-scan in the loop (see [Phase5.md](Phase5.md) §8 Step 4). Grounded in the source of the three
> reference provers under `othersolvers/` (`vampire/`, `eprover/`, `prover9/`). The eq-set benchmark after Step 3
> (subsumption) confirmed the equality problems are demodulation-bound, not subsumption-bound — so this is the
> throughput lever for equality reasoning.

## 0. Our current state (what we scan today)

Demodulation rewrites a term `u` by an active oriented unit equation `l = r` (a **demodulator**) when `u = lσ`
and `lσ > rσ`, replacing `u` with `rσ`. Two directions, both currently **linear scans**:

- **Forward** (`Discount.forwardDemodulate` → `Demodulation.normalForm`): normal-form the *given* clause against
  **every** active demodulator. `normalForm` walks each literal's subterms and, per subterm, tries **every** rule
  in `activeDemodulators` (`Trail.matchTerm(rule.lhs, u)`), so it is `O(#demodulators × #subterms)` per given.
  (`activeDemodulators.toArray` also reallocates the rule array on every call — a free fix.)
- **Backward** (`Discount.backwardDemodulateStep` → `Demodulation.backwardDemodulate`): when the given `gc` is a
  new positive unit equality, scan **every** active clause's subterms for an **instance** of `gc`'s LHS,
  rewriting each hit. `O(#active × #subterms)`.

Supporting pieces we already have: `Demodulation.Rule(source, side, lhs, rhs, oriented, lhsVars)` (a demodulator,
with `oriented` = KBO-oriented so `l > r` unconditionally, else re-checked per instance); `Demodulation.rules`
(extract rules from a positive unit equality — the `Gt` side if oriented, or both variable-safe sides if
incomparable); `activeDemodulators` maintained incrementally (added on activation, dropped on removal);
`Trail.matchTerm` (one-sided matching); `Superposition.foreachSubterm` (the reused-stack subterm walk); and the
fingerprint **into-index** (`intoIndex`) over active clauses' *selected*-literal subterms.

**The two retrieval queries — and their asymmetry (the crux).** Demodulation needs *matching*, not unification:

- **Forward = a generalization (matching) query.** The query is a concrete subterm `u` of the given; we want a
  stored demodulator LHS `l` that **generalizes** `u` (`lσ = u`). Index the demodulator LHSs; retrieve
  generalizations of `u`.
- **Backward = an instance query.** The query is the new demodulator's LHS `l`; we want stored subterms `u`
  (across active clauses) that are **instances** of `l` (`u = lσ`). Index active subterms; retrieve instances of `l`.

The roles of *rule* and *target* swap between the two directions, so the retrieval direction reverses
(generalization vs instance). This dictates *what* is indexed (equation LHSs vs all subterms) and *which matcher*.
Note both are one-sided matching — distinct from the *unification* our Step-1/2 fingerprint indices do (though a
unification index is a sound **superset** filter for an instance query, since every instance is a unifier — that
matters for reusing our into-index for the backward direction).

---

## 1. Vampire — code tree (forward generalizations) + subterm substitution tree (backward instances)

Both demodulation rules take a *simplifying* index from the `IndexManager`, driven by `handleClause(cl, adding)`
on activation/deactivation (`ForwardDemodulation.cpp:79`, `BackwardDemodulation.cpp:51`,
`Indexing/IndexManager.cpp:36-45`). The two indices are deliberately asymmetric.

### 1a. Forward — `DemodulationLHSIndex` is a **code tree**, not a substitution tree
`DemodulationLHSIndex<ho> : TermIndex<DemodulatorData>` is built on `new CodeTreeTIS<ho, DemodulatorData>()`
(`Indexing/TermIndex.cpp:121-123`) — the demodulator LHSs are **compiled into a code tree**: each stored
(variable-normalized) LHS becomes a linear program of `CodeOp`s (`CHECK_FUN`, `ASSIGN_VAR`, `CHECK_VAR`,
`CHECK_GROUND_TERM`, `SUCCESS`; `Indexing/CodeTree.hpp:147-162`), and shared prefixes share instruction blocks (a
trie of programs). Matching a query subterm = flatten it to a `FlatTerm` and execute the code: `CHECK_FUN`
verifies the next symbol, `ASSIGN_VAR` binds an LHS variable to the current query subterm, `CHECK_VAR` enforces
repeated-variable equality. Reaching `SUCCESS` yields the `DemodulatorData*` plus a bindings array that *is* the
substitution with zero renaming (identity on the query side — `CodeTreeSubstitution`,
`CodeTreeInterfaces.cpp:38-85`). This is optimized hard because forward demodulation fires on **every** newly
derived clause. Its one weakness: the code tree can't carry a polymorphic **sort** match, so a variable-LHS hit
repairs the sort with a separate `RobSubstitution` (`ForwardDemodulation.cpp:128-150`).

- **Query:** for each rewritable non-variable subterm `trm` of `cl`, `_index->getGeneralizations(trm.term(), true)`
  (`ForwardDemodulation.cpp:117`) → each stored `l` with `lσ = trm`.
- **Populate (`handleClause`):** only **unit** clauses; LHS set from `EqHelper::getDemodulationLHSIterator` — the
  larger side if oriented (`preordered = true`); for an *incomparable* equation, **both** sides when each contains
  the other's variables (well-definedness). Each LHS is variable-normalized and stored as `DemodulatorData{term,
  rhs, clause, preordered, TermOrderingDiagram}` (`TermIndex.cpp:126-151`, `Index.hpp:115-148`).
- **Ordering `lσ > rσ`, per match:** accept immediately if `preordered`; else evaluate a precompiled
  `TermOrderingDiagram` (`tod->next()`) or `compareUnidirectional(trm, rhsApplied) == GREATER`; `-fde preordered`
  rejects all non-preordered demodulators (`ForwardDemodulation.cpp:153-171`).
- **Encompassment / redundancy** after retrieval: `redundancyCheckNeededForPremise` + `isPremiseRedundant` — under
  encompassing demodulation the matcher must **not** be a renaming (the demodulator must be strictly more general),
  and rewriting is skipped on the smaller side; for non-unit target clauses no other literal may exceed the rewrite
  literal (`DemodulationHelper.cpp:32-80`). This preserves completeness (plain demodulation isn't
  completeness-preserving without it).

### 1b. Backward — `DemodulationSubtermIndex` is a substitution tree over **all** subterms
`DemodulationSubtermIndex<ho> : TermIndex<TermLiteralClause>` on `new TermSubstitutionTree<TermLiteralClause>()`
(`TermIndex.cpp:72-74`). It indexes **every rewritable subterm of every active clause** (all literals, deduped per
literal) — the reverse of the forward index (`handleClause`, `TermIndex.cpp:76-115`). Query: only for a positive
unit equality `cl`, for each oriented LHS `l`, `_index->getInstances<ho>(l, true)`
(`BackwardDemodulation.cpp:180-182`) → every active subterm `u = lσ`. Then per hit: color/self/already-removed
filters, `compareUnidirectional(u, rσ) == GREATER`, redundancy check, `EqHelper::replace`, emit a
`BwSimplificationRecord` (`BackwardDemodulation.cpp:85-152`).

**Takeaway:** forward = compiled **code tree** of equation LHSs, *generalization* retrieval; backward =
**substitution tree over all active subterms**, *instance* retrieval. Both re-check `lσ > rσ` and encompassment
per candidate.

---

## 2. E — perfect discrimination tree (forward) + **fingerprint subterm index** (backward)

E uses two structurally different indices, one per direction — and its backward index is a **fingerprint index**,
the same family as our Step-1/2 indices (the strongest signal for what fits us).

### 2a. Forward — a Perfect Discrimination Tree (PDT), `ccl_pdtrees.c`
A trie over demodulator LHSs stored in **flattened left-to-right preorder** (`PDTNodeCell`, `ccl_pdtrees.h:49-83`):
children keyed by function symbol (`f_alternatives`, an `IntMap` by `f_code`) or by variable (`v_alternatives`);
leaves hold `ClausePos_p` demodulators. It is *perfect* — variables kept distinct (not collapsed to one `*`) — so a
leaf identifies the exact LHS and the retrieved substitution is exact, no re-match. Retrieval (`pdtree_forward`,
`ccl_pdtrees.c:560-697`) is a **generalization/matching** walk: a symbol edge follows the query's current symbol; a
variable edge binds the stored variable to the whole current query subterm (or checks consistency if already
bound). `prev_subst` marks enable backtracking to the next alternative.

- **Size & age pruning at each node** (`pdtree_verify_node_constr`, `ccl_pdtrees.c:521-543`, both flags default on):
  `size_constr` = the *minimum LHS weight* at/below the node — since matching only *grows* a term (variables map to
  bigger subterms), a query lighter than every LHS below cannot match, so the whole subtree is pruned. `age_constr`
  = the newest demodulator date below the node — combined with the term's cached normal-form date, lets E skip
  subtrees with no demodulator newer than the last time the term was normalized. Both are maintained incrementally
  on insert.
- **Populate:** the forward set is the **processed positive unit equalities**, split into oriented "rules"
  (`processed_pos_rules`) and unorientable "equations" (`processed_pos_eqns`), each owning a `demod_index` PDT
  (`ccl_proofstate.c:174-178`). Insertion indexes the `LeftSide`, **and the `RightSide` too when the equation is
  unoriented** (`ClauseSetPDTIndexedInsert`, `ccl_clausesets.c:556-568`) — incomparable equations go in both
  directions, with orientation decided *per instance* at retrieval.
- **Ordering enforced after retrieval** (`indexed_find_demodulator`, `ccl_rewrite.c:562-653`): `instance_is_rule`
  checks `lσ > rσ` (`TOGreater`), rejects renamings and RHS-unbound-variable results; skipped for already-oriented
  equations (orientation is stable under σ). A `restricted_rw` flag forbids rewriting a maximal side by a renaming
  (completeness).

### 2b. Backward — the `bw_rw_index`, a fingerprint index over subterms
When a new demodulator `l→r` arrives, E finds processed clauses with a subterm that is an **instance** of `l` using
`gindices.bw_rw_index`, which is a `SubtermIndex_p` = **`FPIndex_p`** (a fingerprint index,
`ccl_subterm_index.h:37`, `ccl_global_indices.c:102`). It indexes **all non-variable subterms of every processed
clause** (`ClauseCollectIdxSubterms`), each fingerprint leaf carrying an exact-term tree whose payload
`BWRWPayload{rw_rest, rw_full}` maps a subterm to its occurrence clauses (split into "restricted"/maximal-side vs
unrestricted occurrences). The query is an **instance** filter: `FPIndexFindMatchable` /
`fp_index_rek_find_matchable` (`cte_fp_index.c:305-391`) descends the fingerprint trie with `l` — a **variable
position in the query matches every stored symbol** (the stored term instantiates it), a concrete query symbol
follows only that symbol — over-approximating the instance set; candidates are then verified exactly with
`SubstMatchComplete` + `instance_is_rule` (`ccl_rewrite.c:1053-1121`). Rewritten clauses are moved to `tmp_store`
for reprocessing.

### 2c. Shared-term normal-form caching (why E is fast at rewriting)
E shares all terms in a term bank and caches rewriting on the shared cells: `TermAddRWLink` records a rewrite edge
on a shared subterm so every clause containing it reuses the result; `nf_date` per cell lets `term_li_normalform`
skip a term already in normal form w.r.t. the current demodulator set (`ccl_rewrite.c:829-895`). The PDT's
`age_constr` is the index-level counterpart of this cell-level cache. (We don't share terms across clauses the same
way, so this whole layer is a future consideration, not part of a first index.)

**Takeaway:** E = **PDT for forward** (perfect, size/age-pruned, orientation checked post-retrieval) + **fingerprint
subterm index for backward** (instance filter + exact verify). The backward choice is decisive for us: E indexes
backward demodulation with the very structure we already have.

---

## 4. Comparison and what fits us

| | forward (generalization) | backward (instance) |
|---|---|---|
| **Vampire** | compiled **code tree** of LHSs (`getGeneralizations`) | **substitution tree** over all active subterms (`getInstances`) |
| **E** | **perfect discrimination tree** (size/age pruned) | **fingerprint index** over all subterms (`FPIndexFindMatchable`) |
| **Prover9** | **perfect discrimination tree** (`DISCRIM_BIND`) | **FPA path index** (`INSTANCE` query) |

**Unanimous shape, and it matches the query theory (§0):** forward demodulation is a *generalization* query against
a **small, slowly-changing** set of demodulator LHSs → all three use a **discrimination-tree-family** matching index
(E and Prover9 a textbook perfect discrimination tree; Vampire a compiled code-tree optimization of the same idea).
Backward demodulation is an *instance* query against a **huge, fast-changing** population of *all* active subterms →
each uses a coarse **filter-then-verify** index over subterms (E a fingerprint index, Prover9 FPA, Vampire a
substitution tree). The reason is the retrieval asymmetry plus the population sizes: a PDT is exact and cheap for the
few LHSs but poor at instance queries; a fingerprint/path filter is cheap to maintain over the millions of subterms
and just over-approximates, leaving a `matchTerm` verify.

**What fits us:**

- **Forward → a new perfect discrimination tree over demodulator LHSs.** This is the one genuinely new structure in
  Phase 5: our Step-1/2 fingerprint indices do *unification*, but forward demodulation needs *matching/generalization*,
  which a discrimination tree does exactly and cheaply (bind stored variables during a single descent, no verify).
  E and Prover9 both use precisely this. We should add **size-constraint pruning** (min LHS weight per node — E has it
  on by default, it's a few lines and prunes hard). We should **defer** the age/normal-form-date caching — it's tied
  to E's shared-term normal-form cache, which our per-clause term model doesn't have.
- **Backward → reuse a fingerprint index with an instance query.** E's backward index *is* a fingerprint index, so we
  reuse our `FingerprintIndex` directly. Our existing `retrieveUnifiable(l)` is already a **sound superset filter for
  instances** (every instance is a unifier, so no false negatives), verified by `Trail.matchTerm(l, u)` — no new
  compatibility table strictly required (a dedicated tighter "matchable" descent à la E's `FPIndexFindMatchable` is a
  later refinement). The one real gap: our fingerprint **into-index only holds *selected*-literal subterms**, whereas
  backward demodulation may rewrite *any* literal — so we need a demodulation subterm index over **all** rewritable
  subterms of active clauses (a second `FingerprintIndex` populated from all literals), or accept the selected-only
  gap (a completeness loss in simplification only, not refutational completeness).
- **Orientation** stays where it is: our `Demodulation.Rule.oriented` flag plus the per-instance KBO re-check for
  unoriented rules is exactly `instance_is_rule` (`lσ > rσ`); keep it, applied after index retrieval.
- **Free win regardless:** `forwardDemodulate` rebuilds `activeDemodulators.toArray` on every call — drop that.

---

## 5. Implementation plan (Phase 5 Step 4)

**Goal:** replace the two demodulation full-scans with matching indices; measured on the eq set (demodulation-bound).
Same rewrites (indices are filters confirmed by the real `matchTerm` + orientation check), so reconstruction is
untouched; behind flags for A/B, like Steps 1–3.

### 5.1 Forward — `DiscriminationTree` (new file)
A perfect discrimination trie over demodulator LHSs, stored in flattened preorder:
- **Node:** children by symbol (`Int2ObjectOpenHashMap[Node]` keyed by `f_code`) and a variable child (all stored
  variables collapse to a single "bind" edge at a position — for a *perfect* tree keyed by variable *number* we'd
  distinguish them, but LHS variables are already normalized, so one variable-edge per position with the stored var
  number recorded suffices), a leaf list of `Rule`s, and a `minWeight` per node (the size constraint).
- **`insert(rule)` / `remove(rule)`:** walk the flattened LHS, create/reuse edges, update `minWeight` on the path;
  prune emptied nodes on remove.
- **`findGeneralizations(query)(visit: Rule => Unit)`:** the matching descent — a symbol edge follows the query's
  symbol; a variable edge binds the stored variable to the current query subterm (via `Trail.matchTerm`/a bindings
  array) and skips it, backtracking on failure. **Size pruning:** skip a subtree whose `minWeight > weight(query)`
  (a lighter query can't match a heavier LHS). Allocation-free callback, reused walk stack (as `foreachSubterm`).
- **Wiring:** `Demodulation.normalForm`'s inner "try every rule per subterm" becomes
  `demodIndex.findGeneralizations(subterm)` → verify orientation (`rule.oriented` or KBO `lσ > rσ`) → rewrite. The
  tree replaces/augments `activeDemodulators` (insert on activation when gc is a demodulator, remove on removal),
  behind a `demodulationIndexing` flag with the linear path kept for A/B.

### 5.2 Backward — a demodulation subterm `FingerprintIndex`
- A `FingerprintIndex[DemodTarget]` over **all** rewritable non-variable subterms of active clauses (`DemodTarget =
  (clause, litIndex, pos)`), maintained on activation/removal (a second index next to `intoIndex`, or — if we accept
  the selected-only gap — reuse `intoIndex`).
- `backwardDemodulateStep(gc)`: for gc's LHS `l`, `subtermIndex.retrieveUnifiable(l)` → candidate subterms → verify
  `matchTerm(l, u)` + orientation → rewrite (replace the current active-scan in `Demodulation.backwardDemodulate`).
  Reuses the existing fingerprint machinery entirely; only a new payload + the verify-by-match.

### 5.3 Testing & measurement
- **A/B equivalence** toggling `demodulationIndexing`: forward and backward demodulation must produce the same
  normal forms / same verdict as the scan (reuse `DemodulationTest` + `EqualitySaturationTest`, add an index-vs-scan
  test on equality builders).
- **`DiscriminationTree` micro-tests:** generalization retrieval vs a brute-force matching oracle, size-constraint
  pruning correctness, insert/remove/prune, variable/nonlinear cases.
- **Reconstruction guard:** `bad_proof=0` must hold (indices don't touch reconstruction).
- **Measure** the eq set (seed 42) throughput with `demodulationIndexing` on/off — this is the set demodulation
  dominates, so it's where the win should show.

### 5.4 Order
1. `DiscriminationTree` + micro-tests (standalone, no wiring) — as `FeatureVector.scala`/`Fingerprint.scala` were.
2. Backward demodulation subterm `FingerprintIndex` + payload (mostly reuse).
3. Wire both into `Discount`/`Demodulation` behind `demodulationIndexing`; A/B equivalence.
4. Benchmark eq; tune (size pruning; whether to index all literals vs selected; a tighter instance descent).

---

## 3. Prover9 / LADR — perfect discrimination tree (forward) + FPA path index (backward)

Set up at startup with deliberately different structures (`provers.src/search.c:2693-2695`):
`init_demodulator_index(DISCRIM_BIND, …)` (forward) and `init_back_demod_index(FPA, …, 10)` (backward), both behind
the `Mindex` façade.

### 3a. Forward — `DISCRIM_BIND` perfect discrimination tree
A discrimination tree (`ladr/discrim.h:63-73`) keyed by the **flattened preorder symbol string** of the
demodulator LHS (fixed arities ⇒ no end-markers). Siblings sorted (variables first, then rigid symbols); leaves
hold a `Plist` of the LHS terms, each with a `container` back-pointer to its clause. Retrieval
(`discrim_flat_retrieve_leaf`, `ladr/flatdemod.c:100-178`) walks the query term left-to-right against the tree:
a **tree-variable** node binds to the current query subterm (or checks equality if already bound — nonlinearity),
a **rigid** node must match the query symbol. The bindings accumulated *during descent* **are** the matching
substitution — so the "bind" variant is a **perfect** index: the `Mindex` façade skips the verify step for
`DISCRIM_BIND` (`mindex.c:660-664`), unlike the imperfect `DISCRIM_WILD` (all tree vars → wildcard) which needs a
`match()` re-check. `DISCRIM_BIND` supports **GENERALIZATION retrieval only** (`mindex.c:472-474`).

- **Populate:** `demodulator_type` (`ladr/demod.c:40-78`) classifies a positive equality unit as
  `ORIENTED / LEX_DEP_LR / LEX_DEP_RL / LEX_DEP_BOTH`; `idx_demodulator` (`demod.c:90-104`) indexes only `alpha`
  (the LHS) for oriented/LR, and additionally `beta` for RL/BOTH. Inserted in `cl_process_new_demod`
  (`search.c:1517-1545`), removed in `disable_clause` (`search.c:1064-1069`, with empty-node pruning).
- **Orientation enforced at rewrite, not in the index** (`flatdemod.c:326-346`): an `ORIENTED` demodulator
  rewrites unconditionally; a lex-dependent one requires the instance be term-order-greater than the contractum
  (`flat_greater(subject, contractum)`), i.e. `lσ > rσ` re-checked per application.

### 3b. Backward — FPA path index, INSTANCE query
`index_clause_back_demod` (`ladr/backdemod.c:29-61`) indexes **every non-variable subterm of every active clause**
into an **FPA/path index** (`ladr/fpa.c`) — a trie over alternating (symbol, argument-position) labels, variables
encoded as a wildcard label, leaves = term lists ordered by a per-index `FPA_ID`. A new demodulator `l→r` issues
`mindex_retrieve_first(alpha, Back_demod_idx, INSTANCE, …)` (`backdemod.c:188`): `build_query`
(`fpa.c:894-979`) turns `l` into an **AND/OR tree** — fixed symbol/position pairs become path constraints combined
with **intersection (AND)**, and `l`'s **variable positions are simply skipped** (no constraint — this is what
makes INSTANCE queries cheap); `next_term` (`fpa.c:1098-1199`) lazily sorted-merges the posting lists by `FPA_ID`.
FPA answers are candidates (imperfect), verified by `match(query, found)` in the façade (`mindex.c:676`). Found
clauses are then copied, the originals disabled, and re-run through `cl_process` — so backward's index only
*locates* victims; the actual rewrite reuses the **forward** demodulation machinery (`search.c:1677-1710`).

**Takeaway:** identical strategy to Vampire in spirit — a **discrimination/matching index of LHSs** for forward
generalization, an **instance index over all active subterms** for backward — but Prover9's forward index is a
classic *perfect discrimination tree* (bind-during-descent, verify skipped) rather than Vampire's compiled code
tree, and its backward index is FPA path indexing rather than a substitution tree. FPA is explicitly "good for
INSTANCE, poor for GENERALIZATION" — the exact inverse of discrimination trees — which is *why* each direction gets
the structure whose strength matches its query (`fpa.h:36-40`).

---

## 4. Comparison and what fits us — (pending)

## 5. Implementation plan — (pending)
