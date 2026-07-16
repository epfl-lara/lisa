# Phase 5 — Term Indexing (research + design)

> Status: **research + plan for review.** No implementation yet. Per the project rule, coding begins only
> when the previous phase is complete (Phase 4 is) and the user asks to start. This document is the design
> deliverable — a self-contained explanation of term indexing and a concrete, performance-first plan for our
> prover, grounded in how Vampire, E and Prover9 do it.

Phase 5 in [PLAN.md](PLAN.md) is *performance*: term indexing first, then selection / age-weight heuristics.
This document covers **indexing only**; heuristics are a separate later step (§10).

---

## 0. Why indexing — the problem it solves

The DISCOUNT given-clause loop repeats: pick a clause, compute all inferences between it and the **active**
(processed) set, insert survivors. The dominating cost is *finding the partners*: for a given clause we must
locate, among the thousands of clauses already in `active`, the few whose literals/terms can actually
participate in an inference (unify, match, subsume). Today we do this by **scanning `active` linearly** on
every given clause (see §7). If the active set grows to `N` clauses and we process `G` givens, generating
inferences cost `Θ(N·G)` unification attempts — and `N` and `G` both grow with the proof, so this is roughly
**quadratic in the size of the saturation**. On hard problems that quadratic is the wall.

Our own equality benchmark makes the cost concrete: against E on the same 100-problem sample, **~59% of E's
lead (20 of 34 problems) is our prover simply running out of time** while E — with indexing — searches far
deeper in the same 15 s. Indexing replaces the `Θ(N)` scan-per-query with a data structure that returns only
the handful of *plausible* partners in roughly `O(log N)` or `O(#candidates)` time. It is the single biggest
prover-side lever we have.

Indexing does **not** change *which* inferences exist or *what* they produce — it only changes how fast we
find their premises. In particular it leaves proof reconstruction (Phase 4, Step 5) completely untouched: we
still call the same `superpose` / `resolve` / `demodulate` / `subsumes` on the same `Trail`, recording the
same `Justification`. Correctness of the *search* rests on one property of the index — **no false negatives**
(it must never hide a real partner) — while false positives are merely wasted verification work.

---

## 1. The vocabulary: four retrieval queries, perfect vs imperfect, filter-then-verify

Every index answers, for a **query term/literal `q`** against a **stored set `S`**, one of four questions.
Fix a substitution `σ`:

| Query | Returns stored `t ∈ S` such that… | Who needs it |
|---|---|---|
| **Unification** | `∃σ. tσ = qσ` (t and q *can be made equal*) | superposition, resolution, paramodulation |
| **Generalization** | `∃σ. tσ = q` (t is *more general*; q is an **instance** of t) | forward demodulation (find a rule LHS that matches this subterm), forward subsumption |
| **Instance** | `∃σ. t = qσ` (t is an **instance** of q; q is more general) | backward demodulation (new rule LHS → which stored subterms does it rewrite), backward subsumption |
| **Variant** | `∃` renaming `ρ. tρ = q` (t and q equal up to variable renaming) | duplicate/variant detection |

Generalization and instance are **mirror images** — swap query and stored. Unification is symmetric.

Two more distinctions run through every design:

- **Perfect vs imperfect.** A *perfect* index returns exactly the answers (the substitution is built and
  verified during retrieval). An *imperfect* index returns a **candidate superset** — a cheap filter with
  false positives that must be confirmed by a real `unify`/`match` afterward. Imperfect indexes are smaller,
  cheaper to maintain, and often faster overall because the filter is so cheap; the classic pattern is
  **filter-then-verify**: index → candidate set → real unification/matching to confirm and build σ. (Prover9
  names this split explicitly: the index produces candidates, the `mindex` layer verifies.)

- **Retrieval vs maintenance.** The active set *shrinks* too (backward subsumption/demodulation delete
  clauses), so the index must support **insert and delete** efficiently, not just query. Deletion cost is a
  real design constraint (empty-node pruning, ref-counts, tombstones).

We only ever index the **active** set (DISCOUNT indexes processed clauses; passive is drained by selection,
never scanned), and only the **eligible** (selected/maximal) literals' terms — matching what the loop
already iterates and what completeness requires.

The rest of §2–§6 explains each concrete structure from scratch; §7 maps them to our code; §8 is the plan.

---

## 2. Discrimination trees — a trie over the flattened term (perfect matching)

**Idea.** Write a term as the string of its symbols in **preorder** (root, then children left-to-right).
Because every symbol's arity is known, this string needs no brackets: `f(g(a),x)` becomes `f g a x`, and you
always know when a subterm ends. A **discrimination tree** is a trie (prefix tree) over these strings; each
stored term is a root-to-leaf path, and the leaf holds the payload (which clause/rule/position the term came
from).

```
        f
        |
        g
       / \
      a   b        stored: f(g(a),x)  and  f(g(b),x)
      |   |
      x   x   ← leaves hold (clause, side, position)
```

**Variables.** The subtlety is what to do with variables. Two variants:

- **Wildcard / imperfect** (Prover9's `discrimw.c`): every variable collapses to a single symbol `*`. The
  trie is small, but `*` matched a whole subterm structurally without *binding* it, so retrieval is only a
  filter — you still run a real `match` afterward. Handles AC symbols (by storing per-node integer counts:
  total AC args and non-variable AC args, retrieved with `≤`).
- **Perfect / bindable** (E's `ccl_pdtrees.c`, Prover9's `discrimb.c`): keep variables *distinct* (keyed by
  their number). Now a variable branch can **bind** the pattern variable to the query subterm during descent
  and check consistency (`x` seen twice must bind to the same thing). A successful root-to-leaf traversal
  that consumes the whole query *and* keeps the substitution consistent **is** a complete match — no
  post-check needed. This is the "perfect discrimination tree" (PDT).

**Retrieval = backtracking DFS over the query.** To find **generalizations** of a query `q` (stored LHSs
that match `q` — the forward-demodulation query): walk `q`'s preorder; at each tree node, either follow the
`f`-child whose symbol equals `q`'s current symbol, **or** follow a variable-child, binding that variable to
`q`'s current *whole subterm* and skipping over it. Both options may apply, so you keep a **backtracking
stack** and try the alternatives. Reaching a leaf with `q` fully consumed yields a matching rule.

**Why discrimination trees are the standard choice for demodulation.** Forward rewriting asks "does any
rewrite rule's LHS match this subterm?" thousands of times; the PDT answers it *exactly* (no verify pass) and
supports two extremely cheap pruning aggregates stored at each node:

- **Size constraint** (E): each node caches the *minimum term weight* of any LHS stored below it. A
  generalization can never be heavier than what it matches, so if the query subterm is lighter than a
  subtree's minimum, skip the whole subtree.
- **Age constraint** (E): each node caches the *newest clause date* below it, so rewriting only uses
  demodulators older than the term's current normal form — avoids redundant re-rewriting.

**Weakness.** Discrimination trees are excellent for *generalization/matching* but poor for *unification*
(a query variable can unify with any stored subtree, forcing you to explore everything — the wildcard
explosion). Use them for matching-heavy queries (demodulation, unit subsumption), not for
unification-heavy ones (superposition, resolution).

---

## 3. Path indexing / FPA — index by (symbol, position), retrieve by set-merge (imperfect)

**Idea (Prover9's `fpa.c`, "First-order Path Addressing").** Instead of one trie over the whole term,
describe a term by the **set of paths** it contains, where a path alternates *symbol* and *argument index*
down to a fixed depth: `f(g(a),x)` contains paths `⟨f⟩`, `⟨f,1,g⟩`, `⟨f,1,g,1,a⟩`, `⟨f,2,*⟩` (a variable
becomes the wildcard label `*`/`0`). Build one **posting list per path** — the set of all stored term-ids
that contain that path — kept **sorted by id**.

**Retrieval = AND/OR over posting lists.** A query term's answer must contain *all* of the query's required
paths, so you **intersect** their posting lists; positions where the query or a stored term has a variable
contribute a **union** with the `*` list. The query type controls the variable handling:

- **Unification / generalization**: a query variable still contributes its `*` list (a stored generalization
  may have anything there).
- **Instance / unification**: a *query* variable matches anything, so those argument paths are simply
  **skipped** (not intersected).
- Commutative symbols union the normal and argument-swapped intersections.

Because the posting lists are sorted by id, intersection/union are **linear merge-joins** streaming answers
in descending id order. AC symbols are treated opaquely (not descended into), which costs selectivity.

**Profile** (from `fpa.h`): **good for instance/variant, fair for unification, poor for generalization.**
So Prover9 uses **FPA for resolution and paramodulation (unification) and for backward demodulation/backward
subsumption (instance)**, and **discrimination trees for forward demodulation/unit subsumption
(generalization)** — the two structures are complementary, exactly along the strength boundary in §2.

---

## 4. Fingerprint indexing — a tiny fixed feature vector (imperfect, and the best fit for us)

**Idea (E's `cte_fp_index.c`, Schulz 2012).** This is the modern, simple, and very effective term index, and
the one whose assumptions match our data model best. A term's **fingerprint** is a *fixed-length* vector
obtained by sampling a **fixed, statically-chosen set of positions** and, at each, recording one feature from
a four-symbol alphabet:

| Feature | Meaning | When |
|---|---|---|
| `f` (a symbol code) | the position holds function/predicate symbol `f` | position exists, holds a symbol |
| `A` = ANY_VAR | the position holds a variable | walk ends exactly on a variable |
| `B` = BELOW_VAR | the position is strictly below a variable | walk hit a variable *before* consuming all indices |
| `N` = NOT_IN_TERM | the position cannot exist in this term or any instance | walk hit a symbol of too-small arity |

A "position" is a path of argument indices (`ε` = top; `0` = first arg; `0.1` = second arg of the first
arg…). E's default scheme **FP7** samples seven positions `{ε, 0, 1, 0.0, 0.1, 1.0, 1.1}` — the top symbol,
its two arguments, and their four grandchildren. Richer schemes (FP16, all-positions) discriminate more but
grow the index; FP7 is the balanced default.

Example: with positions `{ε, 0, 1}`, `f(g(a), x)` fingerprints to `[f, g, A]`; `f(x, b)` to `[f, A, b]`;
`c` (a constant) to `[c, N, N]`.

**The trie and retrieval.** Store fingerprints in a trie keyed by feature. Our symbol codes are already
`≥ 0`, so the three special features go into the **negatives** — `N = -1, A = -2, B = -3` — leaving symbol
codes unchanged (no `+1` shift) and giving the O(1) test `feature >= 0 ⇔ concrete symbol`, which the
compatibility tables use constantly. Retrieval descends the
trie following only **compatible** branches, per a small fixed **compatibility table** — one for unification,
a stricter/asymmetric one for matching:

- *Unification*: query symbol `f` is compatible with stored `f`, `A`, `B` (a stored variable or below-var can
  unify with `f`); query `A`/`B` is compatible with `A`, `B`, and **any** symbol.
- *Matching* (find generalizations): query symbol `f` is compatible only with stored `f` (a concrete symbol
  matches only itself); query `A`/`B` compatible with `A` and any symbol.

Reaching the bottom collects the node's payload — a **candidate set** (imperfect: false positives, never
false negatives) that is then confirmed with a real `unify`/`match`.

**Why fingerprints fit us best.** The query cost is: compute one fixed-size integer vector (a handful of
`arg`/`isVar`/`headSymbol` reads — all `O(1)` in our arena) then a shallow trie descent. There is no
backtracking substitution machine (substitution trees) and no compiled bytecode VM (code trees). It handles
*unification and matching* with the same structure (just a different compatibility table), so **one term
index serves superposition, and the matching table reuse also serves backward rewriting**. It is by far the
least code for the most benefit, and E — which is closest to our architecture — relies on it for exactly the
inference we're weakest on (superposition). See §8.

---

## 5. Substitution trees & code trees — Vampire's heavier, more powerful machinery

Vampire uses two structures we should **understand but not copy yet** (they are much more complex and their
extra power buys little until we have indexing at all).

**Substitution trees** (`Indexing/SubstitutionTree.hpp`). A single tree whose *edges carry substitutions*; a
root-to-node path composes a substitution, and leaves hold terms. One tree answers **all four** queries by
different descent disciplines (perfect for syntactic unification/matching, via specialized fast iterators
`FastGeneralizationsIterator` / `FastInstancesIterator`). Key performance ideas worth stealing regardless:

- **Top-symbol dispatch.** Literals are split by an outer flat array keyed on `(predicate, polarity)`
  (`LiteralSubstitutionTree` = `2·|preds|` trees); term nodes dispatch on the child's top functor
  (`childByTop`) before any real matching. This two-level "hash on the top symbol, then discriminate the
  arguments" is universal across all three provers and we should replicate it.
- **Adaptive node representation.** Arrays for ≤4 children, an ordered skip-list beyond — small-set fast
  path with a scalable fallback.
- **Allocation avoidance.** One reused mutable substitution with variable "banks" to separate
  query/stored/normalized namespaces, plus a stack of undo closures; pooled iterators; the hot loop only
  pushes/pops small stacks.

**Code trees** (`Indexing/CodeTree.cpp`). The index is **compiled to a linear instruction sequence** —
`CHECK_FUN f`, `ASSIGN_VAR n`, `CHECK_VAR n`, `CHECK_GROUND_TERM ptr`, `SEARCH_STRUCT` (hashed fan-out),
`SUCCESS` — executed by a tiny interpreter with a backtracking stack over a reused bindings array. Shared
prefixes of stored terms share instruction blocks. This is the fastest known *matching* index and Vampire
uses it for **forward demodulation** (`DemodulationLHSIndex`) and optionally forward subsumption
(`ClauseCodeTree`, a multi-literal matcher). It is a compiled discrimination tree — same job as E's PDT,
more engineering.

Notably, **this Vampire has no fingerprint or feature-vector index**: subsumption is a
`LiteralSubstitutionTree` generalization query on one selected literal (filter) followed by a **SAT-based**
exact subsumption test (verify).

---

## 6. Feature-vector indexing — clause-level subsumption (E and Prover9)

Subsumption is a **clause-level, multiset** query ("does clause `C` subsume clause `D`?"), not a term query,
so it needs its own index. Both E (`ccl_fcvindexing.c`) and Prover9 (`di_tree.c`) use a **feature-vector
index**:

1. Map each clause to a fixed-length **integer feature vector** of cheap, structural counts:
   `[#positive literals, #negative literals, and per symbol: (freq in +lits, freq in −lits, max depth in
   +lits, max depth in −lits)]`. E folds high-numbered symbols into shared buckets to bound the length and
   selects the ~17 most *informative* features via a permutation.
2. The features are **monotone under subsumption**: if `C` subsumes `D`, then *every* feature of `C` is `≤`
   the corresponding feature of `D` (`C` has no more literals, no more occurrences, no greater depth).
3. Store clauses in a trie branching on successive feature values. **Forward** subsumption ("is the new
   clause subsumed?") descends only into children with feature `≤` the query's; **backward** subsumption
   descends into children with feature `≥`. Leaves run the real multiset θ-subsumption test.

**We already have the seed of this.** Every `Clause` caches `posCount`, `negCount`, `weight`, and `predBits`
(a 64-bit head-symbol fingerprint) — the O(1) necessary-condition pre-filter `Subsumption` already uses. A
feature-vector index is precisely the *indexed* generalization of that filter: instead of testing the
condition against every active clause, the trie visits only the clauses that pass it.

---

## 7. Our situation — data model and the exact retrieval sites to replace

**Our term model is ideal for indexing.** Terms are hash-consed integer offsets into a flat `Long` arena
([Core.scala](Core.scala) `TermBank`): `isVar`, `varNum`, `headSymbol`, `arity`, `arg`, `weight`,
`freeVarMask` are all `O(1)` inline reads, and *structurally-identical subterms share one offset* (so a term
is a stable integer id and "same subterm" is a pointer compare). Variables are a negative functor;
[Trail](Core.scala) already provides two-scope `unify` and one-sided `matchTerm`, `Order` provides KBO, and
`Superposition.foreachSubterm` walks non-variable subterms on a reused stack. Clauses carry `id`, `weight`,
`posCount`/`negCount`/`predBits`. Everything an index needs (stable keys, cheap structure reads, a verifier)
is already here.

**The linear scans to replace** (all in [Discount.scala](Discount.scala) / [Demodulation.scala](Demodulation.scala)):

| Site | Current cost | Retrieval needed | Index (recommended) |
|---|---|---|---|
| `activate`: resolution against `active` (`while ai < active.length`, each selected literal pair) | `O(N·ℓ²)` per given | literal **unification** (complementary polarity, unifiable atom) | fingerprint over active atoms, split by `(pred, polarity)` |
| `activate`: superposition given↔active (`superposeUsing`/`superposeFromInto` → `superposeAtPositions` walks subterms) | `O(N · subterms)` | term **unification** (from-side ↔ into-subterm) | fingerprint over active subterms ("into") + active max eq-sides ("from") |
| `forwardDemodulate` → `Demodulation.normalForm` (scans `activeDemodulators` array per subterm) | `O(#rules · subterms)` | term **generalization** (rule LHS matches subterm) | perfect discrimination tree over demodulator LHS (size+age pruning) |
| `backwardDemodulateStep` → `backwardDemodulate` (scans `active`) | `O(N)` | term **instance** (new LHS matches stored subterm) | reuse the "into" fingerprint index (matchable retrieval) |
| `forwardSimplify` (scans `active`, `Subsumption.subsumes`) | `O(N)` | clause **generalization** (subsumer) | feature-vector index (`≤` descent) |
| `backwardSimplify` (scans `active`) | `O(N)` | clause **instance** (subsumee) | feature-vector index (`≥` descent) |
| subsumption resolution / unit deletion | folded into the above scans | literal generalization/instance | literal fingerprint + feature-vector |

Note the reuse: **superposition-"into" and backward-demodulation query the same set** (non-variable subterms
of active clauses) with unification vs matching respectively — one fingerprint index serves both.

---

## 8. The plan — a fingerprint-first, incremental, reconstruction-safe build-out

Design principles, in priority order (the user's brief: *performance is crucial*):

1. **Filter-then-verify, always.** Every index is an imperfect *candidate* generator; the existing
   `Trail.unify` / `matchTerm` and `Subsumption.subsumes` remain the verifier. This guarantees we can never
   introduce an unsound or incomplete inference from an index bug — a wrong candidate is caught by the
   verifier, and the only failure mode a *missing* candidate could cause is incompleteness, which we test for
   (§9). **Reconstruction is untouched**: the index changes only which `superpose`/`resolve`/`demodulate`
   calls we make; the `Justification` recorded is identical.
2. **Match our data model — fingerprints and a perfect discrimination tree (the E stack), not substitution/
   code trees (the Vampire stack).** Our flat integer terms make fingerprint sampling `O(1)` and a PDT a
   plain trie; substitution trees (backtracking substitution machine) and code trees (compiled VM) are far
   more code for power we don't need until indexing exists at all. This mirrors E, whose architecture is
   closest to ours and which beats us on exactly the superposition workload.
3. **Two-level top-symbol dispatch everywhere** (outer array on `(functor)` or `(predicate,polarity)`, inner
   fingerprint/trie on arguments) — universal in all three provers.
4. **Incremental maintenance.** Insert on `activate`; delete on removal by backward simplification (our
   clauses have stable `id`s; index payloads are `(clauseId, litIndex, position)`; empty nodes are pruned).
   Index only **active**, only **eligible** literals' terms.

### Step 1 — Fingerprint term index for superposition (biggest win first)

Build `FingerprintIndex` over the active set's rewritable subterms and equation sides. Concretely:

- `fingerprint(term): Array[Int]` sampling **FP7** positions `{ε,0,1,0.0,0.1,1.0,1.1}`, each encoded as an
  `Int`: a **concrete symbol → its code (`≥ 0`, unchanged)**; the three specials into the negatives —
  **`N` (not-in-term) = -1, `A` (any-var) = -2, `B` (below-var) = -3**. Symbols and specials are then
  disjoint with no `+1` shift, and `feature >= 0` is the O(1) "is-a-concrete-symbol" test the compatibility
  tables use. A direct walk over `arg`/`arity`/`isVar`.
- A trie keyed by feature; `findUnifiable(q)` descends the **unification** compatibility table (§4). (The
  matching table / `findMatchable` arrives with Step 3 for backward demodulation.)
- **Payload — a small `final class`, never a tuple** (a `Tuple` boxes the `Int`/opaque-`Int` fields; a
  `final class` stores them as unboxed primitive fields): `IntoEntry(clause: Clause, litIndex: Int, pos:
  Array[Int])` for the into-index, `FromEntry(clause: Clause, litIndex: Int, side: Int)` for the from-index.
  One object per indexed subterm, allocated at **activation** (amortized, not per query); `pos` is the very
  array later passed to `superpose`. (A structure-of-arrays leaf is a measured alternative — see
  PossibleOptimizations.md "Fingerprint index payload".)
- **Allocation-free retrieval.** `findUnifiable` must not allocate per candidate: it pushes candidates
  through a **callback** — `findUnifiable(q)(visit: Entry => Unit)` — or into a **reused buffer**, mirroring
  how `Superposition.foreachSubterm` reuses one `IntArrayList` stack across the whole walk. It never
  materialises a `List`/`Iterator` of entries on the hot query path (retrieval runs on every given clause).
- Two instances: **into-index** = every non-variable subterm of active clauses' eligible literals (this same
  index also serves backward demodulation in Step 3); **from-index** = the `Gt`/incomparable sides of active
  eligible positive equalities.
- Rewire `Discount.activate`: superposition-from-given = for each of the given's from-sides `l`,
  `intoIndex.findUnifiable(l)` → candidate `IntoEntry`; superposition-into-given = for each given subterm
  `u`, `fromIndex.findUnifiable(u)` → candidate `FromEntry`. Each candidate is verified by the existing
  `trail.unify` + `Superposition.superpose` (unchanged), so gates/build/`Justification` are identical.
  Maintain both indices incrementally: insert on `activate`, delete on removal in
  `backwardSimplify`/`removeFromActive` (clauses carry stable `id`s; empty trie nodes are pruned on delete).
- **Verify**: reuse `SuperpositionTest` (results identical to the linear-scan version) + a new index-vs-scan
  equivalence test (same problem, both paths must derive the same clauses / reach □). Keep the linear-scan
  path behind a flag for the A/B check, then remove it.

### Step 2 — Fingerprint literal index for resolution

A `(predicate, polarity) → FingerprintIndex` over active literal atoms. Resolution partners for a given
selected literal = complementary-polarity bucket `.findUnifiable(atom)` → verify with `Inference.resolve`.
Replaces the resolution arm of the `activate` scan.

### Step 3 — Perfect discrimination tree for forward demodulation

A PDT over demodulator LHSs with per-node **size** (min weight) and **age** constraints (§2). `normalForm`'s
inner "scan all rules per subterm" becomes "PDT `findGeneralizations(subterm)`". Backward demodulation reuses
the Step-1 into-index (`findMatchable` for the new rule's LHS). Verify against `DemodulationTest`.

### Step 4 — Feature-vector index for subsumption

Generalize the existing `predBits`/`posCount`/`negCount`/`weight` pre-filter into a feature-vector trie
(E-style; start with those four plus a few per-top-symbol counts). Forward subsumption descends `≤`, backward
`≥`; leaves run the unchanged `Subsumption.subsumes`. Replaces the `forwardSimplify`/`backwardSimplify`
scans. Verify against `SubsumptionTest`.

### Step 5 — Measure and tune

Add a **given-clauses/second** (and inferences/second) counter to the loop, and compare index vs linear-scan
on `EqFofEvaluation` (seed 42) and the clausal `Evaluation` set. Expected: large throughput gains on the
prover-timeout bucket (§0), converting timeouts to refutations, with `bad_proof` staying 0 (reconstruction
unaffected). Tune the fingerprint scheme (FP7 → deeper if false-positive rate is high), node representations
(array→sorted beyond a threshold), and whether the literal index should be a PDT instead.

### Sequencing & scope

Steps 1–4 are independent and individually testable; do them one at a time (Step 1 first — it targets the
biggest bucket). Each step keeps the linear-scan path behind a flag initially so we can A/B and prove
equivalence, then removes it. All code stays under `superposition/`; no kernel or clausifier change; no
change to `Justification`, `Reconstruction`, or the inference primitives — only *how candidates are found*.

---

## 9. Correctness & testing strategy

- **Filter soundness is the only invariant that matters.** An index must never drop a real partner
  (completeness); a spurious partner is harmless (the verifier rejects it). So the key tests are
  **equivalence tests**: on a batch of problems, the indexed path must derive the *same* refutations (reach
  □ on exactly the same inputs) as the linear-scan path. Keep both paths behind a flag during each step to
  run this A/B directly.
- **Reuse the existing unit suites** (`SuperpositionTest`, `DemodulationTest`, `SubsumptionTest`,
  `EqualitySaturationTest`, `DiscountTest`) unchanged — indexing must not alter any result.
- **Reconstruction regression**: `ReconstructionTest` + the `EqFofEvaluation` benchmark's `bad_proof=0` must
  hold (indexing doesn't touch reconstruction, so this is a guard, not new coverage).
- **Micro-tests** per structure: fingerprint compatibility tables (hand-built unifiable/matchable pairs),
  PDT generalization retrieval (with size/age pruning), feature-vector monotonicity (a subsumer's vector is
  componentwise ≤ the subsumee's).
- **Delete/maintenance**: insert then remove (backward simplification) must leave the index equal to
  never-having-inserted (empty-node pruning), tested directly.

---

## 10. Explicitly deferred to Phase 5b (heuristics — after indexing)

Per the user's ordering (indexing first, then heuristics), these are **out of scope for this document** and
listed only so the boundary is clear:

- **Clause selection**: age/weight ratio tuning, better weight functions, the given-clause heuristic.
- **Literal selection** refinements (we already have `CompleteBestLiteralSelector`).
- **Axiom relevance filtering (SInE)** for large-theory problems — our benchmark showed we drown in
  irrelevant axioms on SEU/SET-style problems; this is a large, separate lever, unrelated to indexing.
- **Strategy scheduling** (E/Vampire auto-modes).

Indexing makes each inference *cheaper*; heuristics make us do *fewer, better* inferences. They compose, but
indexing lands first because it is the bigger, more mechanical win and it does not risk completeness.

---

## Appendix — how the three reference provers map operation → structure

| Operation (inference) | **Vampire** | **E** | **Prover9 / LADR** |
|---|---|---|---|
| Superposition / paramod (unification) | substitution tree (`TermSubstitutionTree`, `getUwa`) | **fingerprint** (`FPIndexFindUnifiable`) | **FPA** path index (`UNIFY`) |
| Resolution (literal unification) | `LiteralSubstitutionTree` (`getUnifications`) | fingerprint (literal) | **FPA** via `Lindex` |
| Forward demodulation (generalization) | **code tree** (`DemodulationLHSIndex`) | **perfect discrimination tree** (PDT, size+age) | **bind discrimination tree** (perfect) |
| Backward demodulation (instance) | substitution tree (`getInstances`) | fingerprint (`FPIndexFindMatchable`) | **FPA** (`INSTANCE`) |
| Forward subsumption | substitution-tree generalization + **SAT** verify | **feature-vector** index (`≤` descent) | **bind discrim** (unit) + **feature `di_tree`** (nonunit) |
| Backward subsumption | substitution-tree instances + SAT | feature-vector index (`≥` descent) | **FPA** (unit) + **feature `di_tree`** (nonunit) |
| Subsumption structure | none dedicated (SAT engine) | 17-feature permuted vector trie | integer feature-vector trie |
| Design signature | compiled/substitution trees, allocation-free VMs | fingerprint + PDT + FV — **closest to us** | discrimination + FPA + FV behind a filter/verify façade |

Our plan (§8) is the **E column**: fingerprint for unification/superposition and backward rewriting, perfect
discrimination tree for forward demodulation, feature-vector for subsumption — the combination whose
assumptions match our flat, hash-consed, integer term model with the least engineering for the most speed.
