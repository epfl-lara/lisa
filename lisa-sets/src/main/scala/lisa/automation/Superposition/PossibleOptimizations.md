# Possible optimizations / deferred work

Items noted during review but intentionally not acted on yet.

## R1 — Unbounded recursion depth (robustness)

`occursRec`, `traverseContains`, `traverseFirstVar`, and `Applier.apply` recurse on term
depth. `unify` was deliberately made iterative (explicit worklist) to avoid a
`StackOverflowError` on deeply nested terms, but these four are still recursive. A
pathologically deep term could overflow the JVM stack.

If this ever bites, convert them to explicit-stack iteration (as `unify` already is), or add
a depth guard. Lower priority than `unify` since these run on normal-depth terms in practice.

## Other deferred notes

- The `intern` map (`Int2IntOpenCustomHashMap`) stores `offset -> offset`, so its value
  column duplicates the key column (one extra `int` per term). Unavoidable without a
  hand-rolled open-addressing table, since fastutil's primitive `IntOpenCustomHashSet` has no
  `addOrGet` to retrieve the canonical stored element. Minor memory cost.
- Capacity doublers (`ensureMem`, `ensureVarCapacity`, trail growth) use `* 2`, which would
  overflow `Int` near `2^30` elements (multi-GB structures). Unreachable in practice; a
  guard would be defensive.
- `Justification` (in `Core.scala`) holds parent **clause references**, so a retained clause keeps
  its whole derivation DAG alive even if those ancestors were deleted from the active/passive sets.
  This is the standard cost of pointer-based derivations (Vampire ref-counts; E/Prover9 keep ids +
  a clause table and can free non-proof clauses). Fine for Phase 1; revisit if memory bites — switch
  to clause ids + a table, or drop derivations of clauses provably not on any proof path.

## `occurs` clean-set, and per-term scratch (deferred — revisit in Phase 2/3)

`Trail.occurs` uses `occursClean`, a per-scope `IntOpenHashSet` of derefed terms proven free of the
searched variable (avoids re-walking shared subterms; cleared at the start of each `occurs`).

On the cost: `IntOpenHashSet.clear()` is `Arrays.fill` over the whole backing array, i.e.
`O(capacity)`, not `O(size)` (with an `O(1)` early-return when empty); iteration would likewise be
`O(capacity)` — both intrinsic to open addressing. But this is a near-non-issue: the set only grows
to the largest occurs seen, so a small term keeps it small and `clear()` cheap; the only mildly
costly pattern is one big occurs ballooning the table followed by many small ones eating the
persisted-capacity clears.

Options considered for a hard bound:
- **Size-gate**: skip the memo entirely for small terms (use cached `weight` as the size proxy) so
  it only grows/clears for large terms. Simplest; zero extra memory. The cheap stopgap if needed.
- **Sparse set** (dense list + `sparse: int[U]` index): `O(1)` clear and `O(size)` iteration, but
  `U` = arena size, so ≈ doubles the bank's memory. Overkill here.
- **Per-term epoch-stamped scratch**: a scratch field on each term record + a global epoch; mark =
  `stamp = epoch`, test = `stamp == epoch`, clear = `epoch += 1` (`O(1)`, touch nothing). This is the
  elegant endpoint and how mature provers do it.

Conclusion: **deferred.** Per-term timestamped scratch is near-certain future demand — Phase 2/3
rewrite / normal-form caching (E stamps `TermCell` with a `SysDate`; Vampire caches reduced forms)
plus general traversal marks — but its *shape* depends on the rewriting layer we haven't built
(rewrite caching wants `(normalForm, date)`; `occurs` wants two per-scope marks), and it's pure
optimization. Adding a header word later is cheap and localized: bump `HeaderWords` and the accessors
follow, and hash-consing already hashes/compares only identity words (`functor`/arity/children, not
`fvMask`/`weight`), so a mutable scratch word is naturally excluded from term identity. So add
epoch-stamped scratch when Phase 2 defines the need, sized to it, and route `occurs` through the
traversal-mark part then (retiring `occursClean`). Don't pre-commit a layout now.

## Subsumption matcher (`Subsumption.scala`, Phase 2) — deferred refinements

`subsumes` already applies the O(1) `sigSubsumes` pre-filter (size / pos / neg / weight / `predBits`),
a `□` and a unit fast path, an injective backtracking matcher (`matchRec`, heaviest-`c`-literal-first
via `orderByWeightDesc`), and **Check 1 — per-literal weight skip** (E `ccl_subsumption.c:541`): a
target literal is skipped before `matchLiteral` unless `literalWeight(target) >= literalWeight(ci)`,
which is necessary since `ci σ = target ⇒ weight(target) >= weight(ci)`. Two further E-style
refinements are deferred. **Both are pure optimizations — they must not change the boolean result of
`subsumes`** (guard with a brute-force differential test before trusting either).

- **Check 2 — subsume-order literal sorting + early cut-off** (E `ccl_subsumption.c:531-535`). E keeps
  both clauses' literals in a quasi-order so the matcher can `continue` past too-big candidates and
  `return false` once it passes too-small ones, instead of my pure heaviest-first heuristic with a full
  inner scan. Port:
  - A total comparator `compareSubsume(bank, l1, l2)` next to `compareLiterals` in `Core.scala`,
    ascending by the keys matching respects: **(1) polarity, (2) head predicate symbol** (both invariant
    under matching), **(3) `literalWeight`** (non-decreasing under matching), **(4) `compareStructural`**
    tie-break (→ total/deterministic). Then `ci` can match target `dj` only within the *contiguous block*
    of `d` sharing `ci`'s polarity+predicate with `weight >= weight(ci)`.
  - A **cached index permutation** on `Clause`, `_subsumeOrder: Array[Int]` computed lazily, mirroring
    `_selected` (immutable literals → safe to cache; amortizes the sort of a target `d` checked against
    many subsumers in forward subsumption). **Must be a separate index array — never permute
    `literals`**, since `Justification.Resolution`/`Factoring` store literal *indices* into it.
  - In the matcher, iterate `d`'s candidates for `ci` over `d.subsumeOrder`: skip groups whose
    `(polarity, pred)` is below `ci`'s, scan `ci`'s group from the first `weight >= weight(ci)` entry
    (skipping `used` ones), and **break** as soon as `(polarity, pred)` exceeds `ci`'s. The injective
    `used[]` set still applies (used candidates skipped within the block; contiguity preserved).
  - *Optional* stronger `c`-branching: order `c`'s literals **most-constrained-first** (fewest candidates
    in their `(polarity, pred, weight>=)` block within `d`) instead of pure heaviest-first.
  - Correctness note to document: every skip/break only discards a `dj` that provably cannot match `ci`
    (wrong polarity/predicate, or too light), so reachable matches are unchanged.
  - **Cost/benefit:** payoff scales with literals-per-clause and per-predicate fan-out; most clausal
    clauses have 2–4 literals, so over our benchmark the delta vs. Check 1 alone may be small. E-standard
    and a clean stepping stone to Phase-4 indexing — worth doing, but **gate "keep it" on the benchmark**
    (it's fine to ship Check 1 alone). Loop-level impact is only measurable once subsumption is wired into
    `Discount` and run on the seed-42 benchmark.

- **Check 3 — finer symbol filtering: deferred to Phase 4 (indexing).** Our coarse `predBits` (1 bit per
  head symbol mod 64, OR-ed) is the right Phase-2 cost/benefit point under a linear active scan. The
  finer discriminators both belong with term indexing, not the linear scan:
  - *E*'s **feature-vector index** (`ccl_freqvectors.c`): a trie over `[pos_lit_no, neg_lit_no]` then,
    **per symbol**, `{occurrences in pos lits, occurrences in neg lits}` (+ optional `{max depth pos,
    max depth neg}`), retrieving only clauses dominated feature-by-feature — per-symbol *counts*, where
    `predBits` is per-symbol *presence* (and collides mod 64).
  - *Vampire*'s **literal substitution-tree index** (`ForwardSubsumptionAndResolution.cpp`): queries each
    candidate literal for generalizations, so retrieval itself enforces predicate/polarity/matchability —
    no clause-level fingerprint at all. (Vampire's only clause-level numeric test is `length`.)
  - Plan for Phase 4: replace the linear active scan + `predBits` with one of these indexes. No code now.
  - *Optional* near-free Phase-2 middle ground (not adopted — we deliberately keep `predBits` coarse):
    split into `posPredBits` / `negPredBits` (head symbols in positive vs. negative literals); subsumption
    then needs `posPredBits(c) ⊆ posPredBits(d)` **and** `negPredBits(c) ⊆ negPredBits(d)` — strictly
    stronger, still two `Long` ANDs, at the cost of one extra field per `Clause`.

## Complete general subsumption resolution (Phase 2 P1) — deferred

`Subsumption.subsumptionResolutionResolvent` does subsumption resolution (delete literal `K` from `main`
using side `C' ∨ L` with `Lσ = ¬K` and `C'σ ⊆ main \ {K}`). It builds the result via `Inference.resolve`
(an ordinary resolvent ⇒ no new justification/reconstruction) and **keeps it only when it `subsumes`
`main`** — a completeness gate.

The gate is **conservative**: `resolve`'s mgu binds only `L`'s variables, so when `C'` has a variable not
in `L`, the built clause is `C'σ₀ ∪ M'` (that variable left free), which need not entail `main`, so the gate
declines and that SR step is missed. (Deleting it anyway would not be unsound — the prover never derives a
false `□` — but would break **completeness**: it could discard a clause a refutation needs and wrongly
saturate. This was caught on seed 42, `SYN036-4` going `REFUTED → SATURATED`, before the gate was added.)

A **complete** version (capturing the free-`C'`-variable cases) needs the *full* matcher σ, not just
`resolve`'s mgu: match `L`↔`¬K` and `C'`↔`M'` to get σ (already done by a `matchTerm` + `matchRec` pass),
build `main \ {K}` by dropping `K` and densely renumbering, and record a
`Justification.SubsumptionResolution(side, sideLit, main, mainLit)` whose reconstruction instantiates `side`
by σ, resolves with `main`, then canonicalises (`Reconstruction.scala`, `Core.Justification` + its `age`
rule — the Phase2.md §7 plan). Deferred: the conservative gate already captures the common (shared-variable)
cases at no reconstruction cost; the complete version adds kernel-reconstruction complexity for the rarer
free-variable cases. Revisit if a benchmark shows those cases matter.

## KBO vs. E / Vampire — feature gap (for when we revisit)

How our KBO (`KBO.scala`) compares to E (`cto_kbolin.c`) and Vampire (`KBO.cpp`). Rows below
"Substitution" are scope we deliberately don't cover yet.

| Dimension | E (`cto_kbolin.c`) | Vampire (`KBO.cpp`) | Ours (`KBO.scala`) |
|---|---|---|---|
| Control flow | recursive compare + iterative balance sweeps | fully iterative (explicit `Stack`) | fully recursive |
| KBO weight | not cached — accumulated each traversal | lazy per-term memo (`kboWeight`) | eager per-term, baked in arena |
| Variable balance | dense `int* vb` + `max_var` watermark | sparse `DHMap<unsigned,int>` | dense `Array[Int]` + `maxVar` (E-style) |
| Skip identical args | no | yes (`equalsShallow`) | yes (`==`, via hash-consing) |
| Pacman (strip common unary head) | yes | no | yes |
| Ground fast path | no | no (but weight memo) | yes (`compareGround`) |
| Precedence | total **or** partial (n² matrix) | total (int) | total (int) |
| Substitution | `DerefType` everywhere | `AppliedTerm` everywhere | none (concrete only) |
| Unidirectional "greater" | no (full compare) | yes (`compareUnidirectional`) | no (deferred) |
| Higher-order | yes (LFHO + λ) | no (this class is FO) | no |
| Literals / equality order | via equations | `comparePredicates` + `Ordering_Equality` | deferred to Phase 1 |
| Weight generation / specials | configurable schemes | many schemes + theory/numeral/FOOL/color | all weights default 1, set manually |
| Admissibility check | OCB setup | `checkAdmissibility` in ctor (throw/warn) | `checkAdmissibility(): Option`, not auto-run |

Key architectural divergence: we bake the KBO weight into each term at construction (one weight
assignment, fixed before terms are built) rather than holding it in the ordering object — this is
what unlocks our ground fast path and ground-subterm short-circuit, but precludes two KBOs with
different weights over the same bank. The deferred substitution-aware path would reintroduce weight
accumulation (no cache for `σ(s)`); the unidirectional path is the hot one for demodulation.

## DISCOUNT loop (`Discount.scala`, Phase 1) — deferred work

- **Passive queues: a binary heap + a FIFO, with lazy deletion.** `byWeight` is a binary-heap
  `mutable.PriorityQueue` on `(weight, id)`; `byAge` is a plain FIFO `mutable.Queue` (clauses are
  enqueued in strictly increasing `id`, so the front is already the oldest — no heap needed there).
  Each clause sits in both; selecting via one leaves a **stale** entry in the other, skipped on pop via
  the `livePassive` id set. Cost: `O(log n)` weight pop, `O(1)` age pop, plus the skipped stales. We use
  lazy deletion because neither a heap nor a FIFO supports cheap **arbitrary** removal.
  - *Vampire* keeps **both** the age and weight queues as **skip lists** (`ClauseQueue`) and does
    **real** removal: `popSelected` removes the chosen clause from the other queue, and `remove(cl)`
    deletes a simplified clause from both (`O(log n)` expected each). The ordered structure also feeds
    its LRS (limited-resource) lookahead, which iterates the queues in order.
  - *E* keeps each of several weighted evaluation queues as a **self-adjusting BST** (`EvalTree` —
    historically AVL, now splay), keyed by `(priority, heuristic)`, with `O(log n)` insert /
    find-smallest / extract — again real removal, generalised to N queues.
  - The deciding factor is **arbitrary removal**: a heap has great constants and `O(1)` peek but `O(n)`
    arbitrary delete; skip lists / balanced BSTs give `O(log n)` insert / find-min / **remove** (and
    ordered iteration) at higher constants. Lazy deletion is fine for Phase 1, where a clause leaves
    passive only by being selected. Once **Phase-2 simplification** deletes *passive* clauses (backward
    subsumption, etc.), stale entries accumulate — that is when to switch `byWeight` to a
    remove-capable structure (a skip list à la Vampire, or a splay tree à la E).
- **Active set is scanned linearly** for resolution partners. Term indexing (discrimination /
  fingerprint / substitution trees) is Phase 4 — that's the real scaling fix.
- **No simplification yet** (Phase 2): no forward/backward subsumption, no demodulation. Passive can
  accumulate duplicate or subsumed clauses; correct but not minimal.
- **Selectors.** Two share Comparator10 (colour key dropped → `NegativeEquality → weight → Negative →
  Lex`, factored out as `compareLiteralQuality` in `Selectors.scala`):
  - `BestLiteralSelector` = Vampire's `BestLiteralSelector<Comparator10>` (incomplete selector
    **1010**): argmax over the comparator, one literal. **Not** BG-complete — a positive that
    outweighs every negative is selected even when negatives are present.
  - `CompleteBestLiteralSelector(kbo)` = Vampire's default selector **10**: BG-complete. Best-negative
    ⇒ select it; else a quality-competitive negative, else **all ordering-maximal** literals. This is
    the first place the `KBO` touches the loop — via a resolution **literal ordering** (atoms by KBO,
    polarity tie-break ¬A ≻ A) and a per-clause maximal-literal scan in `CompleteBestLiteralSelector`.
  Still open: (a) Vampire's selector **1** (`MaximalLiteralSelector`) is now a few lines on the same
  maximality machinery, not yet added; (b) the literal order treats equality as the ordinary binary
  symbol — the proper equality/multiset literal order is a Phase-3 (superposition) concern; (c) the
  default `bank.selector` is still `BestLiteralSelector` (making selector 10 the default would require
  the bank to own a `KBO`). `FirstNegativeSelector` remains as a simple alternative. The loop routes
  all selection through `bank.selector` at activation.
