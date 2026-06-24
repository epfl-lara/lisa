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
