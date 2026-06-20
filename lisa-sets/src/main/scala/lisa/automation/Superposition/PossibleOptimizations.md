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
