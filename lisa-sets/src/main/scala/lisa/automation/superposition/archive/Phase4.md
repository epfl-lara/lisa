# Phase 4 — Equality & Superposition (proposed plan)

> Status: **proposal for review.** Not started. Per project rule, Phase 4 begins only when the user
> explicitly asks. The research grounding this plan is in `Phase4Research.md`.

**Goal.** Make the prover refutationally complete on the **equality** fragment of first-order logic by
adding the superposition calculus — superposition (into positive and negative literals), equality
resolution, equality factoring — plus forward and backward **demodulation**, the **equality literal /
clause ordering**, and the equality **redundancy** handling, all with **full kernel reconstruction**.
Term indexing and portfolio tuning stay in Phase 5; the loop scans the active set linearly, exactly as
Phase 1 resolution does today.

**Non-negotiables (from the theory).** (1) Include equality factoring — omitting it loses completeness.
(2) KBO must stay an admissible reduction ordering (we already check this). (3) Never superpose into a
variable subterm. (4) Rewrite only bigger→smaller, re-checking orientation **after** substitution.
(5) Demodulation may delete its premise only when the redundancy/encompassment gate says the rewrite is
a genuine simplification. (6) Keep the loop fair. See `Phase4Research.md §1.7` for the pitfall list.

---

## Deliverables

1. **`Order.scala`** (new) — the equality literal & clause ordering on top of `KBO`.
2. **`Superposition.scala`** (new) — the four generating equality inferences (or extend `Inference.scala`).
3. **`Demodulation.scala`** (new) — forward + backward demodulation with the redundancy gate.
4. **`Inference.canonicalize`** update — drop `s=s` tautologies; leave `s≠s` for equality resolution.
5. **`Discount.scala`** wiring — register the equality generating inferences and demodulation as
   forward/backward simplification, alongside the existing resolution/factoring/subsumption.
6. **`Reconstruction.scala` + `Justification`** — kernel reconstruction for every new rule.
7. **Tests** in `test/.../superposition/` — inference-level unit tests, end-to-end refutations of
   equality problems (unit-equality UEQ + general), reconstruction kernel-checks, and the FOF/clausal
   benchmark extended to equality problems.

---

## Step 1 — Equality-aware literal & clause ordering (extend + share the existing order)

This step is **smaller than a from-scratch build**: a KBO-based literal order and literal maximality
**already exist and are already used by the loop** — they live as private helpers in
`CompleteBestLiteralSelector` (`Selectors.scala`), which the DISCOUNT loop consults at activation:

* `compareLit` (`Selectors.scala`, private): a **resolution** literal order — compare the two atoms by
  `KBO`, tie-break by polarity (`¬A ≻ A`).
* `maximalFlags` (`Selectors.scala`, private): literal `i` is **maximal** iff no other literal is `Gt`.

Its own doc-comment records the gap: equality atoms are compared "as the ordinary binary symbol
`EqualitySymbol` for now; the proper equality/multiset literal order is a superposition concern." That
distinction is irrelevant to resolution but **load-bearing for superposition completeness** (the
"larger side dominates" and "negative slightly larger" properties come from the multiset encoding). So
Step 1 is the *delta* over what exists — five items, of which #1 extends existing code, #5 is a refactor,
and #2–#4 are the genuinely new primitives:

1. **Make the literal order equality-aware.** Extend `compareLit` so an equality literal is compared by
   the multiset extension of `KBO` over its side-multisets `{s,t}` (positive) / `{s,s,t,t}` (negative).
   Keep the current behaviour for non-equality atoms, plus the level rule: **equality literals rank
   below any non-equality literal** (Vampire's `EQ` = lowest level; no `P(t̄)≈⊤` encoding). The generic
   small-multiset comparator (cancel common elements by hash-cons identity, then domination check via
   `KBO.compare`) is robust for the *partial* order — returns `Inc` on genuinely unordered non-ground
   literals. This upgrade also makes the **selector** properly equality-aware — a strict improvement, not
   a rewrite.
2. **Equation orientation (new).** `orient(atom): Cmp = kbo.compare(arg0, arg1)` and
   `maximalSide(atom): Option[Term]` (the `Gt` side; both sides usable when `Inc`). Nothing orients
   equations today; superposition needs this to know which side to rewrite *from*/*into*. Memoize per
   atom (a hash-consed `Int`) — the analogue of Vampire's cached `getEqualityArgumentOrder`.
3. **Strict maximality (new).** Add `isStrictlyMaximal` (no other literal is `Gt`-**or-`Eq`**), distinct
   from the existing non-strict `maximal` (no other `Gt`). Superposition superposes *from*/*into*
   **strictly** maximal positive literals; only non-strict maximality exists today. `Inc` never demotes.
4. **Clause order (new).** `compareClause` = the same multiset comparator lifted over the clause's
   literal multiset (elements compared by the equality-aware `compareLit`). Needed for superposition's
   "left premise not `≻_C`-≥ right" gate and for demodulation's `isPremiseRedundant`.
5. **Promote into a shared `Order` module.** Lift `compareLit` + maximality out of
   `CompleteBestLiteralSelector`'s private methods into a shared `Order` (holding the `KBO`), and have
   the selector delegate to it, so the selector and the new equality inferences (Step 2) use **one**
   ordering. (Minimal-churn alternative: keep the selector's helpers and have them call shared functions
   — same result, smaller diff. Chosen: promote, for a single source of truth.)

* **Post-σ comparisons.** Superposition/factoring/demodulation compare **already-instantiated** concrete
  terms (we materialize conclusions via `Trail.Applier` anyway), so no substitution-deref machinery is
  needed — call `KBO.compare` on the built terms. (Vampire's lazy `compareUnidirectional` on
  `AppliedTerm`s is a Phase-5 optimization.) Step 1 just exposes the `KBO` handle.

Note: this is all distinct from the *syntactic* `compareLiterals`/`compareStructural` in `Core.scala`,
which stay unchanged as the canonicalization sort key.

**Tests:** orientation (`f(a)≈a → Gt`, `x≈y → Inc`); the equality-multiset corners (`s≉u ≻_L s≈t` and
`s≉t ≻_L s≈t` when `s≻t≻u`); the level rule (`P(a) ≻_L s≈t`); strict-vs-non-strict maximality on
hand-built multi-literal clauses (incl. an `Inc` pair where both are maximal); and a regression that the
existing selector's choices are unchanged on equality-free clauses.

## Step 2 — Generating equality inferences (`Superposition.scala`) — **done**

Mirror the `Inference.resolve`/`factor` idiom: save trail → unify (two scopes for superposition, one for
resolution/factoring) → build the conclusion via `Applier` → apply post-σ **term-orientation** gates →
record `Justification` → restore trail. Take explicit literal/subterm positions (the loop supplies them
from `selected`). Signatures pass the shared `order` (for its KBO + `isEqualityAtom`).

**Eligibility is the loop's concern, not the inference's.** With a Bachmair–Ganzinger selection function a
*selected* negative literal is eligible even when it is not maximal, so an `isMaximal` gate inside an
inference would wrongly block it and lose completeness. The loop (Step 4) therefore passes only positions
drawn from each clause's `selected` set, and these functions enforce only the **term-orientation**
conditions — required for completeness and independent of selection. The post-σ maximality *aftercheck*
(E/Vampire's redundancy pruning — re-checking that σ didn't lift another literal above the worked one) is a
**deferred optimisation**: omitting it over-approximates, which is sound and complete.

* **`superpose(bank, trail, order, from, iFrom, fromSide, into, iInto, uPos)`** — superpose `from`'s
  positive equality `l≈r` (literal `iFrom`, side `fromSide`∈{0,1} = `l`) into `into`'s literal `iInto` at
  non-variable subterm position `uPos` (a path of argument indices, root excluded). Gates: `from`'s literal
  is a positive equality; `u = subterm(into, iInto, uPos)` is **not a variable**; `σ = mgu(l, u)`; post-σ
  `lσ⋠rσ` (reject if `rσ≽lσ`); if `iInto` is an equality, don't rewrite its strictly-smaller side; drop a
  trivial `xσ≈xσ` result. Conclusion replaces `u` by `r` under σ across the union of the two clauses'
  remaining literals. One function covers positive and negative into-literals (polarity of `iInto` carries
  through). The loop enumerates both directions (into-given and from-given) and the eligible `fromSide`
  (the `Gt` side, or both if incomparable).
  * *Pruning (E):* E only superposes **from a predicate literal into maximal negative literals** (into a
    positive predicate would only make a tautology) — a cheap pruning we could add. Note this concerns the
    predicate-atom-as-`P(t̄)≈⊤` view; our design instead routes predicate literals through **resolution**
    (Phase 1), so it applies only if we ever superpose over predicate atoms.
* **`equalityResolution(bank, trail, order, c, i)`** — `c`'s literal `i` is a negative equality `s≉t`;
  `σ=mgu(s,t)`; conclusion `(c\{i})σ`. (That `i` is selected/maximal — hence eligible — is the loop's concern.)
* **`equalityFactoring(bank, trail, order, c, i, iSide, j, jSide)`** — positive equalities `s≈t` (`i`,
  side `iSide`=`s`, the maximal one) and `s'≈t'` (`j`, side `jSide`=`s'`); `σ=mgu(s,s')`; **both**
  orientation gates `sσ⋠tσ` **and** `sσ⋠t'σ` (the shared LHS `sσ` is not `≼` either right-hand side —
  Vampire's two gates `sRHS⋡sLHS`, `fRHS⋡sLHS`). Conclusion **drops the maximal literal `i`, keeps the
  partner `j`**, and adds the disequality of their other sides: `(c\{i})σ` with `tσ≉t'σ` — i.e.
  `(C ∨ s'≈t' ∨ t≉t')σ`. (Vampire *and* E both drop the factored maximal literal and keep the partner; an
  earlier draft of this plan had it mirrored, and had a redundant `(s≈t)σ` maximal gate now moved to the
  loop. E also adds a bare-variable guard: a unified side may not be a lone variable unless the partner is
  an equality.)

**Subterm enumeration** for superposition: `foreachSubterm(bank, atom)(visit)` walks all **non-variable**
proper subterms (root excluded) with a single **reused** position stack (no per-position allocation — the
E/Vampire subterm-iterator style), calling `visit(u, path)`; a position is materialised (`path.toIntArray`)
only when an inference fires. The loop pairs these with eligible literals and, for equality literals,
restricts to the maximal side (both if incomparable). Positions are `Array[Int]`; `subtermAt`/`replaceAt`
navigate and rewrite at one.

**Test (`SuperpositionTest.scala`):** each rule in isolation on hand-built clauses; a small UEQ refutation
end to end (`f(a)≈a`, `¬(f(f(a))≈a)` → □ via superposition + equality resolution); the `s≠s ⇒ □` closure;
the smaller-side and orientation gates.

## Step 3 — Demodulation (`Demodulation.scala`) — **done**

* **Usable-rule test** (`rules(bank, order, eq)`): a positive **unit** equality; oriented side is the
  `Gt` side with `vars(r) ⊆ vars(l)` and `l` not a variable; incomparable equalities usable in a
  direction only if that side's variables cover the other's (E's `getDemodulationLHSIterator` logic).
* **Forward** (`forwardDemodulate(clause, activeUnitEqs)` → `normalForm(..., rules)`): traverse `clause`'s
  non-variable subterms (leftmost-**outermost** via `subtermPositions`; any order reaches a normal form
  since every step strictly decreases); find a usable unit equation whose LHS **matches** (generalization)
  the subterm; rewrite; iterate to a normal form. **Re-check orientation after matching**
  (`KBO.compare(lσ, rσ) == Gt`, with `lσ` the matched subterm) — but **skip the re-check for an
  already-oriented rule** (its instance stays oriented under KBO), as both Vampire (`preordered`) and E
  (`EqnIsOriented`) do. Linear scan of active unit equations (no index — Phase 5).
* **Backward** (`backwardDemodulate(newUnitEq, active)`): when a new positive unit equality arrives, find
  active clauses with a subterm that is an **instance** of its LHS, re-check the instance's orientation,
  and apply the **same redundancy gate** as forward (below) before rewriting; remove the original and
  re-queue the replacement (E re-normalises it from scratch). The redundancy gate applies in **both**
  directions.
* **Redundancy gate** (`isPremiseRedundant`, modelled on Vampire's `DemodulationHelper`): demodulation is
  a *simplification* (deletes/replaces its premise). The gate **only bites when rewriting a whole side of
  a maximal positive equality with a renaming (variant) matcher** — Vampire's encompassment demodulation,
  E's restricted rewriting (`CPLimitedRW`). Everywhere else — rewriting the larger side downward, a proper
  (non-renaming) instance, any subterm strictly inside a side, or any non-equality/negative literal — the
  premise is **always** redundant and freely deletable, so default to *simplify* and guard only that
  narrow case. The gate proper: redundant iff the rewritten side becomes smaller than the untouched side,
  **or** (encompassment) the matcher σ is not a renaming (a proper instance), **or** (standard
  multi-literal) no other literal exceeds the rewrite equation `(u ≈ tgt)`. Prefer **encompassment mode**
  (Vampire's default): multi-literal targets then need no extra check; only positive-unit targets need the
  `isRenaming` test. When the gate fails, **skip the rewrite** — do *not* emit it as a generated clause:
  superposition (Step 2) already covers that inference, exactly as Vampire (`continue`) and E do.

**Test (`DemodulationTest.scala`):** forward normal-forming of a clause by oriented equations (ground and
with variables); backward rewriting of a stored clause by a new equation; the orientation-after-matching
guard (an unoriented commutativity rule rewrites only the `≻` instance); the redundancy gate deciding
simplify-vs-**skip** (a renaming matcher on the big side of a positive unit equality must not simplify; a
proper instance does).

## Step 4 — Loop wiring (`Discount.scala`) and `canonicalize` — **done**

The equality inferences slot into the points `Discount` already has for resolution/subsumption, in the
E/Vampire order — **forward-simplify given → activate → backward-simplify active → generate → forward-
simplify each new clause → passive**, all against the **active** set only (DISCOUNT). Steps 1–3 shifted
work into the loop, so this is more than "register alongside resolution/factoring":

* **Single shared `Order` — done.** The `TermBank` now owns a lazy `bank.order` (one `KBO`, one `orient`
  cache). The selector (`Bridge`), the generating inferences, demodulation, and `Discount`'s `factorAfterCheck`
  all use `bank.order`; the per-consumer `new Order(new KBO(bank))` is gone. So the loop wiring just threads
  `bank.order` into the new inference calls.

* **Generating inferences at activation — eligibility = `gSel`.** Step 2's inference functions do *not*
  check maximality (they enforce only term-orientation); the loop supplies eligible literals. Reuse the
  existing `gSel = gc.select(bank)` (now equality-aware, from Step 1) as the eligibility set, and in
  `activate` enumerate, for the given × each active clause (and the given with itself):
  * **Superposition, both directions** — for each eligible **positive-equality** literal as `from`, each
    usable `fromSide` (the `Gt` side; both if `Inc`), and each eligible literal of the other clause with
    each non-variable subterm position from `Superposition.subtermPositions` (restricted to the maximal
    side for equality into-literals). Run given-as-`from` **and** given-as-`into`.
  * **Equality resolution** — each eligible **negative-equality** literal of the given.
  * **Equality factoring** — each pair of eligible **positive-equality** literals of the given, over the
    side pairings.
* **Exclude equality literals from *ordinary* resolution.** The current resolution scan runs over all
  selected literals; once superposition + equality-resolution own equality, resolving on `=` atoms (as an
  uninterpreted predicate) is redundant/off-calculus (E and Vampire never do it). Guard the resolution
  path with `!isEquality`, exactly as the factoring path already does.

* **Demodulation as forward/backward simplification.**
  * *Forward* — `Demodulation.normalForm` (returns the normal form, or the same clause unchanged)
    joins the existing `forwardSimplify` scan for the given and the `forwardSimplifyAtGeneration` path in
    `addPassive` for each new clause.
  * *Backward* — when the given is a positive unit equality, `Demodulation.backwardDemodulate` returns
    `(A, B)` pairs; in `backwardSimplify`, **remove `A` from active and `addPassive(B)`** (re-queue the
    replacement, mirroring the existing backward-subsumption wiring — but with a replacement, not just a
    deletion).
  * Maintain a **demodulator set**: the subset of active that are positive unit equalities (cache their
    extracted `rules` rather than re-deriving on every forward-demodulate).

* **`canonicalize` drops `s=s` positive tautologies** (currently deferred, `Inference.scala:65`);
  superposition already drops the *target* `x≈x`, but residual `s=s` (from equality factoring, or a
  superposition residual) still needs `canonicalize`. `s≠s` is left for equality resolution to close.

* **Fairness** is already provided by the given-clause discipline; demodulation/subsumption must not
  indefinitely starve generation.

**Test:** end-to-end UEQ and equality-FOF refutations combining resolution, superposition, and
demodulation; a saturation (satisfiable equality set) terminating in `Saturated`; equality literals are
not double-handled by ordinary resolution; a regression that Phase 1–3 no-equality behavior is unchanged.

## Step 5 — Reconstruction (`Reconstruction.scala` + `Justification`) — **done**

**Implemented** exactly as planned below, in `Reconstruction.scala` only (no other production file changed).
`build` now dispatches the four cases to `buildSuperposition` / `buildDemodulation` (sharing one
`buildRewrite` core) / `buildEqualityResolution` / `buildEqualityFactoring`. Superposition and demodulation
emit `RightSubstEq`/`LeftSubstEq` (polarity of the rewritten literal picks Left vs Right) adding `lσ=rσ` to
the antecedent, then `Cut` the (possibly reoriented) equation-bearing parent instance on `lσ=rσ`; equality
resolution is one `LeftRefl` on the unified `sσ=sσ`; equality factoring is one `RightSubstEq` (plus a
`flipEqRight` reorientation when the dropped and kept sides disagree). The fresh-variable numbering of each
conclusion is reproduced by re-running the `Applier` in the *generating code's exact order*. Reversed
stored-side orientation is handled by `flipEqRight` (a `RightRefl`+`RightSubstEq`+`Cut` micro-derivation of
symmetry). Kernel-checked end-to-end (`ReconstructionTest`'s equality cases: superposition, equality
resolution, demodulation incl. the flip) and at the individual-inference level (`EqualityReconstructionTest`:
superposition into positive/negative literals, both from-orientations, non-unit from-clause, and equality
factoring with/without reorientation).

The four `Justification` cases (`Superposition`, `EqualityResolution`, `EqualityFactoring`, `Demodulation`)
**already exist** (added during Steps 2–4) and were previously stubbed in `Reconstruction.build` with a
`NotImplementedError`; this step replaced the stubs. Each records parents + literal/subterm positions (as
`Array[Int]`) plus just enough to recompute the substitution — **no stored unifier** (recompute from
positions, as we do for resolution and as LADR's `para_pos` does): `Superposition` stores `fromSide`,
`Demodulation` stores `rule`/`ruleSide`, `EqualityFactoring` stores the two unified sides
(`droppedSide`/`keptSide`), and `EqualityResolution` needs no extra (both sides of one literal). For each,
build the small kernel subproof:

* **Superposition / demodulation** — a rewrite of `u` to `r` (or `l` to `r`) under the recomputed
  unifier: kernel `RightSubstEq`/`LeftSubstEq` with the equation as the substituted equality and the
  literal's context as `lambdaPhi`. Polarity of the rewritten literal selects Left vs Right.
* **Equality resolution** — instantiate `s≉t` with `σ` (making both sides identical), then close with
  `LeftRefl`/`RightRefl` on `sσ = sσ`.
* **Equality factoring** — combine the two equalities and the introduced `t≉t'` via `SubstEq` + the
  existing resolution/cut plumbing.

Reuse the existing reconstruction scaffolding (the same "re-unify recorded literals, then emit kernel
steps" flow already used for `Resolution`/`Factoring`). Kernel-check every reconstructed proof in tests.

## Step 6 — Benchmarks

Extend the existing evaluation (`Evaluation.scala`/`FofEvaluation.scala`) with an **equality** problem
set drawn the same way as the current ones (TPTP `SPC`), now **allowing equality** (UEQ unit-equality
first, then general FOF with equality; still no arithmetic). Report refuted/saturated/timeout and
per-phase timing, certified vs uncertified, as we already do — this is how we'll know Phase 4 works at
CASC-relevant scale.

---

## Explicitly out of scope (Phase 5+)

* **Term indexing** (discrimination / substitution / code / fingerprint / feature trees) — the active
  set is scanned linearly in Phase 4.
* **LPO** and precedence/weight-generation schemes; **portfolio/CASC** scheduling.
* **Substitution-lazy ordering** (`compareUnidirectional`/`AppliedTerm`), demodulation step/size limits,
  SAT-based subsumption, subsumption-demodulation, **AVATAR**.
* **Basic superposition / constraint-based redundancy** refinements.

## Verification

`sbt lisa-sets/compile`, then `sbt "lisa-sets/testOnly lisa.automation.superposition.*"`. Every
end-to-end test must **kernel-check** the reconstructed `SCProof` of the original goal. The completeness
smoke test: the equality problems that currently `Saturated` (no equality reasoning) must now refute.
</content>
