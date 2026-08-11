# Phase 4 Research — Equality & Superposition in Vampire, E, and Prover9

A source-level study of how the three reference provers handle equality, the underlying theory,
and how each piece maps onto our implementation (`Core`, `KBO`, `Inference`, `Discount`,
`Reconstruction`). This is the input to the Phase 4 plan (`Phase4.md`). Everything here is grounded
in the read-only clones under `othersolvers/` and in our own sources; file:function pointers are
given so claims can be checked.

---

## 0. Executive summary

* **The calculus we must implement is superposition** (Bachmair–Ganzinger), not raw paramodulation.
  Superposition = ordered paramodulation + ordered-resolution's maximal-literal/selection machinery
  + the **"don't superpose into variables"** restriction + a **redundancy criterion** that licenses
  demodulation/subsumption/tautology-deletion. All three provers implement essentially this; Prover9
  is the "oldest" (ordered paramodulation with whole-literal maximality, superposition-into-variables
  as a *flag*), E and Vampire are full modern superposition.

* **The minimal complete core is exactly four rules** plus the right orderings and redundancy:
  1. (positive & negative) **Superposition**,
  2. **Equality Resolution**,
  3. **Equality Factoring**,
  parameterized by a **reduction ordering total on ground terms** (KBO/LPO), lifted to a **literal
  ordering** (equations as multisets `{s,t}` / `{s,s,t,t}`) and a **clause ordering** (multiset of
  literals), plus a **fair saturation loop with redundancy-based simplification**.

* **We already have the load-bearing infrastructure**: a hash-consed term bank with `EqualitySymbol=0`
  reserved (`Core.scala:53`), a correct linear KBO on ground/non-ground *terms* (`KBO.scala`), the
  DISCOUNT loop (`Discount.scala`), the redundancy machinery (`Subsumption.scala`), and kernel
  reconstruction that already uses the equality rules' cousins. **The gaps are specific and bounded**
  (below).

* **The four gaps Phase 4 must close**:
  1. **No literal/clause ordering.** `KBO.compare` orders *terms* only; `compareLiterals`
     (`Core.scala:394`) is a *syntactic* sort key, not the semantic multiset literal order. We must
     add an equation-aware literal ordering and a clause ordering on top of `KBO`.
  2. **No equality inferences.** `Inference` has `resolve`/`factor`/`canonicalize` only; superposition,
     equality resolution, and equality factoring do not exist.
  3. **No demodulation** (forward or backward) and **no `s=s` tautology / `s≠s` handling**
     (`canonicalize` explicitly defers equality trivials, `Inference.scala:65`).
  4. **Reconstruction** has no equality-inference cases; the kernel rules to build them
     (`LeftSubstEq`/`RightSubstEq`/`LeftRefl`/`RightRefl`) exist but are unused.

* **Term indexing stays in Phase 5** (per `PLAN.md`). Phase 4 scans the active set linearly, exactly
  as Phase 1 resolution does today. This is the single most important scoping decision: it keeps
  Phase 4 about *correctness and completeness of equality*, not performance.

---

## 1. Theory: the superposition calculus (what we must be faithful to)

### 1.1 Lineage — why superposition, not paramodulation

Plain resolution is complete without equality; axiomatizing equality (reflexivity, symmetry,
transitivity, congruence) is catastrophic because transitivity/congruence unify with everything.
Equality must be **built into the inference machinery**:

* **Paramodulation** (Robinson–Wos): one rule — rewrite a subterm unifiable with `l` by `r` from an
  equation `l≈r`. Complete but explosive: (a) `≈` is symmetric so every equation rewrites both ways;
  (b) completeness naively required paramodulating *into variables*.
* **Ordered paramodulation**: fix a term ordering `≻`, only rewrite the bigger side to the smaller
  (`r ⋠ l`). Orients equations like Knuth–Bendix completion.
* **Superposition** (Bachmair–Ganzinger ~1990–94): ordered paramodulation **+** ordered-resolution's
  maximal-literal/selection restriction **+** the **"`u` not a variable"** restriction (which is
  what actually kills the blow-up) **+** a **redundancy criterion** derived from the model-construction
  completeness proof (this is what makes demodulation/subsumption/deletion *provably* sound to apply).

### 1.2 The reduction ordering `≻`

Must be a **reduction ordering total on ground terms**: a strict partial order that is well-founded,
stable under substitution (`s≻t ⟹ sσ≻tσ`), monotone in contexts (`s≻t ⟹ u[s]≻u[t]`), and total on
ground terms. Ground-totality is what lets the completeness model construction always orient a ground
equation; non-ground incomparability is fine. KBO and LPO are **simplification orderings** (subterm
property `s▷t ⟹ s≻t`), hence automatically reduction orderings over finite signatures.

**KBO** (weight-based): admissible weight function (variables weight `w₀>0`; constants `≥w₀`; at most
one unary symbol may weigh 0, and it must be precedence-maximal), extend additively to terms; compare
by variable-count condition + weight, then precedence, then lexicographic on arguments. **Linear
time.** **LPO** (precedence-only, recursive path order): quadratic, sometimes orients where KBO can't.
Portfolios run both.

### 1.3 Lifting to literals and clauses

* A positive literal `s≈t` ↦ multiset `{s,t}`; a negative literal `s≉t` ↦ `{s,s,t,t}`. The **literal
  ordering `≻_L`** is the multiset extension of `≻`. Consequences: comparison is governed first by the
  **larger side** of each equation; a **negative literal is slightly larger** than the positive one on
  the same terms (mirroring resolution's preference for negatives); non-equality atoms are handled by
  a predicate encoding (`P(t̄) ≈ ⊤`, `⊤` minimal) or given a level above equality.
* A clause is a multiset of literals; the **clause ordering `≻_C`** is the multiset extension of `≻_L`.
  Well-founded and total on ground clauses — what the completeness induction needs.
* **Maximal** literal: none `≻_L`-greater in the clause. **Strictly maximal**: none `⪰_L`. On the
  ground level "strictly maximal" = unique largest.

### 1.4 The four inference rules (exact side-conditions)

Side-conditions applied **after** the unifier `σ`. `D',C'` are the remaining literals.

**Positive superposition** (into a positive literal):
```
   D' ∨ l≈r        C' ∨ s[u]≈t
  ─────────────────────────────    σ = mgu(l,u)
      (D' ∨ C' ∨ s[r]≈t) σ
```
with: `u` **not a variable**; `lσ ⋠ rσ` (rewrite bigger→smaller); `sσ ⋠ tσ`; `(l≈r)σ` **strictly
maximal** in its clause; `(s≈t)σ` **strictly maximal** in its clause; left premise not `≻_C`-≥ right.

**Negative superposition** (into a negative literal): identical, except the into-literal `(s≉t)σ` need
only be **maximal** (not strictly) — negatives are already largest by the `{s,s,t,t}` weighting.

**Equality resolution**:
```
   C' ∨ s≉t
  ──────────    σ = mgu(s,t),  (s≉t)σ maximal
     C' σ
```
The rule that closes disequalities and ultimately yields `□`.

**Equality factoring**:
```
   C' ∨ s≈t' ∨ s≈t
  ─────────────────────    σ = mgu(s,s'),  sσ⋠tσ,  (s≈t)σ maximal
   (C' ∨ t≉t' ∨ s≈t) σ
```
Needed for completeness (the "two maximal positive equations sharing the larger side" case that
neither superposition nor equality resolution can close). *Omitting it is a classic completeness bug.*
Merging paramodulation is the alternative that closes the same case.

**Why each restriction is complete-preserving** (from the model construction): superposition into a
variable position is redundant because the variable's ground binding is already reducible (the
"reducible variable" case) — so it's *unnecessary* and forbidding it removes the explosion; rewriting
bigger→smaller keeps the built model a terminating rewrite system; the (strict) maximality restriction
confines inferences to the literal that "decides" the clause in the candidate model.

### 1.5 Selection

A **selection function** picks a set of **negative** literals per clause. **Eligible literal**: if any
literal is selected, inferences must use a selected (negative) one; otherwise a (strictly) maximal one.
Completeness holds for *any* selection that selects only negatives (empty selection allowed). This is
the same mechanism our `Selectors.scala` already provides for resolution.

### 1.6 Redundancy and the completeness proof (why we can simplify)

The completeness proof builds a **candidate ground model** as a convergent rewrite system, processing
ground clause instances in `≻_C` order; a clause "produces" a rule `s→t` iff its maximal literal is a
strictly-maximal positive equation, false in the model-so-far, with `s` irreducible. If a set is
**saturated up to redundancy** and lacks `□`, this `R` is a model ⇒ satisfiable. Contrapositive:
unsatisfiable saturated set contains `□`.

**Redundancy**: a ground clause is redundant if entailed by `≻_C`-**smaller** instances; an inference
is redundant if its conclusion is entailed by clauses smaller than its maximal premise. Because the
model construction only ever appeals to *smaller* clauses, redundant clauses can be deleted and
redundant inferences skipped **without losing completeness**. This licenses:

* **Demodulation / ordered rewriting** by an oriented unit equation `lσ≻rσ` (the rewritten clause is
  smaller and, with the equation, entails the original ⇒ original redundant). **Orientation must be
  re-checked after matching.**
* **Tautology deletion** (`s≈s`, complementary literals): entailed by ∅ ⇒ redundant.
* **Subsumption**: subsumed clause entailed by the simpler subsumer ⇒ redundant.

**Fairness**: every non-redundant inference from persisting clauses must eventually be performed.

### 1.7 The pitfalls (things that silently break completeness)

1. Forgetting **equality factoring** (or merging paramodulation).
2. A wrong ordering (not stable/monotone/well-founded/**ground-total**).
3. Superposing into variables (explosive) or "optimizing" away the reducible-variable handling.
4. **Over-aggressive deletion**: demodulating with an **unoriented** rule, or deleting clauses that
   aren't entailed by strictly-smaller ones.
5. **Unfair** saturation (starving a needed inference).
6. Bad selection (selecting positives; some destructive-equality-resolution variants are incomplete —
   arXiv 2405.03367). Default: select only maximal negatives, or nothing.
7. Requiring only "maximal" where the calculus needs **strictly** maximal.

---

## 2. How the three provers implement it

### 2.1 Inference rules

**Vampire** (`Inferences/Superposition.cpp`, `EqualityResolution.cpp`, `EqualityFactoring.cpp`,
`Kernel/EqHelper.cpp`). One `Superposition` generating engine runs **both directions**: *forward*
(rewrite into the given clause; query `SuperpositionLHSIndex` for a unifiable equation LHS) and
*backward* (rewrite from the given clause's equation into others; query `SuperpositionSubtermIndex`).
Positive vs negative superposition is not two rules — the rewritten literal may be either polarity; the
rewriting equation must be positive (`EqHelper::getSuperpositionLHSIterator` returns nothing for
negative equalities). The gates (all in code): only selected literals
(`Clause::getSelectedLiteralIterator`); only non-variable, non-type subterms
(`EqHelper::getSubtermIterator` uses `NonVariableNonTypeIterator`); rewrite only *from* the maximal
side of a positive equality (`getLHSIterator` yields only the `GREATER` side, both if incomparable);
post-unification `isGreaterOrEqual(tgtTermS, rwTermS)` rejects rewriting by a `≥` term
(`Superposition.cpp:330`); reject rewriting the strictly-smaller side of an equality (`:335`);
equational-tautology drop (`isEqTautology`); and a **maximality aftercheck** (`:376`) that re-verifies
selected-literal maximality after σ (since unification can enlarge other literals). Equality resolution
and factoring have their own order gates (factoring's two `⊁` checks, `EqualityFactoring.cpp:121`).

**E** (paramodulation core in `cco_*`, ordering in `cto_*`). Same modern superposition; generation is
factoring + equality-resolution + paramodulation, collected then simplified at clause processing.

**Prover9/LADR** (`paramod.c`: `para_from_into`/`para_into`/`paramodulate`). This is **ordered
paramodulation**, not full superposition — a useful "what to do differently" contrast: LADR enforces
orderedness only at (a) from-side orientation (`orient_equalities`/`para_from_right`) and (b)
**whole-literal maximality** (`from_parent_test`/`into_parent_test`/`maximal_literal`), *non-strict and
sign-agnostic*. The finer superposition side-conditions — strict maximality, rewrite-only-into-maximal-
side, and **no-superposition-into-variables** — are **optional flags** (`Para_into_vars`,
`Basic_paramodulation`, `Check_instances`), not hard conditions. That is exactly why paramodulation is
weaker/more explosive than superposition. Reconstruction analogue: `para_pos`/`para_pos2` deterministically
replay the paramodulant from recorded positions — the same "recompute the unifier from stored positions"
idea we already use.

### 2.2 Term ordering (KBO/LPO)

All three implement KBO via **Löchner's linear variable-balance sweep** — the exact algorithm our
`KBO.scala` already ports:

* **E** `cto_kbolin.c` (`kbolincmp`, `KBO6`): accumulators `wb` (weight balance), `vb[]` (per-variable
  balance), `pos_bal`/`neg_bal`; decision `wb>0 ⇒ (neg_bal?Inc:Gt)`, tie-break precedence, then saved
  lex result. Older recursive `cto_kbo.c` recomputes weights per level (quadratic). LPO/LPO4 in
  `cto_lpo.c`. The `CompareResult` enum (`clb_partial_orderings.h`) has partial results
  `to_notgteq/to_notleeq` used **only** for LPO caching.
* **Vampire** `Kernel/KBO.cpp` `KBO::State` — same `_weightDiff`/`_varDiffs`/`_posNum`/`_negNum`,
  `applyVariableCondition` downgrades to `INCOMPARABLE`. Notably has `compareUnidirectional`
  (`KBO.cpp:805`) — a fast "is-greater / not-greater" check that works on `AppliedTerm`s (substitution
  applied lazily) — used by demodulation. `Result` enum has no `GREATER_EQ`; "≥" is a query.
* **Prover9** `termorder.c` — `kbo`, plus `lrpo` (one recursion parameterized by per-symbol LR/multiset
  status = LPO/RPO), and a BOOL `term_greater` from which the 4-valued `term_order` is derived by
  calling both directions.

**Precedence & weights**: E has a rich menu of precedence-generation schemes (`che_to_precgen.c`:
by arity, inverse-frequency, conjecture-frequency, …) and weight schemes (`che_to_weightgen.c`); the
default weight scheme makes the first maximal symbol weight-0. Ours currently uses interning-order
precedence and uniform weight (`SymbolInfo.precedence=id`, `weight=1`) — adequate but a Phase-5 tuning
lever.

### 2.3 Literal & clause ordering

* **Vampire** `PrecedenceOrdering::compare(Literal,Literal)` (`Ordering.cpp:259`): identical→EQUAL;
  exact complement→negative is LESS; **predicate level** (equality pinned to the lowest level `EQ=0`,
  so any non-equality outranks equality unless same level); equalities via `compareEqualities`
  (`Ordering_Equality.cpp`) = multiset extension of the term order over `{s1,s2}` vs `{t1,t2}`,
  hand-unrolled with fast paths; else `comparePredicates`. `getEqualityArgumentOrder` (`Ordering.cpp:229`)
  **caches** the orientation on the shared literal.
* **E** lifts equations to multisets `{{l},{r}}` (positive) / `{{l,r}}` (negative), compares via
  `TOCompare`; `EqnOrient` (`ccl_eqn.c:2384`) orients an equation (swaps sides so the larger is left,
  sets `EPIsOriented`, or leaves unorientable) and `EqnIsMaximal`/`EqnIsOriented` drive selection.

**This is precisely what we lack**: our `compareLiterals` (`Core.scala:394`) is the syntactic sort key
for canonicalization, not this semantic multiset order.

### 2.4 Demodulation (forward + backward)

**Forward** (rewrite the newcomer by stored oriented unit equations):

* **Vampire** `ForwardDemodulation.cpp:82` queries `DemodulationLHSIndex` for **generalizations**
  (`l` with `lσ=trm`); usability decided at index-insertion (`EqHelper::getDemodulationLHSIterator`,
  handles oriented vs incomparable-with-variable-subset); **post-substitution re-check**
  `compareUnidirectional(trm, rhsApplied)==GREATER`; and — crucially — a **redundancy/encompassment
  gate** (`DemodulationHelper::isPremiseRedundant`) deciding whether the rewrite is a *simplification*
  (deletes its premise) vs a mere generating step.
* **Prover9** `flatdemod.c` (`fdemod`): bottom-up leftmost-innermost rewriting over **flatterms** via a
  discrimination tree, oriented (`oriented_eq`) or per-instance `flat_greater`-guarded; **step and
  size-increase limits** (`demod_step_limit`, `demod_increase_limit`) bound runaway rewriting; records
  `(demod_id, sequence, direction)` triples for reconstruction. `demodulator_type` (`demod.c:40`)
  classifies an equation ORIENTED / LEX_DEP_{LR,RL,BOTH} / NOT with variable-subset checks.

**Backward** (use the new clause to rewrite stored clauses): Vampire `BackwardDemodulation.cpp:164`
queries `DemodulationSubtermIndex` for **instances**; Prover9 `backdemod.c` indexes *every* non-variable
subterm of every kept clause and `INSTANCE`-retrieves against a new demodulator's LHS. Both re-check
orientation per instance and remove the original before inserting the replacement.

The **forward⇄generalizations / backward⇄instances duality** is universal and worth internalizing:
forward rewrites the newcomer using stored rules (query = generalizations of the newcomer's subterms);
backward uses the newcomer as a rule against stored targets (query = instances).

### 2.5 Subsumption & other simplification

Already implemented in our `Subsumption.scala` (Phase 2). For reference: Vampire uses **SAT-based**
subsumption + subsumption-resolution (`SATSubsumption/`), plus **ForwardSubsumptionDemodulation**
(non-unit conditional rewriting). Prover9 uses a **feature-vector di_tree** (`di_tree.c`) as a cheap
monotone filter before the real backtracking subsumption test. Tautology/duplicate deletion are cheap
ISEs. These are refinements, not Phase-4 blockers.

### 2.6 Saturation loop

* **Vampire** `SaturationAlgorithm.cpp`: clause state machine (`UNPROCESSED→PASSIVE→SELECTED→ACTIVE`),
  engine categories **ISE** (immediate, cheap, every clause), **FSE** (forward-simplify the newcomer),
  **BSE** (backward-simplify stored clauses with the newcomer), **generating** (only at `activate`).
  **DISCOUNT** (`Discount.cpp`) simplifies only against the **active** set; **Otter** against active
  **and** passive; **LRS** estimates reachable clauses and sets age/weight limits (incomplete but fast).
* **E** `cco_proofproc.c` (`ProcessClause`): select given → forward-contract → insert into processed →
  `generate_new_clauses` → `insert_new_clauses` (simplify, check-empty).

**We already run a DISCOUNT loop** (`Discount.scala`). Phase 4 adds the equality generating inferences
and demodulation into that existing structure — no architectural change.

### 2.7 Indexing & AVATAR (Phase 5+ / out of scope, noted for completeness)

* **Indexing** (Phase 5): Vampire substitution trees + **code trees** (compiled matching automata) for
  the hot forward-demod/subsumption paths, all over **perfect term sharing**; E PDT/feature-vector/
  fingerprint indices; Prover9 FPA path index + discrimination trees + the `mindex` dispatcher (which
  enforces "discrimination ⇒ generalization queries only"). None affect the calculus.
* **AVATAR** (Vampire, optional): SAT-controlled splitting of variable-disjoint clause components;
  equality needs no special handling beyond an optional ground congruence-closure DP. Not for Phase 4.
* **Portfolio/CASC**: strategy scheduling (SA × selection × age:weight × KBO/LPO × AVATAR). Phase 5+.

### 2.8 LADR-2017 vs LADR-2026

Confirmed calculus-identical: every equality/ordering/paramod/demod difference is recursion→iteration,
counter widening, or malloc-wrapping. The **only** materially algorithmic 2026 change is an FPA
per-node child **hash table** (7–13% lookup speedup) — a Phase-5-flavored detail. So mining either tree
is equivalent for correctness.

---

## 3. How this maps onto our implementation

### 3.1 What we already have (reuse, don't rebuild)

| Piece | Where | Status for Phase 4 |
|---|---|---|
| Hash-consed term bank, `EqualitySymbol=0` interned as `"="/2` | `Core.scala:53,90` | ✅ equality atoms are `head=0/arity-2` terms; reuse directly |
| Linear KBO on terms (ground + non-ground), `Cmp{Gt,Lt,Eq,Inc}`, admissibility check | `KBO.scala` | ✅ term ordering done; **needs** literal/clause lifting + (optionally) an instantiated-term compare |
| DISCOUNT loop, passive/active, age/weight | `Discount.scala` | ✅ generating inferences + demodulation slot into it |
| Literal selection (prefer negative equalities noted) | `Selectors.scala` | ✅ superposition eligibility reuses it |
| Resolution/factoring/canonicalize + `Trail`/`Applier` unify+instantiate | `Inference.scala` | ✅ the *pattern* to copy for equality rules |
| Forward/backward subsumption, unit deletion, subsumption resolution, condensation | `Subsumption.scala` | ✅ Phase-2 redundancy already present |
| Kernel reconstruction with `LeftSubstEq`/`RightSubstEq`/`LeftRefl`/`RightRefl` available | `Reconstruction.scala`, kernel `SequentCalculus` | ✅ rules exist, unused; add equality-inference cases |
| Justification DAG (`Input/Resolution/Factoring/Canonicalization`) | `Core.scala:412` | ✅ extend with equality-rule cases |

### 3.2 The four concrete gaps

1. **Literal & clause ordering** (new). `KBO.compare` handles *terms*; we need:
   * `compareEquationLiterals` — multiset extension over `{s,t}`/`{s,s,t,t}`, using `KBO.compare` on
     sides, returning `Cmp`, with equality pinned below non-equality atoms (or a predicate-level scheme);
   * a **maximal-literal test** and a helper to orient an equality (which side is `Gt`), ideally
     **cached on the literal/clause** like Vampire's `getEqualityArgumentOrder`.
   Note `compareLiterals` (`Core.scala:394`) stays as the *syntactic* canonicalization key — the new
   ordering is a distinct, semantic one.

2. **Instantiated-term ordering for post-σ checks.** Superposition/factoring/demodulation must test
   `lσ⋠rσ` etc. *after* unification. Since we already **materialize** the conclusion via `Trail.Applier`,
   the simplest correct approach is to compare the **already-instantiated** concrete terms with the
   existing `KBO.compare` (no deref machinery needed). Vampire's lazy `compareUnidirectional` on
   `AppliedTerm`s is a Phase-5 optimization we can skip initially.

3. **Equality inferences + demodulation** (new in `Inference.scala`, or a new `Superposition.scala`):
   positive/negative superposition (both directions), equality resolution, equality factoring, forward
   & backward demodulation; plus `canonicalize` dropping `s=s` tautologies and routing `s≠s` to equality
   resolution. All following the existing `resolve`/`factor` idiom (save trail → unify → build via
   `Applier` → record `Justification` → restore trail).

4. **Reconstruction** (new cases in `Reconstruction.scala` + `Justification`): rebuild each equality
   inference as a small kernel subproof. Superposition of `l≈r` into `s[u]` is a `RightSubstEq`/
   `LeftSubstEq` rewrite (replace `u` by `r` under the recomputed unifier); equality resolution uses
   `RightRefl`/`LeftRefl` on `sσ = sσ`; demodulation is a substitution of equals. The unifier is
   **recomputed from stored positions** (as we already do for resolution, and as LADR's `para_pos`
   does), so `Justification` stores only rule + parents + literal/subterm positions.

### 3.3 Scoping decisions (recommended)

* **KBO, not LPO.** We already have a correct linear KBO; LPO is a Phase-5 portfolio addition.
* **No term indexing** — linear scan of the active set (Phase 5), matching current resolution.
* **Selection: keep the current selector**, which already prefers negative equalities; empty selection
  is a valid fallback and keeps completeness simple.
* **Demodulation**: implement it (it's part of the Phase-4 definition in `PLAN.md`) with the
  orientation re-check and the `isPremiseRedundant`/encompassment gate, but **without** step/size limits
  initially (a Prover9-style safety valve is a later refinement).
* **Encoding of non-equality atoms**: our clauses already carry ordinary predicate literals; we do **not**
  need the `P(t̄)≈⊤` encoding — superposition happens on equality literals, resolution continues to
  handle predicate literals, and the literal ordering just ranks equality below non-equality (Vampire's
  `EQ=0` level). This keeps Phase 1–3 behavior intact.

---

## 4. Sources

* Superposition theory: Bachmair & Ganzinger, *Rewrite-Based Equational Theorem Proving with Selection
  and Simplification*, JLC 1994; Nieuwenhuis & Rubio, Handbook of Automated Reasoning Ch. 7; Waldmann/
  Ganzinger/Weidenbach LMU/MPI lecture notes; *A Comprehensive Framework for Saturation Theorem Proving*
  (JAR 2022); arXiv 2405.03367 (DER completeness pitfalls).
* Vampire: `othersolvers/vampire/` — `Inferences/Superposition.cpp`, `EqualityResolution.cpp`,
  `EqualityFactoring.cpp`, `Kernel/EqHelper.cpp`, `Kernel/KBO.cpp`, `Kernel/Ordering*.cpp`,
  `Inferences/ForwardDemodulation.cpp`, `BackwardDemodulation.cpp`, `DemodulationHelper.cpp`,
  `Saturation/{SaturationAlgorithm,Discount,Otter,LRS}.cpp`, `Indexing/*`, `Saturation/Splitter.cpp`.
* E: `othersolvers/eprover/` — `ORDERINGS/cto_kbolin.c`, `cto_lpo.c`, `cto_ocb.c`, `cto_orderings.c`;
  `HEURISTICS/che_to_precgen.c`, `che_to_weightgen.c`; `CLAUSES/ccl_eqn.c`; `CONTROL/cco_proofproc.c`.
* Prover9/LADR: `othersolvers/prover9/ladr/` — `paramod.c`, `parautil.c`, `demod.c`, `flatdemod.c`,
  `backdemod.c`, `termorder.c`, `symbols.c`, `fpa.c`, `di_tree.c`, `mindex.c`; vs `othersolvers/ladr-2026/`.
* Our code: `Core.scala`, `KBO.scala`, `Inference.scala`, `Discount.scala`, `Subsumption.scala`,
  `Selectors.scala`, `Reconstruction.scala`; kernel `SequentCalculus` (`LeftSubstEq`/`RightSubstEq`/
  `LeftRefl`/`RightRefl`).
</content>
</invoke>
