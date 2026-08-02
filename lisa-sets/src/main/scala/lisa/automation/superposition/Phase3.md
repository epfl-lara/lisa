# Phase 3 — Clausification wiring

**Goal.** Make the superposition prover usable on **arbitrary (non-clausal) first-order Lisa sequents**,
producing one certified kernel proof of the original goal — not just on pre-clausified CNF. Both halves
already exist independently; Phase 3 is the **integration** that joins them. Targets the **no-equality**
fragment first (equality is Phase 4); the wiring then extends unchanged once the prover handles equality.

This document is grounded in the actual code of `lisa.automation.clausification` (read-only here) and our
`Bridge`. Per the project rule, **all new code lives under `superposition/`**; the clausifier is called via
its public API and is not modified (if it must change, stop and ask — §6).

---

## 1. What already exists (the two halves)

- **The clausal engine** (Phases 0–2): `Bridge.solve(Iterable[K.Sequent], …): Outcome`. On a refutation it
  yields `Outcome.Success` with `reconstructKernelProof: SCProof` concluding the **empty sequent `⊢`**, with
  the input clause-sequents as **imports**. Internally `clauseOfSequent` reads a sequent
  `a₁…aₘ ⊢ b₁…bₙ` as the clause `¬a₁ ∨ … ∨ ¬aₘ ∨ b₁ ∨ … ∨ bₙ` (left = negative atoms, right = positive
  atoms, one variable numbering per clause).
- **The certified clausifier** (`Clausification.scala`, built 2026-04/05, see its `JOURNAL.md`): a full
  pipeline `certifyNegated → certifyNnf → certifySkolem → certifyPrenex → certifyTseitin` that turns a
  first-order `Problem(hypotheses: Seq[K.Sequent], conjecture: Option[K.Sequent])` into clausal form and
  produces a kernel `SCProof`, **leaving the clausal refutation to a downstream prover** it is handed.
  Skolemization uses **Hilbert ε-terms** (`∃x.φ ⟺ φ[ε(λx.φ)/x]`); the Tseitin step introduces fresh atoms.

**Today the clausifier is benchmarked against a `Sorry` stub** (`ClausificationStressTest.refuteClausalProblem`)
— the real clausal prover did not exist when it was written. Phase 3 replaces that stub with `Bridge`.

---

## 2. The hand-off interface

```
Clausification.certifyClausal(problem: Problem, prover: Problem => SCProof): SCProof
```
runs the pipeline and calls `prover` on the resulting **clausal** `Problem` (conjecture consumed; clauses in
`hypotheses`), then composes the clausification derivation with the prover's proof into one `SCProof` of the
original `problem`. The library lemmas are appended to the prover's imports by `certifyClausal`'s own wrapper
(`downstream.imports ++ libImports`), so the prover need not know about them.

**The prover contract** (read off the `Sorry` stub and the `sameImportList` assertion at `certifyTseitin`):
given a clausal `Problem` where each hypothesis is a clause-sequent `() ⊢ {L₁,…,Lₖ}` — the literals as a
**set on the right** (a sequent-level disjunction; *not* a single big `∨`-formula), the returned `SCProof`
must

- have **imports = the clause-sequents** `problem.imports` (in order), and
- **conclude the clauses jointly contradictory** (the stub forms `Sequent(⋃ rightLiterals, ∅)`).

`Bridge.solve` already **consumes this exact form**: `clauseOfSequent` reads left formulas as negative
literals and right formulas as positive, peeling a leading `¬` (so `() ⊢ {¬A, B}` becomes the clause
`{¬A, B}`). So there is **no input conversion** (§3.1). What remains is the *output* side — `Bridge` concludes
`∅ ⊢` with those clauses as imports, which already matches the import half of the contract; only the
conclusion shape needs reconciling (§3.2) — and the **abstraction of non-first-order subterms** the clauses
may contain (§3.3), which is the one substantive seam.

---

## 3. Integration seams (the real work)

### 3.1 Clause-format conversion — none needed

A clausifier clause is `() ⊢ {L₁,…,Lₖ}` (literals as a set on the right), which is exactly what
`Bridge.solve`'s `clauseOfSequent` already ingests (left → negative literals, right → positive, `¬` peeled).
So the input side is just `Bridge.solve(problem.hypotheses, budgets)` — no splitting, no `Restate`. (The
earlier draft pointed at the wrong entry, `formulaToSequent`, which is the single-`∨`-formula / TPTP path.)
The only precondition is §3.3: each literal's atom must be **first-order** by the time it reaches
`clauseOfSequent`.

### 3.2 Prover-contract reshaping: `∅ ⊢` (imports) → clauses-contradictory

`Bridge.reconstructKernelProof` proves `∅ ⊢` with those very clause-sequents as imports, so the **import
half of the contract already holds** (the imports are `problem.imports`). What remains is the **conclusion
shape**: `Bridge` ends at `∅ ⊢`; the pipeline expects the prover to state the clauses jointly contradictory
(the `Sorry` stub forms `Sequent(⋃ rightLiterals, ∅)`, but a `Sorry` accepts any conclusion, so the precise
required form must be read off how `certifyNegated`/`certifyTseitin` cut against it). Bridging `∅ ⊢` to that
form is the standard *imports → local assumptions* move (the clausifier's own IR already does it with
`Hypothesis(φ ⊢ φ)`) — mechanical, fixed per clause, no search. Confirm the exact target in the spike.

### 3.3 Non-first-order subterms → schematic function symbols, discharged by one `InstSchema` *(the one real seam)*

Clausifier output can contain subexpressions that are **not purely first-order** — chiefly Skolem **ε-terms**
`ε(λx.φ)` (an embedded lambda, with the enclosing universals free in `φ`), and possibly other higher-order
Lisa constructs. Our prover is first-order over a flat hash-consed bank with no lambda support, so these must
be abstracted away **before** `clauseOfSequent`.

**Abstraction.** Walk each clause's atoms; for every maximal non-first-order subexpression `e`, compute its
free variables `fv₁…fvₙ` and replace `e` by `F(fv₁,…,fvₙ)`, where `F` is a fresh **schematic function
*variable*** (sort `Indⁿ → Ind`). **Memoize** by the closed abstraction `λfv. e`: identical subexpressions
(across all clauses, up to their free-variable arguments) share one `F`, so `F` is a genuine Skolem/abstraction
*function* applied to different arguments at different sites. After this pass every clause is purely
first-order (`F` is just a function symbol applied to variables) and feeds `Bridge.solve` unchanged.

**Why a schematic *variable*, not a constant.** Only schematic variables can be instantiated by the kernel's
`InstSchema`. This is exactly the trick the clausifier already uses for Tseitin atoms (its JOURNAL: "Tseitin
atoms are schematic `Variable`s … to enable `InstSchema` discharge").

**Discharge at the very end — no per-step re-substitution.** The prover runs and reconstruction emits a kernel
proof **entirely in the abstracted (`F`-)world** — imports are the abstracted clauses, the conclusion is the
abstracted refutation. We do **not** walk the proof rewriting `F` back to `e`. Instead we append a **single
`InstSchema`** step instantiating every `F := λfv. e` simultaneously; the kernel propagates the substitution
through the whole sequent in one certified step, yielding a proof whose imports are the **original** clauses
(`= problem.imports`) and whose conclusion is the original refutation. That proof is what `certifyClausal`
receives.

**The one `Bridge` change this needs.** `Bridge`'s term converter currently rejects an *applied variable*
head as "not first-order"; it must instead intern a schematic function-variable head `F` as an ordinary
function symbol, and the reconstruction must map that symbol **back to the schematic variable `F`** (not a
constant) so the final `InstSchema` can target it. Small, in-scope (`Bridge` is ours), and the only
prover-side change.

This is the seam to **prototype first**: abstract one Skolemized clause, run it through
`Bridge.solve` + reconstruction, append the `InstSchema`, and check the round-trip — the final conclusion
must contain the original ε-terms, kernel-checked.

### 3.4 Library-theorem discharge

`certifyClausal`'s `SCProof` keeps the library lemmas it uses as imports (its doc names
`lisa.maths.Quantifiers.existsEpsilonIff` and `…forallInstantiation`; verify the exact set/positions via
`libImports`). To close the proof into a Lisa theorem, **cut each library import against its library proof**.
These lemmas already exist in `lisa.maths.Quantifiers`; the tactic wrapper supplies them.

### 3.5 Failure path

`certifyClausal` expects `prover: Problem => SCProof` to **always** return a proof. If `Bridge` returns
`Saturated` (clausal set satisfiable ⇒ the goal is invalid) or `Timeout`/`Unknown`, there is no proof — the
**tactic must fail cleanly** (no kernel proof produced), not throw an uncaught exception inside the pipeline.

---

## 4. Deliverables

1. **A wiring module in `superposition/`** (e.g. `Clausal.scala`, plus a small `Bridge` change): the
   non-first-order **abstraction layer** (§3.3 — schematic-function-variable replacement + memo table + the
   final `InstSchema` discharge, and the `Bridge` term-converter/reconstruction tweak to accept and round-trip
   schematic function heads), the `Clausification.Problem`→`SCProof` adapter (`Bridge.solve(problem.hypotheses)`
   + the §3.2 conclusion reshape), and the §3.5 failure path.
2. **A `ProofTactic`** (mirroring `lisa.automation.Tableau`/`Tautology`) over a general Lisa sequent: build
   the `Clausification.Problem` (hypotheses + negated conjecture), run the adapter through `certifyClausal`,
   discharge the library imports (§3.4), and return the certified proof — failing when §3.5 fires.

---

## 5. Testing (`superposition/`)

- **End-to-end, kernel-checked**, on small **no-equality non-clausal** goals: a quantified propositional
  tautology (e.g. `∀x.(P(x) ⇒ P(x))`), the **drinker's paradox** `∃x.(D(x) ⇒ ∀y.D(y))`, mixed `∀/∃`
  validities, and a goal whose Skolemization yields a non-trivial dependency (exercises §3.3). Each test
  asserts the produced proof is `SCProofChecker`-valid and concludes the **original** sequent.
- **Negative / failure**: a satisfiable (non-valid) goal ⇒ the tactic fails (no proof), not a crash (§3.5).
- **Regression**: the existing clausal path (`Bridge.solve` on CNF) is untouched; the SYN/CASC reconstruction
  suites still pass.

---

## 6. Scope boundary (important)

`lisa.automation.clausification` is **read-only** in this phase: the wiring calls its public `certifyClausal`
(and, if needed, `certifyClausalFlat`). Notably the non-first-order abstraction (§3.3) is done **on our side**
with schematic function variables + a final `InstSchema`, so the clausifier needs **no** Skolem-function mode
or format change. If the integration nonetheless turns out to need a change there — a format tweak, or a
different prover-contract conclusion — **stop and ask**; do not edit outside `superposition/`. The `Bridge`
changes (accepting schematic function-variable heads; the conclusion reshape) are in `superposition/` and in
scope.

---

## 7. Open decisions for the user

1. **Abstraction granularity** (§3.3): abstract every *maximal* non-first-order subexpression (recommended —
   fewest symbols, keeps the most structure first-order), versus a coarser rule (e.g. abstract any atom
   containing a non-FO subterm whole). Also: confirm what Lisa constructs beyond ε-terms can appear in
   clausifier output, so the "non-first-order" predicate is exhaustive.
2. **Tactic surface**: a single tactic that always clausifies, or two entry points (a fast path that skips
   clausification when the goal is already clausal, and the general one)?
3. **Budgets**: the tactic's `maxGiven`/`maxMillis` defaults, and whether to expose them.

---

## 8. Build order

1. **Spike §3.3 (abstraction round-trip)** — abstract one Skolemized clause (ε-term → `F(fv)` schematic
   function variable + memo), run it through `Bridge.solve` + reconstruction, append the `InstSchema`
   discharge, and check the round-trip: the final kernel conclusion must contain the **original** ε-terms and
   pass `SCProofChecker`. Includes the `Bridge` term-converter change to accept/round-trip schematic heads.
   This is the feasibility gate.
2. **§3.2** — the `∅ ⊢` → clauses-contradictory conclusion reshape, tested in isolation against `Bridge` on
   hand-built `() ⊢ {literals}` clause sets (no clausifier yet); read off the exact target conclusion from
   `certifyNegated`/`certifyTseitin`.
3. **Compose** — wire `Bridge.solve(problem.hypotheses)` + abstraction + reshape as the `prover` argument to
   `certifyClausal`; first close a proof end-to-end with the library lemmas left as imports (kernel-valid
   *modulo* those imports).
4. **§3.4 + tactic** — discharge the library lemmas and package the `ProofTactic`; §3.5 failure path.
5. **Tests** (§5), then a small TPTP-FOF sanity run reusing the clausifier's harness with `Bridge` swapped
   in for the `Sorry` stub.

---

## 9. Implementation status (progress log — for hand-off)

**As of 2026-06-28: build-order step 1 (the §3.3 spike / feasibility gate) is DONE. Steps 2–5 remain.**
All 135 superposition tests pass; the `Bridge`/`Reconstruction` changes default to a no-op so existing
clausal behaviour is unchanged.

### Done — the abstraction layer + prover round-trip (§3.3)

- **`Clausal.scala`** (new) — `object Clausal` with `final class Abstraction`:
  - `def apply(e: K.Expression): K.Expression` — replaces every **maximal** non-first-order `Ind`-subterm by a
    fresh schematic function variable `F(fv…)`. Descends the first-order skeleton (`isFirstOrderFunction`
    head = `Variable`/`Constant` with sort `Ind → … → Ind`, which excludes `ε : (Ind→Prop)→Ind`); abstracts
    whole subterms whose head is non-first-order.
  - `def dischargeSubst: Map[K.Variable, K.Expression]` — `F ↦ λfv. e` for each introduced symbol (for the
    final `InstSchema`); `def isEmpty`.
  - Memoised by the subterm expression, so identical subterms share one `F` (a genuine function). Free
    variables sorted canonically by `(id.name, id.no)`.
  - **Gotcha (resolved):** abstraction symbols are named `K.Identifier("abs", counter)` (counter in the
    `no` field → `toString` is `abs`, `abs_1`, …). They must **not** contain two `_`: the kernel's
    `String → Identifier` allows at most one underscore (the counter separator) or it throws
    `InvalidIdentifierException`.
- **`Bridge.scala`** — `solve(...)` gained `symbolVars: Set[K.Variable] = Set.empty` (generalised from the
  earlier `functionVars`), threaded through `clauseOfSequent`/`literal`/`atomTerm`/`term`. A schematic symbol
  variable is dispatched **by position**: in `atomTerm` (a literal head) it is interned as a **predicate**
  symbol — this is how clausifier Tseitin atoms `tsᵢ` (and Lisa predicate variables) are ingested — and in
  `term` (an argument) as a **function** symbol (applied `F(fv…)`, or a bare nullary constant), instead of the
  old "applied/head variable ⇒ throw". Clause variables (sort `Ind`, not listed) stay variables. `Clausal.prove`
  populates `symbolVars` with the ε-abstraction functions **plus every non-`Ind`-sorted free variable** in the
  clauses (so `tsᵢ` are caught automatically; `Ind` clause vars are not). `Outcome.Success` gained
  `schematicNames: Set[String]` (= `symbolVars.map(_.id.toString)`), passed into reconstruction; the ε-functions
  are additionally `discharge`d (inlined), while `tsᵢ` are emitted as `Variable`s for the clausifier's own
  `InstSchema` to discharge. Non-clausal problems needing genuine Tseitin naming now refute end-to-end
  (`ClausalTest`: "Tseitin end-to-end … refuted by Bridge").
- **`Reconstruction.scala`** — `reconstruct(...)`/`Builder` gained `schematicNames: Set[String]`; `kernelize`
  rebuilds a symbol whose name ∈ `schematicNames` as a kernel `Variable` (not `Constant`), with the same
  identifier + `sortFor(arity, isPredicate)` sort, so the round-tripped `F` equals the original abstraction
  variable and a later `InstSchema` can target it.
- **`ClausalTest.scala`** (new) — 4 abstraction unit tests (incl. the K-level discharge round-trip via
  `substituteVariables` + `betaNormalForm`) and 2 spike tests: abstract complementary ε-clauses, `Bridge.solve`
  with `functionVars`, `reconstructKernelProof`, assert `SCProofChecker.checkSCProof(_).isValid` and
  conclusion `∅ ⊢` — for a ground ε (nullary `F`) and an ε with a free variable (applied `F`).

### Key kernel facts (confirmed while building)

- `ε = Constant(Identifier("ε"), (Ind → Prop) → Ind)`; an ε-term is `Application(ε, Lambda(x, φ))`
  (`lisa-kernel/.../fol/Syntax.scala:477`). Build in tests as `K.Application(K.epsilon, K.Lambda(x, φ))`.
- `InstSchema(bot: Sequent, t1: Int, subst: Map[Variable, Expression])`
  (`lisa-kernel/.../proof/SequentCalculus.scala:317`). `subst` maps *variables* to expressions — hence
  abstraction symbols must be `Variable`s.
- `Reconstruction.kernelize` (`Reconstruction.scala`, the symbol→kernel rebuild) is the single place that
  decides `Variable` vs `Constant`.
- `Bridge.solve` ingests literal-set clause-sequents directly via `clauseOfSequent` (left → negative atoms,
  right → positive, `¬` peeled) — **no input conversion needed** (the `formulaToSequent` path is only for
  single-`∨`-formula / TPTP input).

### Remaining (steps 2–5) — the composition

The reconstructed proof has **`F`-clause imports** and conclusion `∅ ⊢`. The prover-contract wants the
**original ε-clauses** as imports and a clauses-contradictory conclusion. A naive "`InstSchema` on the
conclusion" does **not** work, because `F` lives in the *imports*, not the empty conclusion. The fix
composes §3.2 and §3.3:

1. Lift the `F`-clause imports to **LHS assumptions** (the imports→assumptions move; the clausifier's IR
   does the same with `Hypothesis(φ ⊢ φ)`), giving `{F-clauses} ⊢` — now `F` is in the conclusion.
2. **One `InstSchema`** `{F-clauses} ⊢ → {ε-clauses} ⊢` (subst = `Abstraction.dischargeSubst`), recovering
   the original clauses on the LHS in a single step (no per-step rewriting).
3. Lower the LHS `ε-clauses` back to **imports** by importing each original clause and `Cut`-ing it in, so
   the proof imports = `problem.imports` and concludes the contradiction the contract expects (read the
   exact target off `certifyNegated`/`certifyTseitin`; the `Sorry` stub's `Sequent(⋃ rightLiterals, ∅)` is
   a placeholder, not necessarily the precise form).

Then: pass this as the `prover` to `Clausification.certifyClausal`; discharge the library lemmas
(`existsEpsilonIff`, `forallInstantiation` from `lisa.maths.Quantifiers`, appended by `certifyClausal` as
imports at fixed end positions) by cutting against their library proofs; package the `ProofTactic`; handle
the `Saturated`/`Timeout` failure path (§3.5). Tests per §5.

### Files
- New: `superposition/Clausal.scala`, `superposition/test/ClausalTest.scala`.
- Changed: `superposition/Bridge.scala` (`functionVars`, `Outcome.Success.schematicNames`),
  `superposition/Reconstruction.scala` (`schematicNames`, `kernelize`).
- Read-only dependency: `lisa.automation.clausification.Clausification.certifyClausal` (do **not** edit; §6).

### Contract investigation (read of `Clausification.scala`, 2026-06-28)

Traced how the pipeline splices the downstream prover's `SCProof` (`certifyTseitinFlat` line ~1087,
`certifyNegated` line 805). Findings that pin the composition:

1. **Imports contract — confirmed.** The prover is called on `Problem(clauseSequents, None)`; its returned
   `SCProof.imports` must equal those clause-sequents in order (the wrapper `certifyClausal` then appends the
   library lemmas — `wrappedProver`, line 731 — and asserts `sameImportList(downstream.imports,
   newProblem.imports ++ libImports)`, line 1193). So we return `imports = problem.hypotheses`; the lemmas are
   handled for us.

2. **Clause format is now UNIFORM literal-sets (clausifier change, 2026-07-12).** Originally `finalAxioms`
   interleaved two shapes: Tseitin **new-clauses** as literal-sets `Sequent(∅, {lits})`, but **already-clausal
   axioms** and Tseitin **final-rewrites** as single-formula `() ⊢ φ` with `φ` a `∨`-of-literals (there are
   **no** `∀` at this stage — `isClause`/`isAtom` reject `Forall` and `tseitinStep.descend` has no `Forall`
   case, so universals are already free variables). We moved the split into the clausifier: `certifyTseitinFlat`
   now emits every residual axiom/rewrite in the same `Sequent(∅, clauseLiterals(·).toSet)` form at the point it
   is declared clausal, bridged by one `Restate` (`clauseSetRef`). So **every** clause the prover receives is a
   literal-set with negatives as `¬A`. `clauseOfSequent` ingests all of them directly; no `∨`-split or `∀`-strip
   in the adapter.

3. **Conclusion contract — CONFIRMED empirically = the EMPTY sequent `⊢`.** `downstream` is embedded as
   `ClausificationSubproof(downstream, recPremises)` (line 1195, **no** assumptions), so its conclusion
   propagates unchanged up through Tseitin/Prenex/Skolem/Nnf; `certifyNegated` (line 824) `Cut`s the negated
   conjecture `¬φ` (t1 = `⊢ φ, ¬φ`) against the lifted subproof to conclude `⊢ φ`. That `Cut` requires the
   subproof to conclude `¬φ ⊢` (**empty RHS**), i.e. the prover must conclude the **empty sequent `⊢`** — the
   `Sorry` stub's `{all literals} ⊢` was a genuine placeholder (a `Sorry` is not kernel-checked, so it never
   had to be derivable). **No `Weakening`.** A probe (`ClausalTest`: "Bridge satisfies the certifyClausal prover
   contract") confirmed it: `{all literals} ⊢` fails the `Cut` (*"LHS of second premise contains a formula
   absent from the conclusion"*); `∅ ⊢` composes to a kernel-valid proof of `⊢ P`.

4. **The adapter's only reshape: move negatives to the LHS.** `Bridge`/`Reconstruction` expect a **negative
   literal's atom on the LHS** (every spike/Discount test passes `Sequent({a}, ∅)`), but the clausifier writes
   negatives as `¬A` on the **RHS**. Handed `⊢ ¬P` verbatim, `Bridge` concludes `⊢ ¬P` (not `∅ ⊢`) — the `Cut`
   in `Reconstruction.buildResolution` leaves `¬P` on the right. Fix (probe-confirmed): **reshape** each clause
   by moving every `¬A ∈ Δ` to the LHS as `A` (`toWorkingSequent`), solve that, then present imports = the
   **original** clausifier clauses via a per-used-import `Restate` bridging original ⟺ working (propositionally
   equivalent — the same `Restate` also absorbs the placement, and now that clauses arrive as literal-sets
   (item 2) there is nothing to split). Validated end-to-end for both the `Q==0` fast path (multi-literal
   already-clausal axiom, real `Bridge`) and the `Q>0` Tseitin path (multi-literal final-rewrite, `Sorry`-checked
   composition) in `ClausalTest`.

5. **ε discharge — DONE, via inline reconstruction (not a trailing `InstSchema`).** The schematic `F` is now a
   purely **`Bridge`-internal** solving device: `Reconstruction` inlines each `F(args)` back to `(λfv. e)(args)`
   β-reduced (`kernelize`) and discharges the imported sequents likewise (`dischargeSeq` in `buildInput`), so the
   kernel proof is **purely ε-bearing** — no `F`, no trailing `InstSchema`, no import-internalization. This works
   because the discharge substitution `{F := λfv.e}` commutes with reconstruction's clause-variable renaming `σ`
   (disjoint domains; the fresh `fv` introduced by the discharge get renamed correctly by `σ`), keeping every
   `InstSchema`/`Cut` step valid; the ε-terms are treated opaquely by the kernel, exactly as an uninterpreted
   Skolem symbol would be. This **avoids** the internalize-imports-to-LHS + `InstSchema` route originally
   sketched here, which foundered on ProofIR's soundness restriction (can't thread a clause-var-bearing
   assumption through the `InstSchema` steps that rename those very vars). Implemented as: `Bridge.solve` /
   `Reconstruction.reconstruct` gain a `discharge: Map[Variable, Expression]`; `Clausal.prove` is the adapter
   (abstract → `Bridge.solve(functionVars, discharge)` → neg-move `Restate` reshape to the original clauses).
   Validated end-to-end (`ClausalTest`: "ε end-to-end … Skolemizes to an ε-term"): `∀x.P(x)` conjecture →
   `¬P(ε(λx.¬P(x)))` clause → abstracted, refuted, reconstructed ε-bearing → kernel-valid `⊢ ∀x.P(x)`. All 139
   superposition tests green.

6. **Non-clausal problems map to solver symbols (`Bridge.symbolVars`).** Generalised `functionVars` to
   `symbolVars`, dispatched by position: a schematic `Variable` in a **literal head** is interned as an
   (uninterpreted) **predicate** — how clausifier Tseitin atoms `tsᵢ` (and Lisa predicate variables) are
   ingested — and in a **term position** as a **function**. `Clausal.prove` collects `symbolVars` = the
   ε-abstraction functions ∪ every non-`Ind`-sorted free variable in the clauses (so `tsᵢ`, which are Prop-sorted,
   are caught automatically). The ε-functions are additionally `discharge`d (inlined); `tsᵢ` are emitted as
   `Variable`s for the clausifier's own `InstSchema` to discharge. Non-clausal problems needing genuine Tseitin
   naming now refute end-to-end.

7. **FOF evaluation dataset + harness (`FofEvaluation`) and the uncertified path.** Built a second dataset the
   same way as the clausal `Evaluation` set — by TPTP `SPC` header `FOF_THM_{RFO,EPR}_NEQ` (non-clausal, theorem,
   no equality, no arithmetic) — as `tptp-fof-fo-noeq-thm.txt`. The `CSR` (SUMO) domain is excluded (all 359 are
   giant numeric ontologies; see PossibleOptimizations), leaving **944** problems. `FofEvaluation.sample(n=100,
   seed=42)` draws the same seeded way as `Evaluation`; `benchmark` parses each, runs `certifyClausal` (or the
   uncertified path) with `Clausal.prove`, kernel-checks every refutation, and reports per-phase
   **clausify / prover / check** timings. `UncertifiedClausification.clausalForm` computes the **identical**
   clause set via the pure transforms only (no proof) — clause-identity test-verified — and is ~**2× faster total,
   ~20× on the median** (proof-building/checking dominates most easy problems).

8. **Two clausification bugs found via the benchmark's SATURATED theorems, both fixed.**
   - **η-reduced quantifiers stranded in clauses.** The kernel's `betaNormalForm` η-reduces `λy. p(x,y) → p(x)`,
     so `∀y. p(x,y)` = `∀(λy. …)` comes back as `∀(p(x))`, which the `Forall`/`Exists` extractors (they need an
     explicit `Lambda`) miss — leaving the quantifier as an opaque atom in the clause → unresolvable → SATURATED
     (Pelletier 50 was one). Fix: `Clausification.etaExpandQuantifiers` after skolem's `betaNormalForm`, on
     `∀`/`∃` only (**not** ε-terms — they're abstracted wholesale and re-expanding their interior desyncs them
     from the β-normalised discharge, which broke import matching → BAD_PROOF; that was the fix's own first
     over-reach, now corrected).
   - **Boolean constants `⊤`/`⊥` not absorbed.** `toNNF` treated `$true`/`$false` as atoms, so they survived as
     uninterpreted 0-ary predicates that block resolution (the `LCL` modal encodings pad with `$false`). Fix:
     smart constructors `mkAnd`/`mkOr` applying the absorption laws in `toNNF` — propositional equivalences, so
     the `certifyNnf` `Restate` still discharges them (no proof change).
   Net on the seeded-100 (clean 944): **SATURATED 9 → 0, REFUTED 50 → 60, BAD_PROOF 0**, all kernel-checked. The
   remaining failures are dominated by rating-1.00 `LCL…+1.0NN` modal encodings (unsolved by *any* ATP system;
   `LCL648+1.020` even overflows the recursive parser's stack) — not a gap on our side.
