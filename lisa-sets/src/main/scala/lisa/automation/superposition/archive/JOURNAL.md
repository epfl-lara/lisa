# Clausification Implementation & Optimization Journal

> **Status: historical.** A record of the 2026-04-30/05-01 sessions, kept for the design rationale (the
> `ClausificationSubproof` IR, library theorems as imports, the ε-Skolemization scheme). It is **not** a
> description of the current code. Since it was written:
>
> - `certifyTseitin` (full Tseitin transformation) was replaced by `CertifiedFastClausifier.certifyFastNaming`
>   — threshold-gated *selective* definitional naming, mirroring the uncertified `FastClausify`. The atoms are
>   `nm…` (`GeneratedNames.namingAtom`), not `tsᵢ`.
> - `ScreenPhase` was added at the top of the pipeline (it subsumes the former `RenamePhase`), and
>   `DistributePhase` at the bottom.
> - The two files named below, `ClausificationTPTPBench.scala` and `ClausificationStressTest.scala`, no longer
>   exist; the benchmark harnesses now live in `superposition/` (`FofHarness` and friends).
>
> The current pipeline is `certifyScreen → certifyNegated → certifyFastNaming → certifyNnf → certifySkolem →
> certifyPrenex → certifyDistribute → prover`; see `CertifiedFastClausifier.scala`.

**Session date:** 2026-04-30 → 2026-05-01  
**Files (as of writing):** `Clausification.scala`, `ProofIR.scala`, `ClausificationTPTPBench.scala`, `ClausificationStressTest.scala`  
**Benchmark runs:** v1 (25 OK) → v2 (35 OK) → v3 (38 OK) → v4 (37 OK) → v5 (39 OK, 0 stuck, 2× faster, 5× less memory)

---

## Phase 0 — Problem Definition and Pipeline Skeleton

The goal is to produce a fully-certified `SCProof` from a first-order problem (set of hypotheses + optional conjecture) in clausal normal form, suitable for feeding to a clausal refutation prover. The pipeline mirrors the SC-TPTP `Clausification.scala` — same function names (`certifyNegated`, `certifySkolem`, `certifyPrenex`, `certifyTseitin`), same recursive structure. Every proof step is constructed using explicit kernel rules (`Hypothesis`, `Cut`, `LeftForall`, `RightSubstIff`, etc.); no high-level tactics. The conjecture is negated and added as an axiom by `certifyNegated`; it does not appear as a separate import. Proof composition uses `SCSubproof` nesting.

---

## Phase 1 — `ClausificationSubproof` IR (ProofIR.scala)

Standard `SCProof` imports must be backed by a closed derivation supplied by the caller. The Tseitin transformation needs to thread a *local assumption* `∀fv. (tsi(fv) ⟺ subst)` — a definitional iff for each fresh Tseitin atom — that is not a global theorem but is later discharged by `InstSchema`. This is inexpressible with plain imports and motivates a two-level IR. The lowering function `lowerClausificationProof` translates it to a kernel `SCProof` by emitting one `Hypothesis(φ ⊢ φ)` step per local assumption (optionally followed by a `Weakening` to add inherited LHS assumptions), then walking the proof steps with shallow handling of nested `SCSubproof`s.

**[MAJOR] The `ClausificationSubproof` / local-assumption IR.**  
A `ClausificationProofStep` sealed trait with two cases:
- `KernelStep(step: SCProofStep)` — a plain kernel step.
- `ClausificationSubproof(proof, premises, assumptions)` — a subproof that declares some imports as *local LHS assumptions*, materialized as `Hypothesis(φ ⊢ φ)` steps during lowering.

The quantified Tseitin iff `∀fv. (tsi ⟺ subst)` lives on the LHS of every step in the inner proof (it is assumed there), but discharging it via `Cut` happens outside via `InstSchema`. This avoids threading it as a proper imported hypothesis, which would require the parent proof to supply a closed derivation of it — a circular requirement since the iff is only ever true after instantiation.

---

## Phase 2 — Library Theorems as Imports

Both Skolemization and Prenex normalization require five library theorems: `existsEpsilonIffStatement` (`() ⊢ ∃(λx.P(x)) ⟺ P(ε(λx.P(x)))`), and four prenex-lifting equivalences (`forallAndLeft/Right`, `forallOrLeft/Right`). These are collected in `val libImports: IndexedSeq[Sequent]` and appended to every clausification proof at fixed positions `n..n+4` (after the `n` user hypotheses). The helper `libRef(nonLibSize, libIdx)` computes the correct negative reference index for any subproof.

**[MAJOR] Theorems are imported as statements, not proven inline.**  
Rather than reproving a library theorem at each use site (duplicating derivations across every clausification proof), the clausification proof takes each theorem's *statement* as an import. The actual proof of the theorem is supplied externally when the clausification proof is eventually wrapped as a tactic, by cutting against the library. This keeps the clausification proof library-independent and bounds its size: without this, every subproof for an n-axiom problem would contain O(n) copies of the epsilon or prenex derivations.

---

## Phase 3 — Certifying Skolemization (`certifySkolem`)

`certifySkolem` processes existentials top-down (outermost first), so each epsilon term for an inner `∃` correctly contains the epsilon terms of outer ones as free variables — producing the standard Skolem dependency structure. After each substitution the formula is beta-normalized (`skoFormula.betaNormalForm`) so subsequent calls can syntactically locate inner `Forall/Exists/And/Or` nodes through the `(λu.body)(b)` redexes left by context application.

**[MAJOR] Single-descent proof via `RightSubstIff` — O(1) steps per Skolem step.**  
A naive certifier would deconstruct the formula tree down to the `∃` node and reconstruct it, costing O(|φ|) steps per step and O(|φ|²) total. Instead, each `skolemizeOne` call uses three kernel steps regardless of nesting depth:
1. Instantiate `existsEpsilonIffStatement` at `P := λx. φ_inner` to get `() ⊢ (∃x.φ_inner ⟺ φ_inner[ε/x])`.
2. Wrap with `RightForall` × k to lift across k enclosing universals: `() ⊢ ∀u₁…uₖ. (∃x.φ_inner ⟺ φ_inner[ε/x])`.
3. Apply `RightSubstIff` with context `λp. φ[∃-node := p]` to rewrite the full formula in one step.

**[MAJOR] Proof size O(n²) in Skolem steps — and this is optimal.**  
Each epsilon term at step k contains all k−1 prior epsilon terms as subexpressions. Proof steps referencing it inherit this size, giving O(1 + 2 + … + n) = O(n²) total. Since the *output formula* has the same O(n²) size for the same reason, no smaller proof can exist.

---

## Phase 4 — Certifying Prenex Normalization (`certifyPrenex`)

After Skolemization, universal quantifiers may appear anywhere in the formula tree. Two certified strategies are implemented and selected by a lightweight heuristic.

### Strategy A: Deconstruction (`provePrenexDeconstruct`)

**[MAJOR] O(|φ|) proof by tree mirroring.**  
Mirrors the formula's connective structure with kernel rules: `LeftForall` at each `∀x.body` node (instantiating with a fresh witness `V_i`), `RightAnd`/`LeftOr` at connectives, `Hypothesis` at leaves — then `Cut` against the imported formula. Proof size is O(|φ|). The `hasForall` guard short-circuits entire quantifier-free subtrees with a single `Hypothesis`, making deconstruction practical even on large formulas where quantifiers are sparse.

### Strategy B: Rewriting (`provePrenexRewrite`)

**[MAJOR] O(nq × depth) proof by quantifier lifting.**  
For each `∀` located in the formula, lifts it to the root one connective layer at a time using the prenex-lifting library theorems via `InstSchema` + `RightSubstIff` + `Cut`, then strips it with `LeftForall`. Proof size is O(nq × depth). The key advantage over deconstruction: only the path from the `∀` to the root is visited — the (potentially large) quantifier-free bulk of the formula is never touched.

**[MAJOR] Heuristic dispatch.**  
`preferRewriteStrategy(φ)` selects rewriting when `|φ| > 4 · nq²`. Below this threshold the O(|φ|) deconstruct cost is cheaper; above it the O(nq × depth) rewrite cost wins. The factor 4 was derived from the crossover point of the two bounds assuming balanced formula trees.

---

## Phase 5 — Certifying Tseitin (`certifyTseitin`)

The Tseitin transformation abstracts the deepest non-clausal subformula `g op h` with a fresh atom `tsi(fv...)`, adding a definitional iff `∀fv. (tsi(fv) ⟺ g op h)` and 1–2 clausal axioms per step. Within a single axiom, K_i Tseitin steps are chained flat — each takes the previous rewritten axiom as input.

**[MAJOR] Tseitin atoms are schematic `Variable`s (not `Constant`s) to enable `InstSchema` discharge.**  
`tsi` has sort `s₁ → … → sₙ → Prop` and is a schematic `Variable` so that `InstSchema(tsi := λfv. g op h)` can substitute it. This turns the definitional iff `∀fv. (tsi(fv) ⟺ g op h)` into the reflexive tautology `∀fv. (g op h ⟺ g op h)`, provable as a small closed subproof. A `Cut` then discharges it from the LHS. Using a `Constant` would block `InstSchema` and leave the iff permanently in the hypothesis set.

**[MAJOR] Flat certifier — O(n) proof size via single-level `ClausificationSubproof`.**  
The initial design used one `ClausificationSubproof` per axiom, each with its own K_i local assumptions. Lowering added a `Weakening` per external import per assumption per level, giving O(n²) total weakenings for n axioms. The flat redesign (`certifyTseitinFlat`) gathers all Q = ΣK_i assumptions into one outer `ClausificationSubproof` — a single nesting level — reducing the weakening count to O(n).

**[MAJOR] O(Q²) → O(Q) discharge loop.**  
The initial loop called `substSequent` on the full LHS (Q formulas) at each of Q iterations — O(Q²) substitution work. Since each `tsi_j` is a fresh unique variable, only `quantifieds(j)` in the LHS contains it; all other formulas are unaffected. The fix operates directly: `mutableLhs -= quantifieds(j); mutableLhs += quantReflFormula`. Total work: O(Q).

---

## Phase 6 — `certifyAxiomwise` Factoring

Both `certifySkolem` and `certifyPrenex` iterate over axioms one at a time, producing a per-axiom "prelude" proof and recursing on the rest — factored into `certifyAxiomwise(problem, prover, transform)`. The original recursive nesting gave O(n) `ClausificationSubproof` levels and O(n²) lowering cost.

**[MAJOR] Flat `certifyAxiomwise` — O(n × K_max) proof size.**  
All prelude steps for all n axioms are inlined into a single flat `ClausificationProof`. A `rebase` function rewrites each step's premise references into the flat index space. A single `ClausificationSubproof` wraps the downstream prover call. Total proof size drops from O(n²) to O(n × K_max) where K_max is the maximum number of prelude steps per axiom.

---

## Phase 7 — TPTP / CASC Benchmark Harness

The harness runs each problem in a dedicated thread. Problems with formula size > `--max-size` (default 5000) are skipped to bound proof blowup — this accounts for 53/100 skipped in the CASC-J12 run. The CSR domain is excluded because the scala-tptp-parser rejects large integer literals in CSR files (source of the 9 ParseFail in v1). Results are output as CSV (`problem, domain, tag, status, numHyps, hasConj, formulaSize, proofSize, timeMs, peakMemMb, error`). The first run sampled from TPTP-v9.2.1 directly; subsequent runs target CASC-J12's FNE and FEQ divisions (500 FOF problems, 100 sampled with fixed seed).

**[MAJOR] Per-thread allocation measurement via `ThreadMXBean`.**  
The initial approach (heap delta from `Runtime.getRuntime` + `System.gc()`) was unreliable: GC activity and other threads introduced noise that made per-problem measurements meaningless. Replaced with `com.sun.management.ThreadMXBean.getThreadAllocatedBytes(threadId)` — a monotonically-increasing per-thread allocation counter, recorded inside the worker thread's own `finally` block. This gives accurate allocation *per problem*, immune to GC timing and unrelated threads.

**[MINOR] Per-problem timeout + cooperative interruption.**  
A watchdog thread interrupts the worker at the per-problem deadline; `checkInterrupted()` (checking `Thread.interrupted()` + heap usage > 90% of max heap) is called at key loop boundaries throughout the pipeline. The heap-pressure check prevents OOM crashes when a runaway problem escapes the wall-clock timeout. A "hard timeout" (`--hard-timeout-mult × timeout`) distinguishes slow-but-finishing workers from leaked threads (Stuck).

### First benchmark results

- **v1** (initial, `--max-size 2000`, TPTP sample): 25 OK / 64 Skipped / 9 ParseFail / 1 Timeout / 1 Stuck
- **v2** (+CSR exclusion, `--max-size 5000`, CASC-J12): 35 OK / 53 Skipped / 6 Timeout / 6 Stuck

The 50% OK target (50/100 problems) was set as the milestone for subsequent optimization work.

---

## Phase 8 — Memory and Performance Optimizations (v3 → v5)

The v2 results (35 OK / 6 Timeout / 6 Stuck) exposed three bottlenecks: (1) `substituteVariables` always walking the full term tree even when the substitution map is empty; (2) `lowerKernelProofWithAssumptions` recursing into every inner `SCSubproof` step to add Q weakenings — O(Q² × inner_step_size) total; (3) `provePrenexRewrite`'s `while` loop having no `checkInterrupted()` call, making those workers uninterruptible. A bug in `rewriteStepBot` also caused the step array to double: `withNewSteps(sp.steps :+ step)` appended to the *existing* steps (since `withNewSteps` does `steps ++ newSteps`), fixed to `sp.withNewSteps(IndexedSeq(Weakening(newBot, sp.steps.size - 1)))`. Micro-optimizations: `ClausificationSubproof.bot` memoized as `lazy val` (was recomputed O(Q) times per discharge loop iteration); import map replaced with a direct-indexed `Array[Int]`; `ArrayBuffer`s in hot helpers pre-sized to avoid reallocation; `proveQuantifiedReflIff` switched from `ArrayBuffer` + `toIndexedSeq` to a pre-allocated `Array[SCProofStep](3 + n)`.

v3 applied `substituteVariablesOpti` and shallow lowering: **38 OK / 5 Timeout / 4 Stuck**.  
v4 added per-thread memory measurement: **37 OK / 5 Timeout / 5 Stuck** (minor regression from measurement overhead).  
v5 applied remaining fixes: **39 OK / 8 Timeout / 0 Stuck**.

**[MAJOR] `substituteVariablesOpti` — structural short-circuits in substitution traversal.**  
Three guards eliminate redundant work: (1) *`m.isEmpty` guard*: returns the original term immediately when the map is empty — fires on every node below the last substituted variable, which in the Tseitin discharge loop is most of the formula after `tsi_j` is consumed; (2) *smart constructors*: after recursing into `Application(f, a)` or `Lambda(v, b)`, sub-results are compared by *reference equality* (`eq`). If unchanged, the original node is returned — no new allocation. On quantifier-sparse formulas the vast majority of nodes are unaffected, so this eliminates nearly all allocation from substitution; (3) *lambda stripping*: when `Lambda(v, _)` removes the last key from `m`, recursion stops — the body cannot contain any substituted variable. Additionally, `fvOfValues` (free variables of substitution values, needed for capture detection) is computed once at the call site and passed down via a private `substituteVariablesOptiRec`, rather than recomputed at every `Lambda` during descent.

**[MAJOR] Shallow lowering of `SCSubproof` steps — O(Q² × inner) → O(Q).**  
`lowerKernelProofWithAssumptions` must add Q inherited assumptions to every step. For `SCSubproof(sp, _)` steps the naive approach recursed into all of `sp`'s inner steps, giving O(Q × |sp|) work per subproof and O(Q² × inner_step_size) total across the 2Q inner subproofs in `certifyTseitinFlat`. The shallow strategy appends a single `Weakening(targetBot, sp.steps.size - 1)` to `sp` instead. The resulting proof is not kernel-valid (inner bots lack the added assumptions) but the clausification pipeline never invokes the kernel checker.

**[MINOR] `toNNF` Iff expansion — 4 passes instead of 6.**  
The original `g ⟺ h` case routed through intermediate `Implies` nodes, traversing each of `g` and `h` twice. Replaced by a direct four-pass expansion: compute `gPos, gNeg, hPos, hNeg` independently and assemble directly.

**[MINOR] Mutable set in discharge loop.**  
Immutable `Set` operations in the Q-iteration loop allocate path-copying nodes at O(log Q) each. Replaced with `scala.collection.mutable.HashSet` mutated in-place. Two `toSet` snapshots per iteration remain necessary for `Sequent` construction but are O(Q) each.

---

## Benchmark Results Summary

| Version | OK  | Timeout | Stuck | Skipped | Wall time (total) | Alloc median | Alloc max |
|---------|-----|---------|-------|---------|-------------------|--------------|-----------|
| v1      | 25  | 1       | 1     | 64+9†   | —                 | —            | —         |
| v2      | 35  | 6       | 6     | 53      | —                 | —            | —         |
| v3      | 38  | 5       | 4     | 53      | —                 | —            | —         |
| v4      | 37  | 5       | 5     | 53      | 312 s             | 73.8 MB      | 2361 MB   |
| v5      | **39** | 8    | **0** | 53      | **148 s**         | **14.1 MB**  | **519 MB** |

† v1: 9 ParseFail on CSR-domain problems (large integer literals unsupported by the TPTP parser).

v5 vs v4: **5.2× lower median allocation, 4.5× lower peak allocation, 2.1× faster total wall time, 0 stuck workers.** The 3 additional timeouts in v5 are formerly-Stuck problems that now run cleanly to the wall-clock limit instead of leaking threads.

---

## Remaining Known Bottlenecks

1. **53 skipped (formula size > 5000)** — dominant gap. Raising `--max-size` exposes them but the discharge loop's remaining O(Q²) set allocations and O(Q × lowering) cost scale poorly for large Q. Prerequisite: fully mutable representation throughout lowering.

2. **`provePrenexRewrite` is not interruptible** — the `while locateForall(currentFormula).isDefined` loop has no `checkInterrupted()` call. In v2 this produced 6 Stuck workers; in v5 they become 8 Timeouts (the OOM interrupt no longer fires to pre-empt them). A one-line fix at the top of the loop body would eliminate all prenex-caused stuck/timeout cases. Highest-leverage remaining change.

3. **SWW900+1 times out at formula size 3979** — unusually slow. Hypothesis: many quantifiers at moderate depth, worst case for the rewrite strategy (O(nq × depth) per step, repeated nq times). Worth profiling with `--max-stuck 1` to capture a thread dump.

4. **50% OK target not reached** — 39/100 (39%). Of 47 non-skipped problems, 39 succeed and 8 time out. Fixing #2 and raising `--max-size` with the fixes required by #1 are the two most actionable steps.

