# Tableau Prover Optimization Log

Comprehensive record of all optimizations, fixes, and improvements applied to `Tableau.scala` in the LISA proof assistant. Changes are organized chronologically across sessions.

**Codebase scope:** `Tableau.scala` grew from **462 lines** (main branch, commit `e8e6bd9`) to **~1600 lines** (current working copy), adding ~1140 lines of new logic.

**Branch:** `tableau-benchmark` (4 commits ahead of `main`): `d963593` → `b70c390` → `be1fbca` → `9e7dea0`

**Correctness contract:** After every change, the current `CorrectnessBaseline` suite must pass with all proofs kernel-verified (`SCProofChecker.checkSCProof`). The suite has since grown from 39 to **41 problems** while remaining green throughout. It now covers Pelletier problems (SYN048–SYN340), two propositional formulas (SYN036+1/+2), logic puzzles (PUZ031+1, PUZ047+1, PUZ060+1, PUZ061+1), management theory (MGT002+1, MGT003+1), NLP (NLP001+1), and SEU167+3.

---

## Session 1 (Pre-Benchmark): Original Algorithm

The starting point was a basic free-variable first-order tableau prover with:
- Alpha (∧), Beta (∨), Delta (∃ → Skolemize), Gamma (∀ → free variable) rules
- Single-substitution closure: `close()` returned the "best" (smallest) unifying substitution
- `closeAll` called at the **top** of `decide()` on every recursive call
- No iterative deepening (single pass with unbounded gamma instantiation)
- No time limits or budgets
- `closeAll` used flat iteration over all (positive, negative) atom pairs

---

## Session 2: Substitution Backtracking & Bug Fixes

**Baseline:** ~91/243 SYN+1 problems solved (37%).

### 2.1 Predicate Indexing in `closeAll`

**Problem:** `closeAll` tried every (positive, negative) pair — O(pos × neg). Most pairs have different head predicates and can never unify.

**Change:** Group negative atoms by head predicate via `headPred()` extraction. Only check pairs with matching heads:
```scala
val negByHead = branch.atoms._2.groupBy(headPred)
for (p <- renamedPos) {
  for (n <- negByHead.getOrElse(headPred(p), Set.empty)) { ... }
}
```

**Impact:** Constant-factor speedup; no change in solve rate.

### 2.2 Substitution Backtracking (MAJOR — key completeness improvement)

**Problem:** The original `close()` returned a single "best" substitution. If that substitution led to a dead end after recursive `decide()`, the whole search failed. This made the prover seriously incomplete.

**Change:** Try up to 5 (later 15) alternative substitutions from `closeAll`, sorted by `substitutionScore`:
```scala
val sorted = allClosingSubsts.sortBy(s => substitutionScore(s._1, branch))
var attempts = 0
while (result.isEmpty && iter.hasNext && attempts < maxAttempts) { ... }
```

**Impact:** Solve rate jumped from ~91/243 to **167/243 (69%)** on SYN+1. Pelletier 37 (SYN066+1) — a classic problem requiring exploring multiple substitution candidates — newly solved in 125ms.

### 2.3 Multi-Binding Instantiation

**Problem:** When `closeAll` returns a substitution `{X → a, Y → b}`, the original code applied only one binding and hoped recursion would find the second.

**Change:** Apply ALL bindings at once, sorted by `varsOrder` (innermost variable first), then recurse on the fully-instantiated branch. Proof reconstruction emits one `LeftForall` step per binding.

**Impact:** Fixes incomplete handling of multi-variable substitutions. Contributes to the 91→167 improvement.

### 2.4 `inverseNewMap` Fix (Bug Fix)

**Problem:** `closeAll` renames positive-atom variables to avoid capture. The original code identified renamed variables by `v.id.no > branch.maxIndex`, which was incorrect after gamma re-expansion — fresh variable indices could exceed `maxIndex`, causing `NoSuchElementException`.

**Change:** Use `inverseNewMap.contains(v)` to correctly identify renamed variables:
```scala
if inverseNewMap.contains(v) then
  if t == inverseNewMap(v) then None  // identity mapping
  else Some(inverseNewMap(v) -> substOpt(t, resolveMap))
```

**Impact:** Eliminated `NoSuchElementException` crashes during close-with-instantiation.

### 2.5 `validSubsts` Filter (Bug Fix)

**Problem:** Some closing substitutions contained variables not in `branch.unifiable` or `branch.varsOrder`, causing crashes in `substitutionScore` and `applyInst`.

**Change:** Filter substitutions:
```scala
resolvedSubst.forall((v, _) => branch.unifiable.contains(v) && branch.varsOrder.contains(v))
```

**Impact:** Eliminated another class of crashes.

### 2.6 Conditional Self-Check

**Change:** `selfCheck = debug` so `SCProofChecker.checkSCProof` only runs when `debug=true`.

**Impact:** Substantial benchmarking speedup (proof checking can be as expensive as proof search).

### Session 2 Summary

| Metric | Before | After |
|--------|--------|-------|
| SYN+1 solve rate | ~91/243 (37%) | 167/243 (69%) |
| Correctness baseline | 38/38 | 39/39 (+Pelletier 37) |

---

## Session 3: Deferred `closeAll` + Performance Optimizations

**Baseline:** 167/243 SYN+1 (69%), 39/39 correctness.

### 3.1 Beta Unit Propagation

**Problem:** When processing `Or(A, B)`, both branches were fully explored via `decide()` even when one disjunct trivially conflicted with an existing branch atom.

**Change:** Two parts:
- **`findLiteralClosure`**: Checks if a formula, when added to the branch, immediately contradicts an atom (O(1) via `Set.contains`).
- **Beta selection**: Before splitting, scan the beta list for a disjunction where one disjunct trivially closes. Move it to the front.
- **During fold**: Skip `decide()` for trivially-closing branches, emit `RestateTrue` directly.

**Impact:** Saves `decide` calls + `closeAll` per trivially-closing branch. Cascading effect: each closed branch may enable more unit propagation.

### 3.2 Per-Level Wall-Clock Time Limits + Iterative Deepening

**Problem:** The solver had a single pass. Level 0 could consume the entire timeout searching an unsolvable subspace, starving higher `instLimit` levels.

**Change:** Introduced iterative deepening with 8 levels:
- `instLimits = Seq(1, 2, 3, 5, 8, 12, 20, 30)` — max gamma re-instantiations per variable per level
- `baseLevelTimeLimits = Seq(800, 1500, 3000, 5000, 10000, 20000, 35000, 60000)` ms per level
- `budgetLimits = Seq(200K, 1M, 5M, 20M, 50M, 100M, 200M, 500M)` — max `decide` calls per level
- `levelDeadline` ThreadLocal checked in `decide()`
- Unused time carries forward to later levels via `savedTimeMs`

**Impact:** Problems needing `instLimit ≥ 2` but otherwise easy now solve instead of timing out at level 0.

### 3.3 Connection-Guided Gamma Selection

**Problem:** Gamma formulas expanded in insertion order. First gamma might create irrelevant variables while a later one could immediately enable closure.

**Change:** Before expanding, check if the gamma body's head predicates match branch atoms (`hasConnectionToAtoms`). If so, move that gamma to the front.

**Impact:** Moderate improvement on multi-quantifier problems; avoids "blind" gamma expansions.

### 3.4 Structural Ground Closure Check

**Problem:** Branch closure required `closeAll` (expensive unification). But most closures at intermediate nodes are ground complementary atoms — no unification needed.

**Key lesson learned:** `uniqueNumber` is NOT structural equality in LISA. It's an incremental object ID. Two structurally identical expressions created separately have different `uniqueNumber` values. **Always use `==` or `Set.contains` for structural equality.**

**Change:** O(1) ground closure via `Set.contains` before any formula processing:
```scala
if branch.atoms._1.contains(bot) then return Some(...)
val groundMatch = branch.atoms._2.find(branch.atoms._1.contains)
if groundMatch.isDefined then return Some(...)
```

**Impact:** Short-circuits `closeAll` for ground complementary atoms. Foundation for the deferred `closeAll` optimization.

### 3.5 Deferred `closeAll` (MAJOR — 12× throughput)

**Problem:** Profiling showed `closeAll` consumed **94–97%** of runtime. The original code called it at the TOP of `decide()`, before processing any formulas. But most `decide` calls just process an alpha (And) and recurse — the `closeAll` call was pure waste.

**Change:** Move `closeAll` to the `else` branch — the point where alpha, delta, beta, and gamma are all empty (leaf node):
```
decide(branch):
  ├── ⊥ check (O(1))
  ├── Ground closure (O(1) Set.contains)
  ├── if alpha → expand, recurse
  ├── elif delta → Skolemize, recurse
  ├── elif beta → unit-prop + split, recurse per disjunct
  ├── elif gamma → connection-guided select, expand, recurse
  └── else → closeAll (only at leaf) → try up to 15 substitutions
```

**Profiling result** (SYN413+1):
| Metric | Before | After |
|--------|--------|-------|
| `decide` calls / 5s | 1,641 | 20,000+ |
| `closeAll` calls / 5s | 1,641 | 68 |
| `closeAll` time share | 97% | ~15% |
| Throughput | 328 decides/s | 4,000 decides/s |

**Impact:** **12× throughput improvement**. Ground closure (§3.4) handles the common case; `closeAll` reserved for leaf nodes.

### 3.6 Early Exit in `closeAll` for Identity Substitutions

**Change:** If a unification yields an identity substitution (atoms already structurally identical after variable renaming), return immediately without computing other substitutions.

**Impact:** Minor safety net — most cases already caught by ground closure check.

### 3.7 Budget Increase (10×)

**Problem:** After the 12× speedup, the decide-call budget became the binding constraint (exhausted in <1s).

**Change:** `budgetLimits` increased 10× (20K → 200K at level 0, etc.).

**Impact:** Time limits now bind instead of budgets. Full allocated time per level is utilized.

### 3.8 Atoms Stored as `Set` Instead of `List`

**Change:** `atoms: (Set[Expression], Set[Expression])` instead of `(List, List)`. Updates use `+` instead of `::`.

**Impact:** Eliminates O(n) `toSet` conversion per `decide` call for ground closure check.

### 3.9 Pre-computed `negByHead` and `posByHead` in Branch

**Change:** Added `negByHead: Map[Expression, Set[Expression]]` and `posByHead: Map[Expression, Set[Expression]]` fields to `Branch`, maintained incrementally in `prepended()`.

**Impact:** Removes O(neg_atoms) `groupBy` in every `closeAll` call.

### 3.10 Bot Detection for OL-Simplified Tautologies

**Problem:** Five SYN problems (SYN378+1, SYN396+1, SYN397+1, SYN408+1, SYN411+1) where `reducedNNFForm` simplifies the formula entirely to `⊥`. The ground closure check required BOTH positive AND negative atoms non-empty, so a branch with just `⊥` missed closure.

**Change:** Check `⊥` independently before the general ground closure check.

**Impact:** 5 previously-failing problems now solve instantly (21–26ms).

### 3.11 `findLiteralClosure` Fixed to Use Structural Equality

**Change:** Replaced `uniqueNumber` comparison with `Set.contains` for atom matching in unit propagation.

**Impact:** Unit propagation fires in more cases.

### 3.12 Profiling Infrastructure

**Change:** Lightweight counters behind `debug` flag: `profileDecideCalls`, `profileGroundCloses`, `profileCloseAllCalls`, `profileCloseAllTimeNs`, `profileCloseAllSubstCount`, etc. Zero overhead when `debug=false`.

**Impact:** Essential for diagnosing the `closeAll` bottleneck and measuring improvements.

### Session 3 Summary

| Metric | Before | After |
|--------|--------|-------|
| Correctness baseline | 39/39 | 39/39 |
| SYN+1 solve rate | 167/243 | ≥170/243 |
| Throughput (hard problems) | ~330 decides/s | ~4,000 decides/s (12×) |
| `closeAll` time share | 94–97% | ~15% |

---

## Session 4: Infrastructure Speedups + Enhanced Gamma Probes

**Baseline:** 39/39 correctness, ~175/180 SYN+1 (r≤0.20).

### 4.1 `substOpt`: Reference-Preserving Substitution

**Problem:** `substituteVariables` allocates new `Application` objects even when no substitution applies (the subexpression is ground).

**Change:** New `substOpt` returns the same object reference when no substitution applies, avoiding GC pressure:
```scala
private def substOpt(e: Expression, m: Map[Variable, Expression]): Expression = e match
  case v: Variable => m.getOrElse(v, v)
  case _: Constant => e
  case app @ Application(f, arg) =>
    val newF = substOpt(f, m)
    val newArg = substOpt(arg, m)
    if (newF eq f) && (newArg eq arg) then app
    else Application(newF, newArg)
  case _ => substituteVariables(e, m)
```

Applied to 10+ call sites: unification, closeAll, delta, gamma, applyInst, groundSaturation.

### 4.2 `collectMetaVars`: Mutable-Set-Based Meta-Variable Collection

**Change:** New utility replaces `e.freeVariables.filter(unifiable.contains)` with a targeted mutable-set walk:
```scala
private def collectMetaVars(e: Expression, unifiable: Map[Variable, ?],
    result: scala.collection.mutable.Set[Variable]): Unit = e match
  case v: Variable => if unifiable.contains(v) then result += v
  case Application(f, a) => collectMetaVars(f, ...); collectMetaVars(a, ...)
  ...
```

**Impact:** Avoids intermediate `Set` allocations at each tree level.

### 4.3 Incremental `posMetaVars` / `negMetaVars` in Branch

**Change:** Added `posMetaVars: Set[Variable]` and `negMetaVars: Set[Variable]` fields to `Branch`, updated incrementally in `prepended()`. Used in `closeAll` for shared-variable computation instead of scanning all atoms.

**Impact:** Avoids full-atom-set scan in `closeAll` setup.

### 4.4 `unifyPredOpt`: Option-Based Unification

**Change:** New `unifyPredOpt` / `unifyOpt` returns `Option[Substitution]` instead of `Iterator[Substitution]`. Since first-order unification is deterministic (0 or 1 results), this avoids `Iterator`/`flatMap` allocation overhead.

**Impact:** Reduced allocation in `closeAll`'s inner loop.

### 4.5 Adaptive Time Allocation (saved time carry-forward)

**Change:** If a level finishes early (budget-limited), the unused wall-clock time carries to the next level:
```scala
val levelElapsed = System.currentTimeMillis() - levelStart
savedTimeMs = math.max(0L, effectiveTimeMs - levelElapsed)
// Next level: baseLevelTimeLimits(i+1) + savedTimeMs
```

**Impact:** Problems that breeze through early levels get more time at higher `instLimits`.

### 4.6 Enhanced Concrete Gamma Probes

**Problem:** The gamma section always creates a free variable. For problems where the right instantiation term is already on the branch, trying concrete ground terms first can find the proof without free-variable backtracking.

**Change:** Before free-variable gamma expansion, try concrete instantiation with:
1. **Ground saturation hints** (from preprocessing, highest priority)
2. **Connection terms** (from `extractConnectionTerms` — body atoms matched against branch atoms)
3. **General ground terms** (Skolem constants, individual constants on the branch)

Budget-limited probing (per-level budget of 30 probes):
- Each probe: up to `concreteProbeMaxBudget` decides, `concreteProbeMaxTime` ms
- Adaptive scaling based on `pendingWork` (remaining gamma + delta formulas)
- Only on first expansion of each gamma

```scala
val allProbeTerms = if hintTerms.nonEmpty then ...
    connectionTerms ++ groundTerms ... up to 16 terms
while (concreteResult.isEmpty && gIter.hasNext && ...) {
  val term = gIter.next()
  val concBody = substOpt(body, Map(v -> term))
  // ... probe with limited budget
}
```

**Impact:** SYN334 (Church 46.14(6), r=0.05) improved from 3857ms → ~1951ms (2× speedup). Several problems solved slightly faster.

### 4.7 `topLevelCompatible` Pre-Filter

**Change:** Defined a quick compatibility check that rejects atom pairs where constant arguments differ:
```scala
private def topLevelCompatible(e1: Expression, e2: Expression): Boolean = (e1, e2) match
  case (Application(f1, a1), Application(f2, a2)) =>
    val argsOk = (a1, a2) match
      case (c1: Constant, c2: Constant) => c1 == c2
      case _ => true
    argsOk && topLevelCompatible(f1, f2)
  case (c1: Constant, c2: Constant) => c1 == c2
  case _ => true
```

Used in `closeAll` to skip full unification for obviously incompatible pairs.

**Important caveat:** Because `closeAll` has a time cap (3–5ms), making it faster per call changes which substitutions are collected before the cap fires, altering search behavior. This was the root cause of several regressions during development. The filter is currently used but with awareness of this interaction.

### 4.8 Adaptive `closeAll` Caps

**Change:** Caps in `closeAll` scale based on number of metavariables (`nUnifiable`):
| Condition | maxSubstitutions | maxRawTotal | deadline |
|-----------|-----------------|-------------|----------|
| nUnifiable > 10 | 30 | 500 | 3ms |
| nUnifiable > 6 | 100 | 2000 | 3ms |
| else | 100 | 5000 | 5ms |

**Impact:** Prevents `closeAll` explosion on problems with many metavariables while allowing thorough search on simpler problems.

### Attempted and Reverted (Session 4)

| Change | Reason for Revert |
|--------|-------------------|
| Application penalty 50→15 | SYN334 regression (changed search order via scoring) |
| maxAttempts 15→30 | SYN334 regression (more attempts per leaf = slower) |
| topLevelCompatible with generous 20-30ms cap | Changed search balance |
| Gamma re-expansion probing | Extra budget consumption without benefit |
| `connectionScore` gamma scoring (ranked vs boolean) | MGT001 regression (different gamma expansion order) |

### Session 4 Summary

| Metric | Before | After |
|--------|--------|-------|
| Correctness baseline | 39/39 | 39/39 |
| SYN+1 (r≤0.20, 15s) | ~175/180 | 175/180 (no regression) |
| SYN334 | 3857ms | ~1951ms (2× speedup) |

---

## Session 5: Gamma-Before-Beta Scheduling + Thread Safety

### 5.1 Gamma-Before-Beta Scheduling

**Problem:** The original order was alpha → delta → **beta** → gamma. Beta splitting before gamma expansion meant definition atoms (from universal axioms) weren't on the branch during splitting, preventing unit propagation.

**Change:** When there are unexpanded gamma formulas (first-time expansion), **defer beta splitting**:
```scala
val hasFirstTimeGamma = branch.gamma.nonEmpty && branch.gamma.exists {
  case Forall(v, _) => branch.numberInstantiated.getOrElse(v, -1) == -1
  case _ => false
}
// ... beta only when !hasFirstTimeGamma
```

**Impact:** Major improvement for biconditional-heavy problems (SET, SEU) where definition axioms create atoms that enable unit propagation during beta splitting.

### 5.2 `extractConnectionTerms` Recurses Into Nested Quantifiers

**Problem:** `extractConnectionTerms` returned `Nil` for `Forall`/`Exists` bodies, missing connections in multi-variable gamma formulas like `∀x.∀y. P(x,y) ∧ ...`.

**Change:** Added recursion:
```scala
case Forall(_, inner) => extractAtoms(inner)
case Exists(_, inner) => extractAtoms(inner)
```

**Impact:** Concrete gamma probes find useful terms in nested-quantifier problems.

### 5.3 Connection Probes for All Gamma Sizes

**Change:** Removed the restriction that connection-guided probing only activated for `gamma.size >= 10`. Now all problems benefit.

### 5.4 Thread Interrupt Checking

**Change:** Added `Thread.currentThread().isInterrupted` check in `decide()` and the solve loop. Prevents leaked threads from consuming resources during batch scans.

### 5.5 Concrete Gamma Budget = 30 Per Level

**Change:** Set `concreteGammaBudget.set(30)` per level (was 10 in earlier iterations). Budget consumed by each probe attempt (`concreteGammaBudget.decrementAndGet()`).

### 5.6 Tighter Level Time Limits

**Change:** Reduced early level times:
- Before: `Seq(2000, 3000, 5000, 5000, 15000, 30000, 45000, 60000)` ms
- After: `Seq(800, 1500, 3000, 5000, 10000, 20000, 35000, 60000)` ms

Helps reach higher `instLimits` faster.

### Attempted and Reverted (Session 5)

| Change | Reason for Revert |
|--------|-------------------|
| `instDepth` limiting (cap recursive instantiation depth) | Caused 3 regressions (PUZ031+1, MGT002+1, MGT003+1) — too aggressive for deep chains |
| Probe budget increase (150→500 decides, 40→100ms) | Added overhead without solving new problems |

---

## Session 6: Ground Saturation Preprocessing + SInE Filtering

### 6.1 Ground Saturation Preprocessing (`groundSaturation`)

**Problem:** The concrete gamma probe only finds terms already on the current branch. For Skolem-chain reasoning (e.g., MSC012+1 needs `sk2(sk(A))`), the terms are created by FUTURE gamma expansions and the probe can't discover them.

**Change:** Added a preprocessing pass (~140 lines) that performs iterative ground forward chaining:
1. Decompose the NNF formula into atoms, gammas, and pending formulas
2. For each gamma `∀v. body(v)`:
   - Find connection terms by matching body atoms against current atoms (using `matchBodyPartial` with wildcards for inner variables)
   - Instantiate body with discovered terms
   - Decompose the result: alphas → expand, deltas → Skolemize, atoms → add to index
   - Handle betas conservatively (only if all but ≤2 disjuncts already resolve)
3. Repeat for up to 8 rounds or until no new atoms are generated
4. Track discovered hints: `Map[Long, List[Expression]]` mapping gamma `uniqueNumber` to useful terms
5. Early exit when `posAtoms` and `negAtoms` both empty (pure-logic problems skip entirely)

Caps: `maxTotalGammas = 200`, `maxRounds = 8`, `candidateTerms.take(3)` per gamma, dedup via `processedPairs`.

Hints are stored in `groundHints` ThreadLocal and used as highest-priority terms in concrete gamma probes.

**Impact:** Provides useful probe terms for problems needing multi-step Skolem reasoning.

### 6.2 SInE (Sumo Inference Engine) Relevance Filtering

**Problem:** Large problems (200+ axioms, e.g., KRS domain) overwhelm the tableau with irrelevant axioms.

**Change:** For problems with >30 left-side formulas:
1. Extract constant/function symbols from each axiom
2. Start from conjecture symbols, iteratively add axioms whose rarest symbol is active (depth=3)
3. If filtering removes ≥25% of axioms, use filtered version first
4. If filtered version fails, fallback to full problem with remaining time

```scala
val useFiltering = leftSeq.size > 30 && rightSeq.nonEmpty
val (filteredLeft, wasFiltered) = if useFiltering then
  val selected = sineFilter(leftSeq, rightSeq)
  ...
```

**Impact:** KRS problems that previously timed out on 200+ axioms now solve in seconds with 40-60 relevant axioms.

### 6.3 Solver Deadline Passing

**Problem:** The solver had no awareness of the external timeout. The benchmark harness interrupted the thread, but the solver couldn't plan its time budget accordingly.

**Change:** Added `solverDeadline` ThreadLocal + `setDeadline(deadlineMs: Long)` public method. The benchmark harness calls `Tableau.setDeadline(System.currentTimeMillis() + timeoutMs)` before `solve()`. The solver computes:
```scala
val effectiveGlobalDeadline = math.min(globalDeadlineMs, solverDeadline.get())
```
The level loop checks remaining time and skips levels with <200ms remaining.

**Impact:** SET590+3 improved from 4905ms → 2656ms. More intelligent time distribution.

### 6.4 `allProbeTerms` Fast Path

**Change:** When ground saturation produces no hints (the common case for pure-logic problems), skip the `ListBuffer` + `uniqueNumber` dedup overhead:
```scala
val allProbeTerms = if hintTerms.nonEmpty then { /* dedup with ListBuffer */ }
  else if connectionTerms.nonEmpty then {
    connectionTerms ++ groundTerms.filterNot(connSet.contains).take(8 - connectionTerms.size)
  } else groundTerms.toList
```

**Impact:** Avoids allocation overhead for the majority of problems that don't benefit from ground saturation.

### 6.5 N-ary Beta Splitting with Disjunct Sorting

**Change:** `beta()` flattens nested `Or` into n-ary disjuncts and sorts by complexity:
```scala
val disjuncts = flattenOr(f).sortBy(disjunctComplexity)
disjuncts.map(d => (b1.prepended(d), d))
```
Atoms first (score 1), `And` (40), `Or` (60), `Exists` (80), `Forall` (100).

Proof reconstruction uses `LeftOr` with the flattened disjunct list. Kernel accepts via OL equivalence (Or commutativity + associativity).

**Impact:** Simpler disjuncts tried first, reducing search tree size.

### 6.6 Beta Score-Based Ordering with `disjunctClosureScore`

**Change:** Before splitting, score each beta formula by the closure potential of its disjuncts:
- Score 0: ground closure (literal complement on branch)
- Score 1: potential unification closure (matching head predicates)
- Score 2: complex formula (needs further expansion)
- Score 3: no closure potential

Process the beta with the lowest `betaScore` first. Only reorder when bestScore ≤ 1 (at least one ground/unification closure).

### 6.7 Early Unification Closure Before Beta

**Change:** Before beta processing, when `branch.beta.size >= 4` and no pending first-time gammas, attempt `tryInstantiations(branch, 3)`:
```scala
val earlyClose = if (branch.beta.size >= 4 && !hasFirstTimeGamma && branch.gamma.isEmpty
                     && branch.unifiable.nonEmpty && ...) then tryInstantiations(branch, 3) else None
```

**Impact:** Avoids exploring exponential beta trees when a unification-based closure exists.

### 6.8 Early Close for Large Gamma Lists

**Change:** Before gamma expansion, when `branch.gamma.size > 30` and `branch.unifiable.size >= 3`, attempt `tryInstantiations(branch, 3)`.

**Impact:** Helps KRS/DL problems with 60+ definitional axioms find proofs without expanding all gammas.

### 6.9 `tryGroundInstantiation` Fallback (Written but Not Wired)

**Change:** New function that tries instantiating metavariables with ground terms from the branch when `closeAll` can't find the right substitution:
```scala
private def tryGroundInstantiation(branch: Branch): Option[(List[SCProofStep], Int)]
```
Generates (metavar, ground_term) pairs sorted by formula penalty, tries up to 5 with full `decide()`.

**Note:** This function exists in the codebase but is currently **not called** from `decide()`. It was written as a fallback strategy but never wired in because the existing substitution backtracking already handles most cases where it would help.

---

## Sessions 7–8: Benchmark Infrastructure + Refactoring (Post-Commit `9e7dea0`)

The last commit (`9e7dea0`, April 15) was "progress on tableau" at 937 lines. Sessions 7-8 focused on building benchmark infrastructure, performing broad domain analysis, and refactoring the solver interface.

### 7.1 Benchmark Infrastructure Created

**New files in `TableauBench/`:**
- **`QuickTest.scala`**: 36 hand-picked representative problems across 9 domains (ALG, COM, KRS, SET, SEU, SYO, LCL, SWB, MSC). Primary regression test for optimization work.
- **`DomainScan.scala`**: Scans TPTP domains with configurable rating range and timeout. Discovers new solvable problems.
- **`BroadScan.scala`**: Samples problems across all domains up to a max rating threshold.
- **`ExploreBench.scala`**: Tests specific problem lists for targeted analysis.
- **`TargetedScan.scala`**: Focused scan on domains with highest potential.
- **`DiagnosticRun.scala`**: Single-problem debug runner with profiling output.

### 7.2 Broad Domain Analysis

Comprehensive scan revealed performance across TPTP domains. Full inventory of FOF Theorem problems per domain:

| Domain | Easy (r≤0.25) | Med (0.25-0.50) | Hard (>0.50) | Total |
|--------|--------------|-----------------|-------------|-------|
| SYN | 180 | 25 | 38 | 243 |
| KRS | 22 | 26 | 34 | 82 |
| CSR | 37 | 7 | 3 | 47 |
| MGT | 15 | 21 | 9 | 45 |
| SET | 7 | 5 | 8 | 20 |
| SEU | 4 | 5 | 6 | 15 |
| LCL | 17 | 1 | 2 | 20 |
| COM | 4 | 0 | 0 | 4 |
| PUZ | 11 | 2 | 2 | 15 |
| NUN | 5 | 3 | 2 | 10 |
| SWB | 5 | 0 | 0 | 5 |
| NLP | 1 | 0 | 0 | 1 |
| MSC | 2 | 0 | 0 | 2 |

### 7.3 `debug = false` by Default

**Change:** Committed with `debug = true`; changed to `debug = false` in working copy.

**Impact:** Eliminates profiling overhead during benchmark runs. Essential for accurate timing.

### 7.4 `solveFormula` Refactoring

**Problem:** The original `solve()` method contained the iterative deepening loop, SInE filtering, and ground saturation all in one method. The benchmark harness couldn't use different formula compositions (e.g., filtered vs full) without duplicating code.

**Change:** Extracted `solveFormula(formulas: Seq[Expression], globalDeadlineMs: Long)` which:
1. Conjuncts all formulas via `K.multiand`
2. Renames variables
3. Computes NNF
4. Runs ground saturation
5. Runs iterative deepening loop
6. Returns `Option[(List[SCProofStep], Int, Expression)]` (proof steps, size, NNF formula)

The outer `solve(sequent)` handles SInE filtering and proof framing:
```scala
def solve(sequent: K.Sequent): Option[SCProof] = {
    // SInE filter → solveFormula(filtered) → if fails, solveFormula(full)
    // Frame result with Restate/Weakening
}
```

**Impact:** Cleaner separation of concerns. SInE fallback works correctly with separate `solveFormula` calls.

### 7.5 SInE Fallback: Time-Aware

**Change:** SInE filtered attempt gets first try; if it fails, fallback to full problem gets `max(10000ms, filteredElapsedMs)`:
```scala
val fallbackBudgetMs = math.max(10000L, filteredElapsed)
solveFormula(leftSeq ++ negGoals, System.currentTimeMillis() + fallbackBudgetMs)
```

**Impact:** Balanced time allocation between filtered and fallback attempts.

### 7.6 Proof Framing with Weakening

**Change:** When SInE filtering was used, the proof's conclusion refers to the filtered sequent. Added a `Weakening` step to project it to the full original sequent:
```scala
val scProof = if finalFiltered then
  SCProof((Weakening(sequent, p.length + 1) :: Restate(filteredSequent, p.length) :: 
           Weakening(nf |- (), p.length - 1) :: p).reverse.toIndexedSeq, ...)
```

**Impact:** Kernel-valid proofs even when SInE filtering drops axioms.

### 7.7 Detailed Debug Output for Proof Validation Failures

**Change:** When `debug = true` and proof validation fails, print a detailed step-by-step analysis:
```scala
if !checkResult.isValid then
  def printProofSteps(proof: SCProof, indent: String): Unit =
    proof.steps.zipWithIndex.foreach { (step, idx) =>
      val stepValid = validateStep(proof, step, idx)
      ep(s"${indent}Step $idx [${if stepValid then "OK" else "FAIL"}]: ${stepName(step)} ...")
    }
```

**Impact:** Essential for diagnosing proof reconstruction bugs (which are the hardest to debug).

---

## Session 9: Attempted Optimizations — All Reverted (Post-Commit)

Session 9 focused on trying to improve the QuickTest score above 20/36. Four optimizations were attempted and all were reverted.

### 9.1 Compound Ground Terms in `collectGroundTerms` (REVERTED)

**Attempted change:** Extended `collectGroundTerms` to collect compound terms (like `f(a)`, `g(b,c)`) in addition to leaf constants/variables, giving concrete gamma probes more instantiation candidates.

**Result:** Net-neutral. Didn't change the pass count. Some problems slightly faster (SET590+3: 2506→1191ms with biconditional rewriting), but no new problems solved.

**Why reverted:** No benefit, added complexity.

### 9.2 `matchBodyPartial` in `extractConnectionTerms` (REVERTED)

**Attempted change:** In `extractConnectionTerms`, replaced `matchBody` (which requires exact match for all non-v variables) with `matchBodyPartial` (which treats other variables as wildcards). This would find more connection terms for multi-variable gamma formulas.

**Result:** Net-neutral. Didn't change the pass count.

**Why reverted:** No benefit, could cause false-positive matches.

### 9.3 Probe Depth Limiting (REVERTED)

**Attempted change:** Added depth tracking for concrete gamma probes to prevent cascading probes (probe within prove within probe). Capped at depth 2 using a `probeDepth` ThreadLocal.

**Result:** Net-neutral. Didn't change the pass count.

**Why reverted:** No benefit. The `probeDepth` ThreadLocal still exists as dead code but is unused.

### 9.4 Biconditional NNF Rewriting (REVERTED)

**Attempted change:** Added `rewriteBiconditionals` function that transforms biconditional NNF patterns:
- `Or(And(A,B), And(¬A,¬B))` → `And(Or(¬A,B), Or(A,¬B))`
- `Or(And(A,¬B), And(¬A,B))` → `And(Or(¬A,¬B), Or(A,B))`

This converts compound beta branches (each disjunct is a conjunction) into alpha + simple beta decomposition, which is more amenable to unit propagation.

**Result:** HARMFUL. Caused massive slowdowns:
| Problem | Before | After |
|---------|--------|-------|
| COM003+3 | 19ms | 181ms (9.5× slower) |
| KRS132 | 75ms | 312ms (4.2× slower) |
| KRS146 | 31ms | 1129ms (36× slower) |

**Why reverted:** Even the identity-preserving version (only rewrites when pattern matches) creates more formulas per branch. Each biconditional becomes two alpha-split clauses, increasing the number of atoms on the branch and slowing closeAll. The `rewriteBiconditionals` method still exists as dead code.

### 9.5 COM007+1 Investigation

A significant analysis effort was spent on COM007+1, which appeared to regress from "547ms" (per a prior session summary) to timeout. Investigation revealed:

1. COM007+1 was **already broken at the committed code** (9e7dea0). Testing with `git stash` confirmed.
2. The "547ms" from the prior summary was **incorrect/stale data**.
3. COM007+1's bottleneck is `closeAll`: at level 0, 1236 calls consuming 542ms with 280K unification attempts.
4. `topLevelCompatible` is a weak filter — it only rejects when both arguments are different constants.

**Interesting development:** In the latest QuickTest run (Session 10+), COM007+1 now **passes at 614ms** with 10s timeout. This is likely due to the `solveFormula` refactoring (§7.4) changing the NNF formula composition slightly, or JVM warmup differences.

### Session 9 Summary

All four optimizations reverted. Net change: 0 new problems solved.

---

## Current State (April 17, 2026)

### QuickTest Results: 20/36 (10s timeout)

| # | Problem | Status | Time |
|---|---------|--------|------|
| 1 | ALG211+1 | PASS | 408ms |
| 2 | COM003+1 | FAIL | Timeout |
| 3 | COM003+2 | FAIL | No proof found |
| 4 | COM003+3 | PASS | 120ms |
| 5 | COM007+1 | PASS | 614ms |
| 6 | KRS130+1 | PASS | 3ms |
| 7 | KRS132+1 | PASS | 90ms |
| 8 | KRS146+1 | PASS | 32ms |
| 9 | KRS151+1 | FAIL | Timeout |
| 10 | KRS153+1 | FAIL | Timeout |
| 11 | KRS159+1 | FAIL | Timeout |
| 12 | SET009+3 | FAIL | No proof found |
| 13 | SET043+1 | PASS | 2ms |
| 14 | SET044+1 | PASS | 5ms |
| 15 | SET045+1 | PASS | 2ms |
| 16 | SET588+3 | FAIL | Timeout |
| 17 | SET590+3 | PASS | 2648ms |
| 18 | SET899+1 | PASS | 0ms |
| 19 | SEU158+1 | PASS | 3ms |
| 20 | SEU163+1 | PASS | 1ms |
| 21 | SEU263+1 | FAIL | Timeout |
| 22 | SEU264+1 | FAIL | Timeout |
| 23 | SYO525+1.015 | FAIL | No proof found |
| 24 | SYO578+1 | PASS | 39ms |
| 25 | SYO607+1 | FAIL | Timeout |
| 26 | LCL636+1.001 | PASS | 7ms |
| 27 | LCL644+1.001 | PASS | 2ms |
| 28 | LCL644+1.010 | PASS | 6ms |
| 29 | LCL654+1.001 | PASS | 85ms |
| 30 | LCL672+1.001 | FAIL | Timeout |
| 31 | SWB001+2 | PASS | 1ms |
| 32 | SWB004+2 | FAIL | Timeout |
| 33 | SWB012+2 | FAIL | Timeout |
| 34 | SWB016+2 | FAIL | Timeout |
| 35 | MSC011+1 | PASS | 2ms |
| 36 | MSC012+1 | FAIL | Timeout |

### CorrectnessBaseline: 39/39 PASS (kernel-verified)

### Dead Code in Current Working Copy

The following code exists but is **unused** (remnants from reverted Session 9 experiments):
- `rewriteBiconditionals`: ~35 lines, never called
- `matchBodyPartial` (top-level method): ~15 lines, only used from `groundSaturation` (not from `extractConnectionTerms`)
- `probeDepth` ThreadLocal: declared but never read or updated
- `flattenAnd`: ~4 lines, never called
- `tryGroundInstantiation`: ~40 lines, never called from `decide()`
- `connectionScore`: ~10 lines, never called (superseded by `hasConnectionToAtoms`)
- Duplicate doc comments on `solveFormula` (3 adjacent Scaladoc blocks)

### Architecture Summary: Current `decide()` Control Flow

```
decide(branch):
  ├── Budget + deadline check → None if exceeded
  ├── Thread interrupt check → None if interrupted
  ├── ⊥ check → RestateTrue if bot in positive atoms
  ├── Ground closure → RestateTrue if complementary atom pair (O(1))
  │
  ├── Compute hasFirstTimeGamma (unexpanded gammas exist?)
  │
  ├── if alpha.nonEmpty → expand And, recurse
  ├── elif delta.nonEmpty → Skolemize Exists, recurse  
  ├── Early unification closure (beta.size ≥ 4, no first-time gammas, gamma empty)
  │     └── tryInstantiations(branch, 3)
  ├── elif beta.nonEmpty && !hasFirstTimeGamma
  │     ├── Beta score ordering (ground closure disjuncts first)
  │     ├── N-ary splitting with disjunct complexity sort
  │     ├── Unit propagation (findLiteralClosure per disjunct)
  │     └── fold-recurse with early-success optimization
  ├── elif gamma.nonEmpty
  │     ├── Unexpanded gamma priority (when hasFirstTimeGamma)
  │     ├── Connection-guided gamma selection
  │     ├── Early close for large gamma lists (>30 gammas, ≥3 metavars)
  │     ├── Concrete gamma probes (ground sat hints > connection terms > ground terms)
  │     │     └── Budget-limited: 30 probes/level, adaptive time/decides per probe
  │     └── Free-variable gamma expansion (default)
  └── else (leaf node) → tryInstantiations(branch, 15)
        ├── closeAll (unification with adaptive caps)
        ├── Sort by substitutionScore, try up to 15 alternatives
        └── Multi-binding instantiation per candidate
```

### Key `solve()` Entry Point Flow

```
solve(sequent):
  ├── SInE filtering (if >30 left-side formulas)
  │     └── Select axioms by symbol-frequency trigger (depth=3)
  ├── solveFormula(filtered or full formulas, deadline)
  │     ├── multiand → makeVariableNamesUnique → reducedNNFForm
  │     ├── groundSaturation(nf) → hints map
  │     └── Iterative deepening loop (8 levels)
  │           ├── Set budgets, deadlines per level
  │           └── decide(Branch.empty.prepended(nf))
  ├── If SInE filtered and no proof → fallback to full problem
  └── Frame proof: Restate + Weakening steps for kernel acceptance
```

### Key Bottlenecks Identified (For Future Work)

1. **`closeAll` dominance**: Still consumes 60-83% of total time on hard problems. The `topLevelCompatible` filter is weak — only rejects when both arguments are different constants.

2. **No incremental `closeAll`**: Every `closeAll` call checks ALL positive × negative atom pairs. When only one new atom was added since the last call, most work is redundant.

3. **No equality reasoning**: ~50% of CSR problems and many SET/SEU problems require equality reasoning (paramodulation or superposition), which the current tableau doesn't support.

4. **SYO525+1.015 and COM003+2 return "No proof found"** (not timeout): This suggests a completeness issue at the current `instLimit` levels, not a performance issue.

5. **Failing problems by category:**
   - **Timeout (needs faster search):** COM003+1, KRS151/153/159, SET588+3, SEU263/264, SYO607, LCL672, SWB004/012/016, MSC012
   - **No proof found (needs higher completeness):** COM003+2, SET009+3, SYO525+1.015

---

## Evolution Summary

| Session | Major Change | SYN+1 Impact | QuickTest Impact |
|---------|-------------|-------------|-----------------|
| 1 | Original algorithm | 37% (91/243) | N/A |
| 2 | Substitution backtracking | 69% (167/243) | N/A |
| 3 | Deferred closeAll (12× throughput) | ≥70% (170+/243) | N/A |
| 4 | substOpt, unifyOpt, concrete probes | ~72% (175/180 at r≤0.20) | N/A |
| 5 | Gamma-before-beta scheduling | Same SYN, helps SET/SEU | N/A |
| 6 | Ground saturation, SInE, n-ary beta | Same SYN, helps KRS/SET | ~20/36 |
| 7-8 | Benchmark infrastructure + refactoring | Same | 20/36 (baseline) |
| 9 | All experiments reverted | Same | 20/36 |
| 10 | Probe-depth + GS namespace/probing fixes | Same SYN, +easy-scan robustness | 79/105 on self-contained easy scan |
| 11 | `closeAll` pruning + GS budget tuning | Same solve profile, lower wasted work | Correctness preserved; groundwork for next scan |

**Total lines added:** ~1140 (462 → 1600)  
**Correctness maintained:** 39/39 through Session 10, then 41/41 after the baseline expansion in Session 11

---

## Lessons Learned

1. **`uniqueNumber` ≠ structural equality** in LISA. Two structurally identical expressions created separately have different `uniqueNumber`s. Always use `==` for structural comparison.

2. **Heuristic interactions are dangerous.** `closeAll` has a time cap; making it faster per-call changes which substitutions are collected, altering downstream search behavior. This caused multiple unexpected regressions.

3. **Biconditional rewriting is counterproductive** for this tableau architecture. Even when it creates more "unit-propagable" patterns, the increased atom count per branch outweighs the benefit.

4. **`closeAll` cost scales with atoms, not formulas.** Once formulas are decomposed into atoms, the O(pos × neg) inner loop dominates. Predicate indexing helps but isn't enough for large branches.

5. **Iterative deepening is essential.** Without it, level 0 (instLimit=1) can consume the entire timeout. The carry-forward time allocation ensures higher levels get fair budget.

6. **SInE filtering works well for KRS/description-logic problems** with 100+ axioms. The 75% threshold (keep if <75% filtered) and depth=3 trigger are good defaults.

7. **Ground saturation preprocessing is niche but valuable.** It helps exactly when the proof requires multi-step Skolem-chain reasoning (e.g., substituting `f(g(a))` when `f`, `g`, `a` are separately on the branch). Most pure-logic problems get no benefit and skip it quickly.

8. **Probe budgets must be tight.** Concrete gamma probes are speculative — each failed probe consumes decides from the main budget. The current caps (150-600 decides, 40-150ms, 30 probes/level) balance discovery vs overhead.

---

## Session 10: Probe Depth, GS Namespace, and Biconditional Improvements

**Baseline:** 78/105 self-contained easy problems (rating ≤ 0.10, max 10/domain), 10s timeout.

### 10.1 Probe Depth Limit
**Problem:** Cascading probes (probe within probe) consumed budget exponentially. A probe at depth N spawns inner probes at depth N+1, each using decideBudget.
**Change:** Added `probeDepth` tracking via `ThreadLocal[Int]`. Gate probing on `currentProbeDepth < 2`. Increment before entering probe, restore after.
**Impact:** LCL672+1.001 (682ms, was timeout) and TOP022+1 (626ms, was timeout) newly solved. MGT002+1 improved from ~5s to ~1.8s. Overall: 79/105 (+1).

### 10.2 GS Contradiction Detection  
**Problem:** When ground saturation's beta resolution had 0 unresolved disjuncts, this meant all disjuncts contradict current atoms — a contradiction! GS wasn't detecting this.
**Change:** Added `if (unresolved.isEmpty) return hints.toMap` before the `unresolved.size <= 2` check. Kept the `<= 2` propagation for hint generation.
**Impact:** GS returns earlier for problems with contradictions. SEU167+3 hints: 128→61 for 29→17 gammas.

### 10.3 GS Namespace Fix (MAJOR)
**Problem:** GS created its own Skolem constants (index ≥ 100000) which were in a DIFFERENT namespace from the main solver's delta-decomposed constants. GS hint terms like `Variable('A', 100000)` didn't match any branch atoms. All probing with GS hint terms was USELESS.
**Change:** Added `decomposeAlphaDelta(branch)` helper that fully decomposes all alphas and deltas. GS now receives the pre-decomposed branch atoms (with main solver's Skolem constants). GS no longer creates its own top-level Skolem constants. GS hint term filtering removes remaining GS-internal Skolems (from inner existentials during forward chaining).
**Impact:** GS now produces hints in the correct namespace. SEU167+3: 61→373 hints for 17→67 gammas. Connection terms prioritized over (filtered) hint terms in probing.

### 10.4 extractConnectionTerms Fix
**Problem:** `extractConnectionTerms` used `matchBody` (strict matching) which requires non-v variables to match exactly. For nested gammas `∀A∀B∀C.body(A,B,C)`, inner bound variables (B, C) never match branch constants, so no connection terms were found.
**Change:** Added `matchBodyPartial` fallback (wildcards for non-v variables) after `matchBody` fails. Now finds connection terms for nested gammas.
**Impact:** More connection terms for nested gamma formulas.

### 10.5 Extended Biconditional Rewriting
**Problem:** `rewriteBiconditionals` only detected `Or(And(A,B), And(¬A,¬B))` where ¬ is SYNTACTIC. For `A ⟺ (B₁∧B₂)`, the NNF produces `Or(And(A,B₁,B₂), And(¬A,¬B₁∨¬B₂))` where the second component uses DeMorgan (Or instead of And), not simple negation.
**Change:** Added `isNNFNeg` helper that checks DeMorgan negation (And↔Or with negated children). Added `nnfNegate` that produces NNF negation with DeMorgan. Both simple and DeMorgan patterns are now checked.
**Impact:** Enables biconditional rewriting for complex biconditionals with compound RHS.

### 10.6 Results Summary
| Metric | Before | After |
|--------|--------|-------|
| Self-contained scan (≤0.10) | 78/105 | 79/105 |
| Correctness baseline | 39/39 | 39/39 |
| Newly passing | — | LCL672+1.001, TOP022+1 |
| Regression | — | SEV515+1 (borderline timing) |

**Key regression:** SEV515+1 (rating 0.05, "Russell's paradox") was borderline at 10s timeout. Cumulative overhead from GS pre-decomposition + probe changes pushed it just over. Passes at ~12s timeout.

---

## Session 11: `closeAll` Pruning, GS Budget Tuning, and Baseline Expansion

This round did not introduce a new proof-search strategy. Instead, it consolidated the previous GS/probing work, removed avoidable overhead on common paths, and updated the regression suite to cover two more representative problems.

### 11.1 Skip `closeAll` When No Meta-Variables Can Participate

**Problem:** `tryInstantiations` could still call `closeAll` on branches where unification had no useful work left to do because either there were no unifiable variables at all, or no metavariables appeared in the current atoms.

**Change:** Added an early guard in `tryInstantiations`:
```scala
val allClosingSubsts =
  if branch.unifiable.isEmpty || (branch.posMetaVars.isEmpty && branch.negMetaVars.isEmpty)
  then Nil
  else closeAll(branch)
```

**Impact:** Avoids paying the `closeAll` setup and pair-scanning cost on branches where only ground closure is possible. This is a pure overhead reduction and preserves behavior.

### 11.2 Lazy Positive-Atom Renaming in `closeAll`

**Problem:** Even after predicate indexing, `closeAll` still renamed positive atoms eagerly, including atoms whose head predicate had no matching negative atom.

**Change:** Positive atoms are now renamed lazily, only after confirming that the atom's head predicate has at least one negative candidate:
```scala
for (posOrig <- branch.atoms._1.iterator if !done) {
  val pHead = headPred(posOrig)
  val negCandidates = negByHead.getOrElse(pHead, Set.empty)
  if (negCandidates.nonEmpty) then
    val p = if newMap.isEmpty then posOrig else substOpt(posOrig, newMap)
    ...
}
```

**Impact:** Cuts unnecessary `substOpt` work on large branches with many unmatched atoms. This is especially relevant on KRS/SET-style branches where indexing removes most pairs but the old rename path still touched every positive atom.

### 11.3 `deepCompatible` Pre-Filter Before Unification

**Problem:** `topLevelCompatible` only rejects obvious constant/constant clashes. It misses another common failure mode in LISA: ground solver variables (including Skolem-like variables outside `unifiable`) that cannot possibly unify.

**Change:** `closeAll` now calls `deepCompatible` before `unifyPredOpt`. The filter recursively rejects:
- ground-variable vs different ground-variable mismatches
- ground-variable vs constant mismatches
- the original constant/constant mismatches

**Impact:** More impossible pairs are eliminated before unification. As with all `closeAll` micro-optimizations, the main goal is reducing wasted inner-loop work without changing the substitution search order more than necessary.

### 11.4 Beta Scoring Updated for Conjunctive Disjuncts

**Problem:** After biconditional rewriting, some beta disjuncts are conjunctions. The old closure score treated them as opaque complex formulas, missing cases where one conjunct immediately closes.

**Change:** `disjunctClosureScore` now inspects `And` disjuncts by flattening them and reusing the literal scoring logic:
```scala
case And(_, _) =>
  val conjuncts = flattenAnd(f)
  val bestConjunctScore = conjuncts.iterator.map(c => disjunctClosureScore(c, atoms, negByHead)).min
  if bestConjunctScore == 0 then 1 else 2
```

**Impact:** Beta ordering better reflects the actual closure potential of disjuncts produced by biconditional rewriting. This is a heuristic-quality improvement rather than a completeness change.

### 11.5 Ground Saturation Capacity Increase

**Problem:** The original GS caps were conservative enough that some forward-chaining-heavy problems exhausted GS before enough useful hints had been collected.

**Change:** The GS pass was widened in several places:
- `maxRounds`: 8 → 25
- `maxTotalGammas`: 200 → 500
- per-gamma term fanout: `candidateTerms.take(3)` → `take(5)`
- GS wall-clock budget now scales with remaining solve time, using up to 25% of the remaining budget, with a floor of 500ms and a cap of 5s

**Impact:** GS can pursue longer forward-chaining chains before giving up. This is targeted at problems where useful concrete instantiation terms only emerge after several rounds of derived atoms.

### 11.6 Probe Budget Scales With Hint Volume

**Problem:** A flat concrete-gamma probe budget underutilizes good GS output on forward-chaining problems and overpays on problems with no usable hints.

**Change:** Per-level probe budget now depends on the total number of GS hints:
```scala
val hintCount = hints.values.map(_.size).sum
val probeBudget = if hintCount > 50 then math.min(200, hintCount) else 30
concreteGammaBudget.set(probeBudget)
```

**Impact:** Problems with strong GS evidence receive more speculative concrete probes, while the default remains conservative on ordinary problems.

### 11.7 Correctness Baseline Expanded to 41 Problems

**Change:** Added two problems to `CorrectnessBaseline.scala`:
- `PUZ047+1` (wolf/goat/cabbage)
- `SEU167+3` (set-theory theorem)

**Impact:** The always-green regression suite now covers more of the behaviors touched by the recent tableau work, especially around richer branching and set-theoretic structure. The baseline remains **41/41 PASS**.

### 11.8 Observed Performance Effect

This round's changes were mostly **cost-profile improvements** rather than new completeness machinery. The expected runtime wins are concentrated in three places:
- fewer useless `closeAll` invocations (`tryInstantiations` guard)
- less per-call `closeAll` overhead (lazy renaming + `deepCompatible` pruning)
- better use of GS/probe budget on forward-chaining problems (larger GS budget only when time permits, and larger probe budget only when hints justify it)

These changes were validated primarily by keeping the expanded correctness suite green while checking that representative problems remain comfortably within their time budgets. Post-change timings from the April 20 correctness run included:

| Problem | Role | Time | Notes |
|---------|------|------|-------|
| `SYN066+1` | classic substitution-backtracking case | 9ms | Confirms the newer closure pruning does not regress Pelletier 37 |
| `PUZ047+1` | newly-added regression case | 197ms | Exercises richer branching with the expanded baseline |
| `MGT002+1` | branchy non-trivial baseline case | 63ms | Remains comfortably below its 10s cap |
| `MGT003+1` | branchy management-theory case | 162ms | No slowdown from the extra GS/closure guards |
| `SEU167+3` | GS/set-theory stress case | 1850ms | Still solves within its 5s regression budget |

These numbers are **not** controlled before/after microbenchmarks for Session 11 in isolation. They are representative post-change timings showing that the solver remains fast on the baseline while the new pruning and GS-budget logic stays within acceptable overhead.

---

## Current State (April 20, 2026)

This snapshot supersedes the earlier April 17 status notes above where they conflict with the current working copy.

### Verified Status

- **CorrectnessBaseline:** 41/41 PASS (kernel-verified)
- **Probe depth limiting:** active in the gamma probe path
- **`rewriteBiconditionals`:** active from `solveFormula`, no longer dead code

### Stale Notes Corrected

The earlier "Dead Code in Current Working Copy" section is partially outdated. In the current code:
- `rewriteBiconditionals` is called from `solveFormula`
- `probeDepth` is read and updated during concrete gamma probing

The still-unused items from that older list are the genuinely dormant ones such as `tryGroundInstantiation` and `connectionScore`.

### Remaining Technical Theme

The prover is still bottlenecked primarily by leaf-level closure search and by forward-chaining problems that need better term discovery. The last round improved the cost profile of those paths, but it did not yet change the fundamental open problems: `closeAll` remains the dominant hotspot on hard branches, and GS still needs strong term-generation to turn forward-chaining evidence into actual solves.
