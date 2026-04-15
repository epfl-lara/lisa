# Detailed Breakdown of Tableau Prover Optimizations

This document describes every change made to `Tableau.scala` across Sessions 2 and 3, why it was made, and what effect it had.

---

## Session 2: Substitution Backtracking & Bug Fixes

Baseline before Session 2: ~91/243 SYN+1 problems solved (37%).

### 2.1 Predicate Indexing in `closeAll`

**Problem.** The original `closeAll` tried to unify every positive atom against every negative atom — an O(pos × neg) loop. Most pairs have different head predicates and can never unify (`p(X)` can't unify with `q(a)`), so most iterations were wasted.

**Change.** Group negative atoms by their head predicate symbol, then only try to unify against atoms with matching heads:

```scala
// Before: flat traversal of all negatives
for (p <- renamedPos; n <- branch.atoms._2) {
  val unifs = unifyPred(p, n, branch)
  ...
}

// After: index by head predicate, only try matching heads
val negByHead: Map[Expression, Set[Expression]] = branch.atoms._2.groupBy(headPred)
for (p <- renamedPos) {
  val pHead = headPred(p)
  for (n <- negByHead.getOrElse(pHead, Set.empty)) {
    val unifs = unifyPred(p, n, branch)
    ...
  }
}
```

Where `headPred` strips applications to get the predicate symbol:

```scala
def headPred(e: Expression): Expression = e match
  case Application(f, _) => headPred(f)
  case _ => e
```

**Impact.** Modest speedup on problems with many distinct predicate symbols. No change in solve rate, but reduces a constant factor.

---

### 2.2 Substitution Backtracking (Key Completeness Improvement)

**Problem.** The original code called `close(branch)` which returned a single "best" closing substitution from `closeAll`. If that substitution led to a dead-end (i.e., the recursive `decide` after applying the instantiation failed), the whole search failed. This made the prover incomplete: it could miss solutions accessible through alternative substitutions.

**Change.** Instead of picking one substitution, try up to 5 alternatives sorted by `substitutionScore`:

```scala
// Before: single attempt
close(branch) match
  case Some((subst, set)) =>
    // apply subst, recurse — if it fails, return None
  case None => None

// After: backtracking over sorted alternatives
val sorted = validSubsts.sortBy(s => substitutionScore(s._1, branch))
val maxAttempts = 5
var result: Option[...] = None
var attempts = 0
val iter = sorted.iterator
while (result.isEmpty && iter.hasNext && attempts < maxAttempts) {
  val (subst, set) = iter.next()
  attempts += 1
  // apply subst, recurse
  result = decide(currentBranch).map(...)
}
result
```

**Impact.** This was the single most impactful change in Session 2. Solve rate jumped from ~91/243 to **167/243 (69%)** on SYN+1. The key new solve was Pelletier 37 (SYN066+1) — a classic problem that requires trying multiple instantiation candidates to find the correct one.

---

### 2.3 Multi-Binding Instantiation

**Problem.** When `closeAll` returns a substitution like `{X → a, Y → b}`, the original code applied only one binding and recursed, hoping the next `closeAll` would catch the second. This was unreliable.

**Change.** Apply ALL bindings at once, sorted by `varsOrder` (innermost variable first):

```scala
val sortedBindings = subst.toList.sortBy((x, _) => -branch.varsOrder(x))
var currentBranch = branch
var appliedBindings: List[(Variable, Expression, Expression)] = Nil
for ((x, t) <- sortedBindings) {
  val (newBranch, inst) = applyInst(currentBranch, x, t)
  appliedBindings = (x, t, inst) :: appliedBindings
  currentBranch = newBranch
}
// Recurse on branch with ALL instantiations applied
result = decide(currentBranch).map(...)
```

The proof reconstruction then emits one `LeftForall` step per binding.

**Impact.** Fixes incorrect or incomplete handling of multi-variable substitutions. Contributes to the 91→167 improvement along with backtracking.

---

### 2.4 `inverseNewMap` Fix

**Problem.** `closeAll` renames positive-atom variables to avoid capture during unification (e.g., `X` becomes `X'`). The original code identified these renamed variables by checking `v.id.no > branch.maxIndex`. This was incorrect after gamma re-expansion, because the re-expanded variable's index could be beyond `maxIndex`, causing a `NoSuchElementException`.

**Change.** Use `inverseNewMap.contains(v)` to identify renamed variables:

```scala
// Before (crashes on re-expanded gammas):
if v.id.no > branch.maxIndex then ...

// After (correct):
if inverseNewMap.contains(v) then
  if t == inverseNewMap(v) then None  // identity mapping, discard
  else Some(inverseNewMap(v) -> substituteVariables(t, ...))
```

**Impact.** Eliminated `NoSuchElementException` crashes during close-with-instantiation.

---

### 2.5 `validSubsts` Filter

**Problem.** Some closing substitutions from `closeAll` contained variables not present in `branch.unifiable` or `branch.varsOrder` (e.g., Skolem constants or variables from other branches). Applying these caused `NoSuchElementException` in `substitutionScore` and `applyInst`.

**Change.** Filter substitutions before sorting:

```scala
val validSubsts = nonEmpty.filter(_._1.forall((v, _) =>
  branch.unifiable.contains(v) && branch.varsOrder.contains(v)
))
```

**Impact.** Eliminated another class of crashes.

---

### 2.6 Conditional Self-Check

**Change.** `selfCheck = debug` so that the expensive `SCProofChecker.checkSCProof` only runs when `debug=true`, not during benchmarking.

**Impact.** Substantial speed-up for benchmarking (proof checking can be as expensive as proof search).

---

### Session 2 Summary

| Metric | Before | After |
|--------|--------|-------|
| SYN+1 solve rate | ~91/243 (37%) | 167/243 (69%) |
| Correctness baseline | 38/38 | 39/39 (added Pelletier 37) |
| Cross-domain (first 5/domain) | — | 41/84 (49%) |

---

## Session 3: Deferred `closeAll` + Performance Optimizations

Baseline before Session 3: 167/243 SYN+1 (69%), 39/39 correctness.

### 3.1 Beta Unit Propagation

**Problem.** When processing `Or(A, B)`, both branches A and B were fully explored via `decide()`, even when one disjunct trivially conflicted with an existing branch atom. For example, if the branch contains `p(a)` and we split `Or(¬p(a), Q)`, the `¬p(a)` branch is trivially closed — but the original code still called `decide()` to discover this.

**Change.** Two parts:

**Part A — Trivial closure detection.** A new function `findLiteralClosure` checks if a formula, when added to the branch, would immediately contradict an existing atom:

```scala
private def findLiteralClosure(
    f: Expression,
    atoms: (Set[Expression], Set[Expression])
): Option[Set[Expression]] = f match
  case And(_, _) | Or(_, _) | Exists(_, _) | Forall(_, _) => None
  case Neg(inner) =>
    inner match
      case And(_, _) | Or(_, _) | Exists(_, _) | Forall(_, _) => None
      case _ =>
        if atoms._1.contains(inner) then Some(Set(inner, f))  // ¬p found, p on branch
        else None
  case _ =>
    if f == bot then Some(Set(f))
    else if atoms._2.contains(f) then Some(Set(f, !f))  // p found, ¬p on branch
    else None
```

**Part B — Beta formula selection.** Before splitting, scan the beta list to find a disjunction where one disjunct trivially closes. Move it to the front:

```scala
// In the beta processing section of decide():
val selectedBranch = branch.beta.find {
  case Or(l, r) =>
    findLiteralClosure(l, branch.atoms).isDefined ||
    findLiteralClosure(r, branch.atoms).isDefined
  case _ => false
} match
  case Some(f) if f.uniqueNumber != branch.beta.head.uniqueNumber =>
    branch.copy(beta = f :: branch.beta.filterNot(_.uniqueNumber == f.uniqueNumber))
  case _ => branch
```

Then, during the `foldLeft` over disjuncts, skip `decide()` for trivially-closing branches:

```scala
val trivialClose = findLiteralClosure(next._2, branch.atoms)
val res = trivialClose match
  case Some(closureSet) =>
    Some((List(RestateTrue(Sequent(closureSet, Set()))), 0))  // instant proof
  case None =>
    decide(next._1)  // full recursive search
```

**Impact.** Saves 1 `decide` call + 1 potential `closeAll` per trivially-closing branch. The cascading effect is significant: once one branch is unit-propagated, the resulting simpler branch may enable more unit propagation. Particularly effective on propositional-heavy problems.

**Correctness:** 39/39 baseline maintained.

---

### 3.2 Per-Level Wall-Clock Time Limits

**Problem.** The solver uses iterative deepening with increasing `instLimits` (1, 2, 3, 5, 8) controlling how many times each universal quantifier can be re-instantiated. Level 0 (instLimit=1) often consumed the entire 60s timeout searching an unsolvable subspace, starving higher levels that might quickly find the proof.

**Change.** Each level gets a wall-clock deadline. Early levels get less time:

```scala
val levelTimeLimits = Seq(5000L, 10000L, 20000L, 40000L, 60000L) // milliseconds

// In the solve loop:
levelDeadline.set(System.currentTimeMillis() + levelTimeLimits(i))

// In decide, abort when deadline exceeded:
if (decideBudget.decrementAndGet() < 0 ||
    System.currentTimeMillis() > levelDeadline.get()) return None
```

**Impact.** Problems that need instLimit ≥ 2 but are otherwise easy now solve instead of timing out. Level 0 gets cut off after 5s, leaving 55s for levels 1–4.

**Correctness:** 39/39 baseline maintained.

---

### 3.3 Connection-Guided Gamma Selection

**Problem.** When multiple universal quantifiers (gamma formulas) are on the branch, the default is to expand them in the order they were added. This is often suboptimal: the first gamma formula might create variables that don't connect to any branch atoms, while a later one might immediately create a closure opportunity.

**Change.** Before expanding a gamma formula, check if its body contains a literal whose head predicate matches an atom already on the branch. If so, move that formula to the front:

```scala
private def hasConnectionToAtoms(
    body: Expression,
    posHeads: Set[Expression],
    negHeads: Set[Expression]
): Boolean = body match
  case And(l, r) =>
    hasConnectionToAtoms(l, posHeads, negHeads) ||
    hasConnectionToAtoms(r, posHeads, negHeads)
  case Or(l, r) =>
    hasConnectionToAtoms(l, posHeads, negHeads) ||
    hasConnectionToAtoms(r, posHeads, negHeads)
  case Exists(_, inner) => hasConnectionToAtoms(inner, posHeads, negHeads)
  case Forall(_, inner) => hasConnectionToAtoms(inner, posHeads, negHeads)
  case Neg(inner) => posHeads.contains(headPred(inner))
  case _ => negHeads.contains(headPred(body))
```

Used in the gamma section of `decide`:

```scala
val posHeads = branch.atoms._1.map(headPred)
val negHeads = branch.atoms._2.map(headPred)
val selectedBranch = branch.gamma.find(f => f match
  case Forall(_, body) => hasConnectionToAtoms(body, posHeads, negHeads)
  case _ => false
) match
  case Some(f) if f.uniqueNumber != branch.gamma.head.uniqueNumber =>
    branch.copy(gamma = f :: branch.gamma.filterNot(_.uniqueNumber == f.uniqueNumber))
  case _ => branch
```

**Impact.** Helps avoid "blind" gamma expansions that create metavariables without any chance of immediate closure. Moderate improvement on problems with multiple quantifiers.

**Correctness:** 39/39 baseline maintained.

---

### 3.4 Structural Ground Closure Check

**Problem.** The only way to detect branch closure was `closeAll`, which involves variable renaming, unification, and substitution computation — all expensive. But in many cases, the branch has two atoms that are **structurally identical** (one positive, one negative) — no unification needed.

**First attempt (FAILED).** Used `uniqueNumber` for comparison:

```scala
// WRONG — uniqueNumber is NOT structural equality in LISA!
val groundMatch = branch.atoms._2.find(n =>
  branch.atoms._1.exists(_.uniqueNumber == n.uniqueNumber))
```

This produced **0/39 correctness** because in LISA, `uniqueNumber` is an incrementally-assigned object ID, NOT a hash-consing key. Two structurally identical expressions created separately have different `uniqueNumber` values.

**Correct implementation.** Use Scala's `==` operator (case-class structural equality) via `Set.contains`:

```scala
// In decide(), before any formula processing:
if branch.atoms._1.contains(bot) then
  return Some((List(RestateTrue(Sequent(Set(bot), Set()))), 0))

if branch.atoms._1.nonEmpty && branch.atoms._2.nonEmpty then
  val groundMatch = branch.atoms._2.find(branch.atoms._1.contains)
  if groundMatch.isDefined then
    val n = groundMatch.get
    return Some((List(RestateTrue(Sequent(Set(n, !n), Set()))), 0))
```

This works because `atoms._1` is a `Set[Expression]`, and `Set.contains` uses `hashCode` + `equals` which implement structural equality for case classes.

**Impact.** Short-circuits `closeAll` for branches with ground complementary atoms. Together with the deferred `closeAll` (§3.5), this is the key to the 12× throughput improvement.

**Correctness:** 39/39 baseline maintained.

**Key lesson:** `uniqueNumber` CANNOT be used for structural equality in LISA. Always use `==` or `Set.contains`.

---

### 3.5 Deferred `closeAll` (MAJOR — 12× Throughput)

**Problem.** Profiling showed that `closeAll` consumed **94–97%** of runtime on hard problems. The original code called `closeAll` at the **top** of `decide`, before processing alpha/delta/beta/gamma formulas. But `closeAll` is only needed at leaf nodes — when all decomposition rules have been applied and the only hope is finding a closing unification.

Most `decide` calls process an alpha formula (And) and recurse. The `closeAll` call at the top was pure waste: after alpha-expanding, the recursive call would immediately call `closeAll` again on the expanded branch.

**Change.** Move `closeAll` to the `else` branch — the point where alpha, delta, beta, and gamma are all empty:

```scala
def decide(branch: Branch): Option[(List[SCProofStep], Int)] = {
  // Budget + deadline check
  if (decideBudget.decrementAndGet() < 0 || ...) return None

  // Ground closure (O(1) via Set.contains) — catches complementary atoms
  if branch.atoms._1.contains(bot) then ...
  if branch.atoms._2.find(branch.atoms._1.contains).isDefined then ...

  if (branch.alpha.nonEmpty)       // Alpha: always process first
    ...
  else if (branch.delta.nonEmpty)  // Delta: Skolemize existentials
    ...
  else if (branch.beta.nonEmpty)   // Beta: split disjunctions (with unit prop)
    ...
  else if (branch.gamma.nonEmpty)  // Gamma: instantiate universals
    ...
  else
    // ONLY HERE: all rules exhausted, try unification-based closure
    val allClosingSubsts = if branch.unifiable.isEmpty then Nil
                           else closeAll(branch)
    ...
}
```

**Profiling results** (SYN413+1, Kalish-Montague 256):

| Metric | Before (closeAll at top) | After (deferred closeAll) |
|--------|--------------------------|---------------------------|
| `decide` calls at Level 0 / 5s | 1,641 | 20,000+ |
| `closeAll` calls at Level 0 / 5s | 1,641 | 68 |
| `closeAll` time % | 97% | ~15% |
| Throughput | 328 decides/s | 4,000 decides/s |

**Impact.** **12× throughput improvement** measured on hard problems. The ground closure check (§3.4) handles the common case of identical complementary atoms in O(1), and `closeAll` is reserved for the rare case where unification is actually needed. This is the single most impactful performance change across both sessions.

**Correctness:** 39/39 baseline maintained.

---

### 3.6 Early Exit in `closeAll` for Empty Substitutions

**Problem.** During the unification loop in `closeAll`, if a pair of atoms unify with an identity substitution (i.e., they're already structurally identical after variable renaming), there's no need to continue computing other substitutions.

**Change.** Check each substitution during the loop. If it maps back to identity, return immediately:

```scala
for (s <- unifs) {
  val isIdentity = s.forall((v, t) =>
    (inverseNewMap.contains(v) && t == inverseNewMap(v)) ||
    (newMap.contains(v) && t == newMap(v))
  )
  if isIdentity then
    val closureSet = Set(p, !n).map(f => substituteVariables(f, inverseNewMap))
    return List((Substitution.empty, closureSet))  // immediate return
  substitutions = (s, Set(p, !n)) :: substitutions
}
```

**Impact.** Minor — the structural ground closure check (§3.4) catches most of these cases before `closeAll` is even called. But this is a safety net for edge cases where the ground check doesn't fire but the unification yields an identity.

**Correctness:** 39/39 baseline maintained.

---

### 3.7 Budget Increase (10×)

**Problem.** After the 12× throughput improvement from deferred `closeAll`, the budget (number of `decide` calls per level) became the binding constraint. Level 0 would exhaust its budget of 20,000 calls in under 1 second, well before the 5s time limit.

**Change.** Increase budgets by 10×:

```scala
// Before:
val budgetLimits = Seq(20000, 100000, 500000, 2000000, 5000000)

// After:
val budgetLimits = Seq(200000, 1000000, 5000000, 20000000, 50000000)
```

**Impact.** Now time limits (§3.2) are always the binding constraint, which means we use the full allocated time per level.

**Correctness:** 39/39 baseline maintained.

---

### 3.8 Atoms Stored as `Set` Instead of `List`

**Problem.** Atoms were stored as `(List[Expression], List[Expression])`. The ground closure check required converting to a `Set` on every `decide` call (`branch.atoms._1.toSet`), which is O(n).

**Change.** Changed the `Branch` field type from `List` to `Set`:

```scala
// Before:
atoms: (List[Expression], List[Expression])
// With conversion in decide():
val posSet = branch.atoms._1.toSet
if posSet.contains(bot) ...

// After:
atoms: (Set[Expression], Set[Expression])
// Direct O(1) lookup in decide():
if branch.atoms._1.contains(bot) ...
```

Updated `prepended` to use `+` instead of `::`:

```scala
case Neg(f) =>
  val head = headPred(f)
  this.copy(
    atoms = (atoms._1, atoms._2 + f),
    negByHead = negByHead.updated(head, negByHead.getOrElse(head, Set.empty) + f)
  )
case _ =>
  this.copy(atoms = (atoms._1 + f, atoms._2))
```

**Impact.** Eliminates O(n) `toSet` conversion on every `decide` call. Also ensures `findLiteralClosure` uses O(1) `contains` instead of O(n) `exists`.

**Correctness:** 39/39 baseline maintained.

---

### 3.9 Pre-computed `negByHead` Index in Branch

**Problem.** `closeAll` computes `branch.atoms._2.groupBy(headPred)` on every call. Since atoms only grow (never shrink) during branch construction, this is redundant work.

**Change.** Added `negByHead` field to `Branch`, maintained incrementally when atoms are added:

```scala
case class Branch(
  ...
  negByHead: Map[Expression, Set[Expression]] = Map.empty
) {
  def prepended(f: Expression): Branch = f match
    ...
    case Neg(inner) =>
      val head = headPred(inner)
      this.copy(
        atoms = (atoms._1, atoms._2 + inner),
        negByHead = negByHead.updated(head, negByHead.getOrElse(head, Set.empty) + inner)
      )
```

In `closeAll`, just read the pre-computed index:

```scala
// Before: recompute every time
val negByHead = branch.atoms._2.groupBy(headPred)

// After: use pre-computed index
val negByHead = branch.negByHead
```

**Impact.** Removes O(neg_atoms) work from every `closeAll` call. Since `closeAll` is now only called at leaf nodes (§3.5), the impact is moderate but non-zero.

**Correctness:** 39/39 baseline maintained.

---

### 3.10 Bot Detection for OL-Simplified Tautologies

**Problem.** Five SYN problems (SYN378+1, SYN396+1, SYN397+1, SYN408+1, SYN411+1) failed with only 1 `decide` call across all levels. Investigation showed that LISA's `reducedNNFForm` simplifies these formulas entirely to `⊥` (bottom). The ground closure check required BOTH positive AND negative atoms to be non-empty, so a branch with just `⊥` as a positive atom and no negative atoms would miss the closure.

**Change.** Check for `⊥` before the general ground closure check, without requiring negative atoms:

```scala
// Before: ⊥ check was inside the "if both nonEmpty" guard
if branch.atoms._1.nonEmpty && branch.atoms._2.nonEmpty then
  if branch.atoms._1.contains(bot) then ...  // UNREACHABLE when atoms._2 is empty!

// After: ⊥ check is independent
if branch.atoms._1.contains(bot) then
  return Some((List(RestateTrue(Sequent(Set(bot), Set()))), 0))

if branch.atoms._1.nonEmpty && branch.atoms._2.nonEmpty then
  val groundMatch = branch.atoms._2.find(branch.atoms._1.contains)
  ...
```

**Impact.** 5 previously-failing problems now solve instantly (21–26ms). These were all problems where the OL equivalence checker determined the negated conjecture was a tautology, simplifying the NNF to `⊥`.

**Correctness:** 39/39 baseline maintained (these problems were not in the baseline).

---

### 3.11 `findLiteralClosure` Fixed to Use Structural Equality

**Problem.** `findLiteralClosure` originally used `uniqueNumber` for atom comparison. As established in §3.4, `uniqueNumber` is NOT structural equality. This was not a correctness issue (it's a heuristic optimization), but it meant unit propagation missed matches between structurally identical atoms that were different objects.

**Change.** Switch to `Set.contains` (structural equality):

```scala
// Before (may miss structurally identical atoms):
if atoms._1.exists(_.uniqueNumber == inner.uniqueNumber) then ...
if atoms._2.exists(_.uniqueNumber == f.uniqueNumber) then ...

// After (correct structural equality):
if atoms._1.contains(inner) then ...
if atoms._2.contains(f) then ...
```

**Impact.** Enables unit propagation to fire in more cases. Minor improvement.

**Correctness:** 39/39 baseline maintained.

---

### 3.12 Profiling Infrastructure

Added lightweight counters behind the `debug` flag. These have zero overhead when `debug=false`:

```scala
var profileDecideCalls = 0L
var profileGroundCloses = 0L
var profileCloseAllCalls = 0L
var profileCloseAllTimeNs = 0L
var profileCloseWithInst = 0L

// In solve():
if debug then pr(s"  Level $i (inst=${instLimits(i)}, budget=${budgetLimits(i)}): " +
  s"decides=$profileDecideCalls, groundCloses=$profileGroundCloses, " +
  s"closeAllCalls=$profileCloseAllCalls, closeAllMs=${profileCloseAllTimeNs/1000000}")
```

These were crucial for diagnosing the `closeAll` bottleneck and measuring the deferred `closeAll` improvement.

---

## Session 3 Summary

| Metric | Before (Session 2 end) | After (Session 3 end) |
|--------|------------------------|----------------------|
| Correctness baseline | 39/39 | 39/39 |
| SYN+1 solve rate | 167/243 (69%) | Pending clean benchmark (expected ≥170) |
| Throughput (hard problems) | ~330 decides/s | ~4,000 decides/s (12×) |
| `closeAll` time share | 94–97% | ~15% |

---

## Attempted and Reverted Changes

### Proof Reconstruction Fix (Reverted)

**Problem.** When `decide` finds a proof via close-with-instantiation (§2.2), the decomposition chain (alpha → delta → gamma → close) may skip some formulas (they weren't needed for the proof). Without `Weakening` steps in the skip paths, the proof sequent's left-hand side may not contain formulas that upstream steps expect.

**Attempted fix.** Add `Weakening` in all skip paths:

```scala
// In alpha section, when formula wasn't used:
else
  val sequent = proof.head.bot +<< branch.alpha.head
  (Weakening(sequent, step) :: proof, step + 1)  // add formula to sequent
```

**Why it was reverted.** The `Weakening` adds the parent formula to the proof's head sequent. In the beta section, the early-success check is:

```scala
if nextProof.head.bot.left.contains(next._2) then // disjunct was used
```

With `Weakening`, the parent formula (which is the disjunction itself or contains the disjunct) appears in `bot.left`, causing the check to fire incorrectly. This prevents the early-success optimization (when one branch proves the whole sequent, skip the other branches), forcing BOTH branches to be explored — exponential blowup.

SYN065+1 went from 167ms to timeout (2s), PUZ031+1 from fast to 15s timeout. Reverted immediately.

---

## Architecture: `decide` Control Flow After All Changes

```
decide(branch):
  ├── Budget/deadline check → return None if exceeded
  ├── ⊥ check → return RestateTrue if bot in positive atoms
  ├── Ground closure → return RestateTrue if complementary atom pair (O(1) Set lookup)
  ├── if alpha.nonEmpty → expand And, recurse
  ├── elif delta.nonEmpty → Skolemize Exists, recurse
  ├── elif beta.nonEmpty → unit-prop selection, split Or, fold-recurse with trivial closure
  ├── elif gamma.nonEmpty → connection-guided selection, expand Forall, recurse
  └── else (leaf node)
       ├── closeAll (unification-based) → only if unifiable.nonEmpty
       ├── Sort by substitutionScore, try up to 5 alternatives
       └── For each: apply all bindings, recurse, build LeftForall proof steps
```

This ensures `closeAll` (the expensive operation) is called ONLY at leaf nodes, while ground closure (O(1)) handles the common case at every node.
