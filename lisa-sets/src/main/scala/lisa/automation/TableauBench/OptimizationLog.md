# Tableau Optimization Log

## Session 3: Deferred closeAll + Performance Optimizations

### Optimizations Applied (in order)

1. **Beta Unit Propagation**: Skip decide for beta disjuncts that trivially conflict with branch atoms. Prefer betas with trivially-closing disjuncts.
2. **Per-Level Wall-Clock Time Limits**: Cut short early iterative deepening levels (5s, 10s, 20s, 40s, 60s) to give higher instLimits more time.
3. **Connection-Guided Gamma Selection**: Prefer gamma formulas whose body mentions head predicates of existing branch atoms.
4. **Structural Ground Closure Check**: HashSet-based O(n) structural equality check before closeAll. Cannot use uniqueNumber (NOT structural equality in LISA).
5. **Deferred closeAll (MAJOR)**: Only call closeAll when all alpha/delta/beta/gamma are exhausted. 12x throughput improvement.
6. **Early Exit in closeAll**: Return immediately when empty substitution found during unification.
7. **Budget Increase (10x)**: From (20K,100K,500K,2M,5M) to (200K,1M,5M,20M,50M).

### Key Findings
- closeAll consumed 94-97% of runtime for hard problems
- uniqueNumber is NOT structural equality in LISA (no hash-consing)
- Proof reconstruction bug exists when close-with-inst creates fresh variables (pre-existing, not fixed — fix breaks beta early-success)

### Results
- **Correctness baseline**: 39/39
- **SYN+1 benchmark**: Pending clean run...
- **Previous baseline**: 167/243 (69%)

---

## Session 2: Substitution Backtracking & Bug Fixes

### Changes Applied
1. **Predicate indexing in closeAll**: Group negative atoms by head predicate symbol, only try to unify with matching predicates. Reduces O(pos × neg) to O(matched_pairs).
2. **Substitution backtracking**: When a closing substitution leads to a dead end, try up to 5 alternative substitutions from closeAll (sorted by substitutionScore). This is the key completeness improvement.
3. **Multi-binding instantiation**: When a closing substitution has multiple variable bindings, apply ALL bindings via applyInst before recursing, instead of applying one and recursing.
4. **inverseNewMap fix**: Use `inverseNewMap.contains(v)` instead of `v.id.no > branch.maxIndex` to correctly identify renamed positive variables. Fixes key-not-found crashes during gamma re-expansion.
5. **validSubsts filter**: Filter closing substitutions to only those whose variables are in both `unifiable` and `varsOrder`, preventing crashes.
6. **Conditional self-check**: `selfCheck = debug` so proof validation only runs when debug=true (not during benchmarking).

### Results
- **Correctness baseline**: 39/39 (added Pelletier 37)
- **SYN+1 domain**: 167/243 (69%) — up from ~91/243 before backtracking
- **Key new solve**: Pelletier 37 (SYN066+1) — solved in 125ms via backtracking
- **Cross-domain (first 5 per domain)**: 41/84 (49%)
- **Broad benchmark (first 100 FOF)**: 35/100

### Representative Timings
| Problem | Before | After | Notes |
|---------|--------|-------|-------|
| SYN066+1 (Pelletier 37) | Timeout | 125ms | Backtracking finds correct substitution |
| SYN048+1 | 32ms | 33ms | No change for easy problems |
| SYN340+1 | ~3000ms | ~3000ms | No change (already solved via varsOrder fix) |

### Known Limitations
- **ALC problems (SYN436-487)**: Very large formulas (446 atoms, 605 connectives). Need efficient propositional reasoning (unit propagation, BCP).
- **Church problems (46.12-46.16)**: Need specific search strategies or connection-driven approach.
- **SYN413+1 (Kalish/Montague 256)**: Needs global substitution — current approach re-derives universal body on each instantiation, causing exponential blowup.
- **SYN365+1**: Needs multiple gamma instantiations with complex function terms. Search space too large.

### Next Directions
1. **Global substitution**: Apply substitutions to atoms lazily, without re-deriving universal bodies. Major refactoring.
2. **Connection-driven instantiation**: Only expand gammas that create potential connections.
3. **Regularity**: Prevent duplicate atoms on a branch.
4. **Propositional simplification**: Unit propagation for large ground-heavy formulas.
