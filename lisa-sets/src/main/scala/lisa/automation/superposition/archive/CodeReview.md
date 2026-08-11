# Code review — `clausification/` and `superposition/`

**Date:** 2026-08-08 · **Reviewed:** every `.scala` file in
`lisa-sets/src/main/scala/lisa/automation/{clausification,superposition}/` and
`lisa-sets/src/test/scala/lisa/automation/{clausification,superposition}/`, plus the 18 `.md` documents
that live alongside the superposition sources. State reviewed: working tree after the `ScreenPhase`
input-screening fix (so `RenamePhase.scala` is gone and `ScreenPhase.scala` is new).

**Scale:** 13 clausification sources (~2 900 lines), 25 superposition sources (~10 400 lines), 25 test
files (~4 400 lines), 4 287 lines of markdown, 208 KB of `.txt` problem lists.

---

## 0. Verdict

This is unusually good code. The engineering is deliberate throughout: opaque integer types over a flat
arena, hash-consing exploited for O(1) identity, allocation-free hot paths, indexed and linear variants of
every retrieval kept side by side and A/B-tested for equivalence. The commentary is genuinely explanatory —
it says *why*, cites E/Vampire/Prover9 by file and function, and flags what is deliberately incomplete. Most
codebases this size have nothing comparable.

The problems are almost all **entropy problems**, not design problems: comments that were true two phases
ago and are now false, parameter lists that grew organically across four call layers, and test scaffolding
that leaked into production sources. Two things rise above that: a **latent cache-invalidation hazard** in
`Order`, and a **catch-all exception handler** in the tactic that converts internal bugs into ordinary
tactic failure. Both are cheap to fix.

Nothing found is a soundness bug. The kernel is the backstop and the pipeline is kernel-checked end to end.

Findings are grouped by theme; each carries a severity: **[H]** fix soon, **[M]** worth doing, **[L]** nice
to have.

---

## 1. Correctness risks and latent hazards

### 1.1 ~~**[H]** `Order.orientCache` rests on an unstated, unenforced ordering invariant~~ — FIXED 2026-08-08

*Resolved: `Signature.orderingVersion` is bumped by every weight/precedence write, `Order.orient` stamps its
memo with it and clears on a mismatch, and `Precedence.assign` now runs before the selector is built. Two
regression tests in `OrderTest` (both confirmed to fail without the stamp). Original finding below.*


[`Order.scala:38-56`](Order.scala) memoises equation orientation keyed on the atom's arena offset, and never
invalidates. Its justification reads:

> *Safe to cache because the KBO weights/precedence are fixed once the problem signature is set.*

The real invariant is stronger and is nowhere stated: **no `orient` call may happen before
`Precedence.assign` runs.** Precedence is read *live* by `KBO.compare`
([`KBO.scala:141,208`](KBO.scala)), so an orientation computed before assignment would be cached under the
interning-order precedence and silently outlive it.

Today the invariant holds, but only just. In [`Bridge.solve`](Bridge.scala):

```scala
125:  bank.selector = LiteralSelection.selector(selection, bank)   // forces bank.order (lazy val)
134:  Precedence.assign(sig, bank, clauses, precedenceScheme)      // ...and only now is precedence real
```

Line 125 already forces the `Order`. It happens to be harmless because forcing only *constructs* the
object, and the first `orient` call is at clause activation — well after line 134. But any future code that
compares a term between bank construction and `Precedence.assign` (a preprocessing pass, a clause-ordering
heuristic, a debug print) would poison the cache permanently and produce a subtly wrong term ordering — the
kind of bug that shows up as "the prover got slower and stopped refuting three problems", not as a crash.

The same latent dependency exists for de-indexing: `updateSuperpositionIndices(c, add = false)`
([`Discount.scala:551`](Discount.scala)) re-derives `fromSides(c, sel)` and relies on `orient` returning
*exactly* what it returned at insertion, or entries leak into the index forever.

**Fix as applied:** rather than constrain the callers (a `require` would have broken the many tests that
legitimately never call `Precedence.assign`), the cache now invalidates *itself*. `Signature` carries an
`orderingVersion` counter bumped by every write to a symbol's weight or precedence — `SymbolInfo.weight` and
`.precedence` became `def`/`def_=` pairs so no call site changed — and `Order.orient` compares it against the
version its entries were computed under, clearing on a mismatch. Assigning precedence late, twice, or never
is now safe by construction rather than by convention. `Precedence.assign` was also moved above the selector
construction in `Bridge.solve`, which is now a clarity choice, not a correctness one.

### 1.2 **[H]** ~~The tactic's catch-all converts internal bugs into ordinary failure~~ — WON'T FIX

*Reviewed and declined: the preceding arm catches `NotRefuted` and the catch-all prints the exception class
and message, so an internal error is distinguishable in the reported text. Recorded as considered.*


[`SuperpositionTactic.scala:64-67`](SuperpositionTactic.scala):

```scala
try Right(CertifiedFastClausifier.certifyClausal(problem, prover))
catch
  case nr: NotRefuted => Left(s"Superpose could not refute the goal (${nr.reason}).")
  case e: Throwable   => Left(s"Superpose failed: ${e.getClass.getSimpleName}: ${e.getMessage}")
```

The second arm swallows *everything*: a `require` violation in a phase, an index-arithmetic error, an
`AssertionError` from `Trail.matchTerm`, a `StackOverflowError`. All become "Superpose failed", which reads
to a user exactly like "your goal isn't provable".

This is not hypothetical. The clausification bug fixed this session (`InstSchema` on a variable free in an
assumption) surfaced as a *kernel rejection*; had it thrown instead, this handler would have hidden it, and
`SuperposeTacticTest` would have reported a clean tactic failure rather than a defect. The new
"fails cleanly" test asserts on the message prefix precisely to work around this — that workaround is
evidence the handler is too broad.

**Fix:** catch `NotRefuted` and `InterruptedException` only; let the rest propagate. If a tactic must never
throw, at minimum re-throw `Error` subclasses and tag the message unmistakably (`INTERNAL ERROR — please
report`) so it cannot be mistaken for an unprovable goal.

### 1.3 ~~**[H]** `lowerKernelProofWithAssumptions` documents itself as producing invalid proofs~~ — FIXED 2026-08-08

*Investigated and resolved. The claim was **true but blamed the wrong thing**, and its second sentence was
false. The
failure needs a nested `SCSubproof` whose inner proof **has imports**: the shallow rewrite weakens only the
nested conclusion, so the inner imports keep their original LHS while the parent premises discharging them
gain the assumptions, and the kernel's premise/import match fails. Inner **steps** lacking the assumptions —
what the comment blamed — are harmless; that is exactly what the appended `Weakening` legitimises. Verified
by construction: closed nested subproof → valid after lowering; import-bearing → `Premise step #0 is not the
same as import #0 of the subproof`. The pipeline never builds the bad shape (confirmed empirically by arming
a `require` and running the whole suite: zero trips), because its only nested subproofs are
`DistributePhase`'s closed clause proofs. The restriction is now an enforced `require` with an accurate doc,
plus a new `ProofIRTest` pinning both halves. Original finding below.*


[`ProofIR.scala:147-149`](../clausification/ProofIR.scala):

> *Note: The resulting proof is NOT kernel-valid (the SCSubproof's inner steps won't have the assumptions on
> their bots). This is intentional: the clausification pipeline only uses kernel proofs for proof-size
> accounting, not for verification.*

This cannot be right as written. `certifyClausal`'s output *is* kernel-checked — by `ClausalTest`,
`SuperposeTacticTest`, `FofHarness`, and every `Theorem` the tactic produces — and it passes. So either the
comment describes a path that no longer exists, or it describes a real invalid case that is simply never
exercised (in which case a future caller will hit it).

In a pipeline whose entire premise is "full proof reconstruction into the kernel", a comment saying
"intentionally not kernel-valid" is a landmine. It should be resolved to one of: (a) delete it, it is
obsolete; (b) narrow it — "the *imports* of a nested `SCSubproof` are not weakened, which is sound because
they are always discharged from parent imports, never parent steps"; or (c) it is real, and the case needs a
guard.

Note this is exactly the mechanism behind the collision bug: lowering pastes assumptions onto imports. The
right narrow statement is likely the one you identified — closed library imports should not be weakened at
all — which would also make `ScreenPhase` unnecessary for the `P`/`R` half of that bug class.

### 1.4 ~~**[M]** `Reconstruction.identOf` calls a compiler-generated given by name~~ — WON'T FIX

*Reviewed and declined: correct behaviour. Worth recording that the finding was weaker than written — the
codebase already couples to that synthesised name in five other places (`Predef.scala` exports it,
`Syntax.scala` and three tests import it), so a rename breaks loudly at compile time everywhere at once and
`Reconstruction` is not uniquely exposed. Original finding below.*


[`Reconstruction.scala:361`](Reconstruction.scala):

```scala
private def identOf(name: String): K.Identifier = K.given_Conversion_String_Identifier(name)
```

`given_Conversion_String_Identifier` is a name *synthesised by the compiler* from the given's type. Renaming
or re-typing that conversion in the kernel breaks this call site with a confusing error, and nothing signals
the coupling. Prefer `summon[Conversion[String, K.Identifier]](name)` or an explicit named given.

### 1.5 ~~**[M]** Doc/implementation mismatch in indexed forward subsumption~~ — FIXED 2026-08-08

[`Discount.scala:623-626`](Discount.scala) was documented as "stop at the first verified subsumer", but:

```scala
subsumptionIndex.forwardCandidates(m) { c => if !subsumed && Subsumption.subsumes(bank, trail, c, m) then subsumed = true }
```

The descent ran to completion; only the `subsumes` *call* was skipped. Correct, but it walked the whole
≤-cone after the answer was known — and the scan path it is A/B-compared against (`forwardSimplifyScan`)
*does* return on the first subsumer, so the two differed in work done if not in verdict.

**Fixed** by giving `FeatureVectorIndex` a short-circuiting `existsForwardCandidate(q)(pred)` — forward
subsumption asks an existence question, so the ≤-cone descent now stops at the first accepted clause. The
call site loses its mutable `subsumed` flag and reads as the question it is asking. The four collect-style
retrievals (unit-deletion dispatch, char-2 forward SR, backward SR sign-flip, `backwardCandidatesThenInsert`)
genuinely need every candidate and are untouched. `FeatureVectorTest` pins both halves: the verdict agrees
with visiting the whole cone for an arbitrary predicate, and an always-true predicate sees exactly one clause.

*Correction to this finding as originally written:* it claimed `FingerprintIndex.retrieveUnifiable` has a
`Boolean`-returning `visit` and so already supports early exit. It does not — its `visit` is `E => Unit`, and
`Discount.superposeIndexed` works around that with a `refut` variable exactly as this code did. Only
`DiscriminationTree.retrieveGeneralizations` and `Superposition.foreachSubterm` take the `Boolean`
convention. So the retrieval APIs are split two-and-two, and the "make all three agree" suggestion was based
on a miscount; `FingerprintIndex` would be the remaining candidate if that consistency is wanted.

### 1.6 ~~**[L]** Two `assert`s on the hottest path in the engine~~ — MEASURED, NO CHANGE 2026-08-08

*The factual half holds, the cost half does not. Confirmed the asserts are **live** in this build (calling
`matchTerm` with `ps == ts` throws `AssertionError`), so Scala 3 is not eliding them — they do run in
production. But an A/B benchmark found no measurable cost. Workload: an 800-given-clause saturation on a
self-generating clause set (`¬P(x) ∨ P(f(x))`, `P(a)` plus a binary twin), which exercises
unify/bind/restore and subsumption heavily. Removing **both** asserts *and* the `liveBindings` bookkeeping
that exists solely to serve the second one:*

| | run 1 | run 2 | run 3 |
|---|---|---|---|
| asserts + `liveBindings` present | 556.9 ms | 550.1 ms | 495.4 ms |
| both removed | 542.3 ms | 535.2 ms | 527.0 ms |

*The distributions overlap completely; identical code varies ±3% run to run and the two arms differ by less
than that. `Predef.assert` is JIT-inlined, the branches are perfectly predicted, and `liveBindings` is a
two-element array that never leaves L1. So the checks are free in practice — which makes running them in
production a **feature**: a genuine soundness precondition is verified on every call at no cost. Left
exactly as they are. Original finding below, with its cost claim now known to be wrong.*


[`Core.scala:672-673`](Core.scala), in `Trail.matchTerm`:

```scala
assert(ps != ts, "matchTerm: pattern and target scopes must differ")
assert(liveBindings(ts) == 0, "matchTerm: target scope must have no live bindings ...")
```

Scala's `assert` is a normal method call, live unless the whole build passes `-Xdisable-assertions` — unlike
Java's `-ea`-gated asserts. `matchTerm` is called once per literal pair per subsumption attempt, i.e.
millions of times per saturation. The checks are valuable (they encode a genuine soundness precondition), so
the right move is not deletion but making them explicitly build-gated, or hoisting them to the *callers*
(`Subsumption.subsumes`, `Demodulation.tryRewrite`, `DiscriminationTree.descend`) where they run once per
clause rather than once per literal.

### 1.7 ~~**[L]** `Clausal.proveOutcome` does a linear scan per used import~~ — FIXED 2026-08-08

*Replaced the `work0.indexOf(w)` scan with a `HashMap[Sequent, Int]` built once, first occurrence winning so
duplicate input clauses resolve exactly as before. `ClausalTest` gains a characterisation test for that
tie-break (a clause set containing an exact duplicate still composes a kernel-valid proof declaring every
clause).*

*Two honest notes on the justification. First, the stronger reason turned out to be **robustness, not
speed**: `indexOf` returns `-1` on a miss, and `-(-1 + 1)` is `0`, so an import the clausifier never produced
silently became a reference to step 0 rather than an error. The lookup now throws with the offending sequent.
Second, I did **not** measure a wall-clock win, and won't claim one — `base.imports` is the cone of `□`,
usually tens of clauses, so the quadratic only bites when a large fraction of a large clause set is used, and
constructing that workload is contrived. The change stands on the asymptotics and the failure mode, not on a
benchmark. Original finding below.*


[`Clausal.scala:139-143`](Clausal.scala):

```scala
val premises: Seq[Int] = base.imports.map { w =>
  val i = work0.indexOf(w)     // O(|work0|) per used import
  ...
}
```

O(n·m) in clause count × used-import count, with `Sequent` structural equality as the comparison — the
expensive kind. A `Map[K.Sequent, Int]` built once makes it linear. On CASC-sized inputs (thousands of
clauses) this is measurable, and it sits on the certified path.

Secondary subtlety: if two input clauses are *equal* sequents, `indexOf` returns the first for both. Sound
(the sequents are identical), but it silently deduplicates in a way the surrounding code does not mention.

---

## 2. ~~Documentation that contradicts the code~~ — DONE 2026-08-08

*All nine swept, plus two more found during the sweep (below the table). `tsi`/`tsApp` renamed to
`nm`/`nmApp` in `NamingStep`; `PLAN.md`, `Phase1.md` and `JOURNAL.md` given `Status: historical` headers
listing what has since changed. Phase references that are pure **provenance** ("Phase 5, Step 3" pointing at
the design doc) were deliberately left — the rule applied was to remove phase-relative *tense* (claims about
what is not yet done), not every mention of a phase.*

*Two additional stale rationales surfaced while sweeping, both worth more than the original nine because
they justify a **default** with a condition that no longer holds:*

- *[`Discount.scala:56-58`](Discount.scala) justified `forwardSubsumptionResolution = false` by "without term
  indexing it is a much heavier cost" — but both directions are indexed now (the sign-flip queries over
  `subsumptionIndex`). The default may still be right; it is simply no longer justified by that reason.*
- *[`Discount.scala:64-66`](Discount.scala) said "Revisit once indexing makes it cheap" for
  `forwardSimplifyAtGeneration`. Indexing shipped in Phase 5, so that condition is **met** and the seed-42
  ablation backing the default predates it.*

*Both comments now say so explicitly. **Update 2026-08-08: the ablations were re-run** against TPTP-v9.2.1
(seed 42, n=100, same parameters as the originals) and all three defaults are now measured rather than
inherited — see the "Re-ablation after Phase-5 indexing" section of `Benchmarks.md`:*

| *default* | *verdict* |
|---|---|
| *`forwardSimplifyAtGeneration = false`* | *kept — indexing narrowed the gap 4→2 problems but did not tip it* |
| *`forwardSubsumptionResolution` / `backward…`* | ***flipped to `true`** — +6 refuted, none lost, `bad_proof=0`* |
| *`condensation = false`* | *kept — first time it was ever measured; loses 3, gains none* |

These are cheap to fix and disproportionately damaging: they are the comments a new reader trusts most.

| Location | Says | Reality |
|---|---|---|
| [`Bridge.scala:27-28`](Bridge.scala) | "equality is treated as an ordinary predicate for now — no paramodulation until Phase 3" | Superposition, demodulation, equality resolution/factoring all landed (Phase 4) and are on by default |
| [`Inference.scala:51-52`](Inference.scala) | "Equality trivials (`s = s`, `s ≠ s`) … intentionally not handled yet (Phase 3 …)" | The *next nine lines* (55-64) handle exactly that: positive `s = s` returns `None` |
| [`Discount.scala:364`](Discount.scala) | "equalities get equality-factoring in Phase 3" | Equality factoring is invoked 27 lines below, at line 391 |
| [`Order.scala:196-200`](Order.scala) | `compareClause` is "consumed by superposition's premise-comparison gate and demodulation's redundancy check" | Neither uses it. `Superposition` never calls it; `Demodulation.isPremiseRedundant` uses `kbo.compare` directly. Only `OrderTest` calls it |
| [`Clausal.scala:9,21`](Clausal.scala) | File headline "Phase 3 — clausification wiring", "See `Phase3.md` for the full plan" | The file is now the whole prover adapter + CASC setup + distinct-object axioms; the phase framing is the least useful thing to lead with |
| [`Bridge.scala:108`](Bridge.scala), [`Clausal.scala:151`](Clausal.scala), [`CertifiedFastClausifier.scala:71`](../clausification/CertifiedFastClausifier.scala) | "Tseitin atoms `tsᵢ`", field `tsi` | The clausifier renamed these to `nm` (`GeneratedNames.namingAtom`) and does *selective naming*, not Tseitin. The `tsi` field name and every `tsᵢ` in prose are stale |
| [`JOURNAL.md:3-4`](../clausification/JOURNAL.md) | Files: `ClausificationTPTPBench.scala`, `ClausificationStressTest.scala`; describes `certifyTseitin` | Neither file exists; `certifyTseitin` is now `certifyFastNaming` |
| [`Phase1.md`](Phase1.md) (9 lines) | "The selected literal is the first negative literal … otherwise the first literal" | That is `FirstNegativeSelector`, explicitly documented as **not** BG-complete; the default is `CompleteBestLiteralSelector` |
| [`PLAN.md:6-16`](PLAN.md) | Phase 3 written in future tense ("Phase 3 is the integration"), Phases 3–5 unmarked | All three are implemented and tested; Phase 5 indexing is on by default |

**Recommendation:** a single pass to (a) delete phase-relative tense from *code* comments — phase numbers
belong in the phase documents, not in Scaladoc that outlives them; (b) mark `PLAN.md` phases done; (c) rename
`tsi` → `nm`/`namingVar` and fix the `tsᵢ` prose; (d) either delete `Phase1.md` (9 lines, superseded) or
fold it into `Phase2.md`.

The systemic lesson: **Scaladoc that references a project phase will rot.** A comment saying "not yet
implemented" is a promise the code cannot keep. Prefer "this function does not do X; X is handled by Y".

---

## 3. Duplication and structural pressure

### 3.1 ~~**[H]** The search-knob chain: one option, four edits~~ — DONE 2026-08-08

*[`SearchOptions`](SearchOptions.scala) now holds all 23 search knobs and is threaded whole. `Discount` takes
it and does `import opts.*`, so its 970-line body is byte-identical — the diff is the constructor only. The
parameter documentation moved into `SearchOptions`, where it is now in one place instead of spread over four
signatures with three of them out of date.*

*What it fixed beyond tidiness:*

- ***the drop-through asymmetry is gone.*** *`Bridge.solveTPTPProblem` re-declared a 13-knob subset, so the
  literal selector, precedence scheme and weight scheme were unreachable through it — the clausal benchmark
  literally could not vary what the FOF one could. It now forwards `opts` whole.*
- ***the positional-boolean hazard is gone.*** *Both eleven-boolean positional call sites
  (`Bridge.solveTPTPProblem` → `solve`, and `Evaluation` → `solveTPTPProblem`) are single `opts` arguments.*
- ***`Clausal.proveOutcome` gained `goal`***, *which `solveOutcome` had and it did not, for no reason — so
  goal-directed selection was unavailable on the certified path even though the clausifier knows which
  clauses are the goal.*
- ***the equality auto-gate is now visibly the only mutation:*** *`opts.copy(equality = opts.equality &&
  hasEquality)` in `Bridge.solve`, where before it was one line among sixteen hand-forwarded arguments.*

*`Strategy` becomes `(name, SearchOptions, sine, orthologic)`. Its eight definitions read as `base.copy(…)`,
which makes the documented "each differs from `balanced` in exactly two knobs" property checkable by eye.
The portfolio's `base` deliberately pins SR **off** — the engine default flipped to on in the same session's
re-ablation, and adopting it here would have silently turned #6/#7's "full simplification" axis into a no-op.
Preserving behaviour was the point: the refactor changes no search.*

*Verified behaviour-preserving on the corpus, not just by a green suite: 453 tests pass (0 canceled, with
`TPTP` set) and the seed-42 SR ablation reproduces 80 refuted exactly. Original finding below.*


The same ~20 search parameters are declared, defaulted, and forwarded through four layers:

| Layer | Params | File |
|---|---|---|
| `Discount` constructor | 22 | [`Discount.scala:42-107`](Discount.scala) |
| `Bridge.solve` | 22 | [`Bridge.scala:80-121`](Bridge.scala) |
| `Bridge.solveTPTPProblem` | 13 | [`Bridge.scala:173-193`](Bridge.scala) |
| `Clausal.solveOutcome` | 15 | [`Clausal.scala:172-180`](Clausal.scala) |
| `Clausal.proveOutcome` | 7 | [`Clausal.scala:132-134`](Clausal.scala) |
| `Strategy` | 11 | [`Strategies.scala:17-29`](Strategies.scala) |

Adding a knob means touching four files and getting six defaults consistent. Three concrete consequences
already visible:

- **`solveTPTPProblem` silently drops knobs.** It cannot set `selection`, `precedenceScheme`,
  `weightScheme`, `goal`, `subsumptionIndexing`, or `demodulationIndexing`. `Evaluation` — the *clausal*
  benchmark harness — goes through it, so that benchmark cannot vary the selector or precedence at all,
  while `FofHarness` (a different harness) can. That asymmetry is invisible from the call sites.
- **Positional booleans.** [`Bridge.scala:188-193`](Bridge.scala) forwards eleven `Boolean`s positionally:

  ```scala
  solve(problemSequents(problem), maxGiven, maxMillis, forwardSubsumption, backwardSubsumption,
        forwardUnitDeletion, backwardUnitDeletion, forwardSubsumptionResolution, backwardSubsumptionResolution,
        condensation, forwardSimplifyAtGeneration, equality = equality, ...)
  ```

  Transposing any two compiles cleanly and changes the search silently. `Evaluation.scala:167-172` does the
  same at its call site.
- **`Clausal.proveOutcome` vs `solveOutcome`** differ in which knobs they expose for no principled reason —
  `proveOutcome` (the certified path) can't set `goal`, so goal-directed selection is unavailable to
  `Superpose` even though the machinery exists and the clausifier knows which clauses are the goal.

**Recommendation:** one `case class SearchOptions(...)` with defaults, threaded whole. `Strategy` becomes
`SearchOptions` plus a name and the preprocessing flags (`sine`, `orthologic`). `Bridge.solve` takes
`(sequents, budget, SearchOptions, wiring)`. This is a mechanical, well-contained refactor and it removes
the positional-boolean hazard, the drop-through asymmetry, and three of the four edit sites at once.

### 3.2 ~~**[M]** `Discount` is 976 lines doing six jobs~~ — DONE 2026-08-08 (Stages 1–3)

*Three of the six jobs extracted; `Discount` is **920 → 391 lines** and is now the loop plus activation and
generation. Total across the four files is larger, as extraction always is; what changed is that each
invariant now has an owner.*

- ***[`PassiveSet`](PassiveSet.scala)*** *(91 lines) — the two lazy-deletion queues, the age/weight
  alternation, and the live-membership set.*
- ***[`ActiveSet`](ActiveSet.scala)*** *(256 lines) — the buffer **and all seven shadows**: demodulators
  (list or discrimination tree), the into/from/positive/negative/demod-subterm fingerprint indices, the
  feature-vector subsumption index, and the unit sublist. `add` and `remove` are now the only doors in and
  out, so the sync rule that used to be a comment honoured at four call sites is a class boundary. `remove`
  also asserts the precondition its re-derivation depends on (`c.selected != null`).*
- *`fromSides` moved to [`Superposition`](Superposition.scala): the loop and the from-index maintenance must
  derive **identical** entries or the index leaks, so they now share one definition.*
- *`isPosUnitEq` became `Demodulation.isPositiveUnitEquality`.*

*One deliberate behaviour change: `FeatureVectorIndex.backwardCandidatesThenInsert`'s **fusion was dropped**.
It existed to compute `gc`'s feature vector once, at the cost of splitting `gc`'s insertion across
`backwardSimplify` and `activate` fifteen lines apart — exactly the coupling that made a clean `add`/`remove`
interface impossible. The cost is one extra `fillVector` per activation (O(clause size), against a cone
descent). It also means `gc` now enters the subsumption index slightly later, after backward demodulation
rather than before; that is only observable with the non-default `forwardSimplifyAtGeneration`.*

- ***[`Simplifier`](Simplifier.scala)*** *(335 lines) — every redundancy step: forward/backward subsumption,
  unit deletion, general subsumption resolution, condensation, and backward demodulation, each in its indexed
  and scanning variant. The counters moved with it into a `SimplificationStats`, surfaced from `Discount` by
  delegating `def`s so the ~15 test assertions that read `d.forwardSubsumed` are untouched.*

*The backward methods take an `emit` callback rather than returning their replacements — a deliberate
departure from the original plan. Returning a list works for subsumption resolution, whose replacements are
already collected and added in a batch, but **not** for backward demodulation, which interleaves rewrite,
removal and re-add per clause: deferring those re-adds would move the `canonicalize` calls inside them and
shift clause ids, and with them the whole search trajectory. The callback keeps the interleaving exact.*

*Verified after **each** stage: 454 tests pass (0 canceled) and the seed-42 corpus ablation reproduces **80
refuted with an identical refuted set** — compared by problem name, not merely by count.*

*Stage 4 (`Generator`) deliberately not done — see the plan's own assessment: generation calls `addPassive`
per inference and short-circuits on `□`, so extracting it needs a sink callback on the hottest path for
little gain. `Discount` at 391 lines is a reasonable size. Original finding below.*


[`Discount.scala`](Discount.scala) holds: the given-clause loop; the passive set (two queues + lazy
deletion); the active set (+ `activeIndex` swap-with-last); maintenance for *five* indices (`intoIndex`,
`fromIndex`, `posLitIndex`, `negLitIndex`, `demodSubtermIndex`, `demodTree`, `subsumptionIndex`,
`activeUnits`, `activeDemodulators`); forward and backward simplification, each in an indexed *and* a scan
variant; and instrumentation counters.

The dual indexed/scan variants are the right call (they are what makes the A/B tests possible), but they
double the surface: `forwardSimplify`/`forwardSimplifyIndexed`/`forwardSimplifyScan`,
`backwardSimplify`/`…Indexed`/`…Scan`, `scanGenerate` vs `resolveIndexed`+`superposeIndexed`,
`backwardDemodulateStep` vs `backwardDemodulateIndexed`. Eight of the ten `private def`s between lines 548
and 955 are index bookkeeping, not saturation logic.

**Recommendation:** extract `ActiveSet` (the buffer + `activeIndex` + `detachAux` + all
`update*Index`/`remove*` routines — everything that must stay in sync when a clause enters or leaves
active) and `Simplifier` (forward/backward × indexed/scan). The loop then reads as the loop. The invariant
"every auxiliary structure is updated exactly where `active` is mutated" becomes a class invariant instead
of a comment at line 924.

### 3.3 ~~**[M]** `Evaluation.scala` duplicates the harness that `FofHarness` already abstracts~~ — DONE 2026-08-08, *narrower than recommended*

*The recommendation was to generalise `FofHarness` over the entry point and make `Evaluation` a config like
its two siblings. **I did not do that**, and the measurement is why. The two harnesses differ in more than the
dataset: the pipeline (clausify-then-prove with per-phase timings vs. solve-already-CNF), the columns (`HYP`/
`CJ`/`clausify`/`prover`/`check` vs. `SPC`/`CLS`/`ms`), the row type, and the report (phase breakdowns and
loop stats vs. a category tally). Parameterising over all four would mean passing in four functions — an
abstraction about as large as the duplication it removes, and it would make both harnesses harder to read.*

*What was **actually** duplicated, counted rather than assumed:*

- *the `TPTP`-root check and its hint message — **6 copies across 4 files**, in three slightly different
  wordings (one was just `println("set TPTP")`);*
- *"locate the list, read it, `Random(seed).shuffle(all).take(n)`" — **3 copies** (`FofHarness`,
  `Evaluation`, `BaselineBench`).*

*Both are now single: `BenchUtil.tptpRootOrExplain()` and a `ProblemList` class. The second matters beyond
tidiness — benchmark numbers are only comparable when a seed names the *same* problems, so that draw has to
be identical across harnesses by construction rather than by three copies agreeing. Verified directly:
`BaselineBench sample clausal 3 42` and `Evaluation 42 3` both yield `SYN498-1, SET015-1, ANA037-2`.*

*Left alone deliberately: the per-problem pipelines, columns and reports, which are genuinely different
programs. Verified with 454 tests (which assert the sampling contract) plus live runs of both rewired
harnesses. Original finding below.*


`FofEvaluation` and `EqFofEvaluation` are correctly reduced to three-line configs over
[`FofHarness`](FofHarness.scala). `Evaluation.scala` (219 lines) then re-implements the same shape by hand:
list location, seeded sample, `solveRow`, category `report`, `printHeader`, TPTP-root check. It differs only
in dataset (clausal, not FOF) and in going through `Bridge.solveTPTPProblem` rather than the clausifier.

**Recommendation:** generalise `FofHarness` over the *entry point* as well as the dataset, and make
`Evaluation` a config like its two siblings. This also fixes 3.1's dropped-knob asymmetry for free.

### 3.4 ~~**[M]** The test fixture is copy-pasted 16 times~~ — FIXED 2026-08-08

An essentially identical `class Fix` — `Signature` + `TermBank` + `Trail` + `pred`/`fn`/`const`/`app`/`v`/
`pos`/`neg`/`clause` — appears in `BridgeTest`, `DemodulationTest`, `DiscountTest`, `DiscriminationTreeTest`,
`EqualityReconstructionTest`, `EqualitySaturationTest`, `FeatureVectorTest`, `FingerprintTest`,
`InferenceTest`, `KBOTest`, `MatchTest`, `OrderTest`, `PrecedenceTest`, `ReconstructionTest`,
`SubsumptionTest`, `SuperpositionTest` — sixteen files, ~15 lines each, with small arbitrary divergences
(`clause` vs `cl`, some carry `kbo`, some `ord`, some `prop`).

**Recommendation:** one `TermFixture` trait in the test package. ~200 lines removed and, more valuably, the
divergences disappear — right now a reader must diff two fixtures to know whether `cl` and `clause` mean the
same thing.

**Fix.** [`TermFixture.scala`](../../../../../test/scala/lisa/automation/superposition/TermFixture.scala) holds
the common core (`sig`/`bank`/`trail`/`order`/`kbo` + the dozen builders). The count was fourteen `class Fix`
declarations, not sixteen — `PrecedenceTest` and `FingerprintTest` build their signatures inline. Each is now
`class Fix extends TermFixture` plus only its genuine extras (a `DiscriminationTree`, a `subsumes` shorthand,
a non-default selector); ~150 lines removed. The drift is gone: `cl` → `clause` in `SubsumptionTest`,
`ord` → `order` in `OrderTest`.

The base forces `bank.order` eagerly, which is only sound because of the `orderingVersion` stamp added in
§1.1 — a fixture that forces the ordering before its `Precedence.assign` would otherwise cache stale
orientations.

### 3.5 ~~**[L]** Small duplications~~ — FIXED 2026-08-08

- `headAndArgs` is defined privately and identically in [`Bridge.scala:289`](Bridge.scala) and
  [`Clausal.scala:76`](Clausal.scala).
- The `Justification` 8-case match is written out in five places: `Core.mkClause` (packing age/goal),
  `Reconstruction.build`, `CascProver.parents`, `CascProver.ruleName`, `DiscountTest.inputLeaves`. Adding a
  ninth rule means finding all five. A `def premises: List[Clause]` on the enum itself would collapse three
  of them.
- `Cmp`-to-verdict helpers (`cat`) are redefined in four `DiscountTest` tests.

**Fix.** One `Bridge.headAndArgs`, now `private[superposition]`; `Clausal.headAndArgs` and the third copy
(`CascProver.Tptp.flatten`, which the review missed) delegate to it. `Justification.premises: List[Clause]`
added to the enum, collapsing `CascProver.parents` and `DiscountTest.inputLeaves` to one line each. It is
deliberately *not* used in `Core.mkClause`: that runs for every clause ever built and would pay a `List`
allocation, and its match also needs whether the rule advances the age generation. `ruleName` was left alone
too — it is proof-output vocabulary and does not belong in `Core`. The five `cat` copies became one
class-level helper in `DiscountTest`.

---

## 4. Efficiency observations

### 4.1 ~~**[M]** `DistributePhase` multiplies kernel *checking* cost~~ — FIXED 2026-08-08

[`DistributePhase.distributeClauses`](../clausification/DistributePhase.scala) builds, per output clause, an
`SCProof` that embeds its parents' proofs as `SCSubproof`s:

```scala
case Or(a, b) =>
  for ((cA, pA) <- la; (cB, pB) <- lb) yield (cA ++ cB, joinOr(pA, a, pB, b, cA ++ cB))
```

`pA` is *shared* (no memory duplication — these are immutable objects), but it appears as a distinct
`SCSubproof` occurrence `|lb|` times, and `SCProofChecker` re-checks every occurrence. So checking cost
multiplies where memory does not, compounding up the `∧`/`∨` tree. The naming pass bounds the clause count,
which bounds this — but the bound is on clauses, not on re-checked subproof *nodes*, and the two differ by
the product across levels.

Worth measuring before acting: `FofHarness` already reports a `check` phase column, so the data may exist.
If checking dominates on distribution-heavy problems, hoisting each child proof to a single step and
referencing it by index removes the multiplication entirely.

**Fix.** `distributeClauses` now emits one flat step list per hypothesis, straight into the caller's buffer,
where each derivation exists once and later steps cite it by index; the per-clause `SCSubproof` wrappers are
gone. Emitting into the caller's buffer (rather than collecting and re-basing) matters: re-basing means
rebuilding every step through `mapStepPremises` just to shift its premises.

Measured on the 44 FOF problems of the seed-42/200 sample that the pipeline refutes, run as an explicit list
so no problem is missing from either side:

| | tree (before) | flat | flat + selective lowering |
|---|---|---|---|
| refuted | 44 | 44 | 44 |
| check | 30774 ms | 19431 ms (−37%) | **17811 ms (−42%)** |
| prover | 21599 ms | 21568 ms | 21037 ms (unchanged) |
| clausify | 2818 ms | 3301 ms (+17%) | **2424 ms (−14%)** |
| **total** | 55191 ms | 44300 ms (−20%) | **41272 ms (−25%)** |

The third column is the follow-up described below, applied. Repeat runs put `clausify` at 2424/2481 ms and
`prover` within 1.3% across all three configurations, so the differences are well outside the noise.

Proof shape, over five representative problems: checked steps (counting every `SCSubproof` *occurrence*, which
is what `SCProofChecker` walks) fall 40–66% — e.g. NLP117 5070 → 1729, SWB002+3 6204 → 3671 — while total
sequent entries are unchanged (48515 → 49887; 103524 → 103872). So the win is purely the removed re-checking,
and the lowered proof is no bigger. Per-problem `given` counts are identical either way, confirming the prover
receives the same clause set in the same order.

Flattening initially cost +17% in `clausify`, because it moves the derivation out of nested subproofs:
`lowerKernelProofWithAssumptions` handles a nested *closed* subproof shallowly (one appended `Weakening`)
while a top-level step goes through `mapStepPremises` + `rewriteStepBot` individually. Note the two shapes
are not combinable at the same node — sharing requires citing a parent step, a subproof citing parent steps
has imports, and a nested import-bearing subproof is exactly what the shallow lowering cannot handle (see the
restriction on `lowerKernelProofWithAssumptions`).

**Follow-up, applied.** `lowerClausificationProof` now pastes the assumptions only onto steps whose premise
cone actually reaches an import. Assumptions can enter nowhere else: external imports were given the
inherited ones, and each local assumption is materialised as a `Hypothesis(φ ⊢ φ)` prefix step. The
distribute derivation touches no import, so none of it is rewritten, and `Ψ` enters exactly where it should —
at the `Cut` against the hypothesis import, turning an assumption-free `φ ⊢ Cᵢ` into `Ψ ⊢ Cᵢ`.

A needing step may now have a non-needing premise, and the two compose because a step inherits `needs` from
its premises: the only way to be needing while a premise is not is for *another* premise to reach an import,
i.e. a multi-premise rule, and those take the union (or a subset test) of their premises' left sides. Single-
premise rules, where the kernel demands the left sides line up exactly, always agree with their premise by
construction. A trailing `Weakening` guards the degenerate case where the conclusion itself needs nothing,
since the parent matches it against `ClausificationSubproof.bot`.

This is not specific to distribution — every phase lowered under assumptions pays less — and it more than
repays the flattening cost: `clausify` ends up 14% *below* the original tree baseline, and `check` drops
further still (19431 → 17811 ms) because subproof interiors are no longer weakened either.

**A caution about how this was measured, which cost more than the fix.** The first comparison used the
sampled harness (`FofEvaluation 42 200 15000`) and showed refutations collapsing 44 → 20, reproducibly, with
25 problems lost and none gained. That verdict was an artifact — see §4.4, found while chasing it. Every one
of the 25 refutes in isolation, in milliseconds. Do not A/B a proof-construction change on a long sampled run.

### 4.2 ~~**[L]** Throwaway query clauses consume ids and arena~~ — FIXED 2026-08-08

[`Discount.scala:642`](Discount.scala), [`713-714`](Discount.scala), [`774`](Discount.scala) each build a
`bank.mkClause(...)` purely as an index query key — one per literal per call, on forward and backward
simplification. Each consumes a `clauseCounter` id, computes weight/`predBits`, and interns nothing
reusable. Clause ids are used for identity and lazy-deletion bookkeeping, so inflating them is not free of
consequence (`IntOpenHashSet` sizing, `activeIndex` key spread). A query-only path taking
`(Array[Literal], posCount, negCount, predBits)` would avoid minting a `Clause`.

**Fix.** The three sites (now in [`Simplifier.scala`](Simplifier.scala) after §3.2) call
`TermBank.mkQueryClause`, which shares `mkClause`'s field computation but draws no id from `clauseCounter`:
every query clause carries `Core.QueryClauseId`, a negative shared sentinel. The suggested tuple-taking path
was not worth it — the trie and `Subsumption.subsumes` both want a `Clause`, so it would have meant a parallel
retrieval API for one allocation.

The sentinel is what makes this safe to get wrong loudly rather than quietly: a shared id would alias in
anything keyed by it, so `Clause.isQuery` names the condition and `ActiveSet.add` / `PassiveSet.enqueue`
`require` against it. Verified no query clause's id is read anywhere today — the `seen`/`sorted`/`!=`
comparisons in `Simplifier` are all on the *retrieved* clause, never the query.

### 4.3 ~~**[L]** Small allocations on gate paths~~ — FIXED 2026-08-08, *no measurable effect*

- `Demodulation.matcherIsRenaming` ([`Demodulation.scala:203-205`](Demodulation.scala)) does
  `lhsVars.map(...)` then `images.distinct` — two arrays per redundancy-gate evaluation. For the tiny arrays
  involved a double loop is both faster and allocation-free.
- `Discount.removeDemodulatorsOf` ([`945-948`](Discount.scala)) re-derives the rules (recomputing `orient`,
  `varsOf`) just to locate them for removal. Storing the rules on activation would avoid it.
- `Clausification.checkInterrupted` ([`Clausification.scala:252-258`](../clausification/Clausification.scala))
  calls `Runtime.getRuntime.totalMemory/freeMemory` on *every* invocation — it is called per axiom, per
  naming step, per distribute step. Polling the heap every ~1000 calls would be equally safe.

**Fix, all three.**

- `matcherIsRenaming` computes each image once into one array and compares against its predecessors, exiting
  at the first witness. *Not* the recommended double loop recomputing images: `Applier.apply` allocates a
  tuple key per call, so recomputation would have traded one array for more garbage. The win over the
  original is dropping `.map`/`.forall`/`.distinct` — `distinct` boxed every element, `Term` being an opaque
  `Int` — and `n == 1`, the common case, now allocates nothing.
- `ActiveSet` records the rules it inserted into the discrimination tree (`treeRulesOf`) and removes exactly
  those. The speed is incidental; the point is that re-derivation called `order.orient`, so it reproduced the
  inserted rules only while the ordering was unchanged since activation — true today, and now not relied on.
- `checkInterrupted` polls the heap every 256th call instead of every call, with `maxMemory` hoisted and the
  native calls moved out of line. The interrupt flag is still read every call.

**Measured: no detectable difference**, on the 44-problem FOF list. Honest caveats, both of which mean this
is weaker evidence than it looks:

1. The machine drifted ~40% slower partway through the session (prover total on an unchanged workload went
   21000 → 30000 ms). Caught by re-running with the change reverted — clausify 3818 vs 3673/3753, prover
   30192 vs 29999/31371, check 24796 vs 25607/26236, i.e. identical. Absolute numbers from before that point
   are not comparable to ones after it.
2. That list is the equality-**free** corpus, so demodulation barely fires and the gate paths the first two
   items touch are hardly exercised. The equality-bearing set would be the right instrument; that A/B was
   not run.

So these stand as structural improvements — strictly fewer allocations, and a removal that no longer depends
on an unstated invariant — not as a measured speedup. Same outcome as §1.6; at [L], that is the expected one.

### 4.4 ~~**[H]** `BenchUtil.withTimeout` abandons a timed-out worker, poisoning the rest of the run~~ — FIXED 2026-08-08

Found while measuring §4.1, and it invalidates measurements rather than slowing code — hence [H].

[`BenchUtil.withTimeout`](BenchUtil.scala) starts a daemon thread, `join(ms)`s it, interrupts it if it is
still alive, and **returns immediately without joining again**. Interruption here is cooperative — the prover
polls a deadline, `checkInterrupted` polls a flag — so a thread deep in a tight loop with a multi-million
clause passive set does not stop on request. The harness records `HARD_TIMEOUT` and starts the next problem
while the runaway thread keeps running and allocating, for the remainder of the run.

The effect is not subtle. In a seed-42/200 `FofEvaluation` run, position 22 (`LCL666+1.010.p`) hard-timed
out; from position 26 onward essentially *every* problem reported `TIMEOUT`, including ones that refute in
under 10 ms standalone (`MGT022+1.p`: 6 ms). Repeated runs of the *same* binary on the *same* sample scored
19, 20, 20, 21 and 28 refutations — a 47% spread — because the outcome depends on when the first runaway
starts. This is compounded by `checkInterrupted`'s 90%-of-max-heap trip wire (§4.3), which is global and
counts uncollected garbage, so one problem's residue aborts another's clausification.

Consequences, in order of importance:

1. **Any A/B run through this harness on a sample containing a hard-timeout problem is unreliable.** §4.1 was
   nearly reverted on its verdict. Prefer an explicit `files` list of problems that terminate; compare
   `check`/`prover`/`clausify` totals over a set both sides refute.
2. The ablations recorded elsewhere in this session (subsumption-resolution on/off, `gen`/`nogen`,
   condensation) used the same instrument and should be treated as provisional until re-run this way.
3. `hard_timeout` should be reported as *contaminating* the run, not as one problem's verdict.

Two fixes, both cheap: join with a grace period after interrupting and report how many workers survived, and
make the summary state loudly that results after a surviving worker are suspect. Neither restores a lost run,
but both stop a silent one.

**Fix.** `withTimeout` now interrupts, then joins for a 2 s grace period, so the common case — a solver that
notices at its next poll — really has finished before the caller moves on. A worker still alive after that
cannot be stopped (`Thread.stop` is gone, and was unsafe when it existed), so it is counted in
`BenchUtil.abandonedWorkers`. Every harness resets the count when it prints its header and reports it at the
end: `FofHarness` marks each row that ran after the first abandonment with `!` and says how many there were,
`Evaluation` prints the warning under its summary, `StrategyEvaluation` resets *per strategy* (a worker
abandoned under one strategy penalises the ones after it — precisely the comparison that harness exists to
make) and tags the affected summary line, and `BaselineBench` emits `# CONTAMINATED=n` so it survives the TSV
being piped into a plotting script.

One trap worth recording, because it would have been a silent regression: joining after the interrupt means a
*cooperative* worker now finishes during the grace period and stores its `Failure(InterruptedException)` in
the result box. Returning that would have reclassified every `HARD_TIMEOUT` as `ERROR(InterruptedException)`
across all four harnesses. `withTimeout` therefore returns `None` unconditionally once the budget is
exceeded: the overrun is the verdict, and the exception is merely how the worker was stopped.

`BenchUtilTest` pins the contract — a worker that respects its interrupt times out but is *not* counted,
one that ignores it is; both return `None`, so the count is the only thing that distinguishes them; and an
interrupted worker's own exception does not leak out as a result.

Verified on both sides. The seed-42/200 sample that exposed this reports `!! 6 workers ignored the interrupt`
and marks 172 of 200 rows; the 44-problem explicit list runs clean, with no warning and no marks.

**Second fix: process isolation, which removes the problem rather than reporting it.** Detection was only ever
a mitigation — an abandoned worker still held its heap. `BenchUtil.runForked` runs a problem in a fresh JVM
(same java binary, classpath and `-Xmx`), waits `timeoutMs + 5000`, and `destroyForcibly`s it otherwise. The
child prints one tab-separated `RESULT` line; a child that printed none was killed or died on a fatal error.
That makes the budget a real guarantee, kills the shared-heap coupling (including
`Clausification.checkInterrupted`'s JVM-global ceiling aborting an unrelated problem), and drops the
cross-problem carry-over of static state and GC ergonomics.

`FofHarness` (so `FofEvaluation`/`EqFofEvaluation`) and `Evaluation` run this way; both keep the in-process
path behind `LISA_FORK=0`, and print which is in force. `StrategyEvaluation` and `BaselineBench` still use the
thread path — the abandonment counter above is what protects them, and converting them is a follow-up.

**The cost, which is why the mode is in the banner.** Forking pays a JVM start-up and full JIT warm-up per
problem. Verdicts are unaffected — the 44-problem list refutes 44/44 either way — but per-problem *timings*
inflate badly on fast problems: median `clausify` 10.4 → 146.9 ms, median `prover` 3.8 → 106.4 ms, totals
2345 → 9144 and 21437 → 28107 ms. So: **fork for verdicts, `LISA_FORK=0` for timings**, and never compare
timings across the two. The §4.1 table was measured in-process and should stay that way.

Verified on the seed-42/200 sample that exposed the finding: **no contamination reported, no marked rows**,
because nothing can be abandoned — `LCL666+1.010.p`, the problem whose survival poisoned the earlier runs, is
now simply killed and recorded as `HARD_TIMEOUT`. The same sample scored 19/20/20/21/28 refutations while
contaminated; it now scores **138 of 196 attempted**, the first figure in this sequence produced by an
instrument that cannot be poisoned. It is not attributable to any one code change, since the instrument
changed alongside the prover — it is a new baseline, not a delta.

One unexplained side-effect worth recording rather than papering over: `parse_err` fell from 5 to 3 on the
same sample. The likely cause is that a forked child parses on the JVM's *main* thread, whose default stack is
larger than that of the `new Thread(...)` worker the in-process path used, so a few deeply-nested `LCL`
formulas that used to `StackOverflowError` now parse. Plausible and consistent with §4.5, but not verified.

This does not subsume §4.5. A `StackOverflowError` that the child *catches* leaves the child alive to report,
so it still arrives as `BAD_PROOF`; only failures that kill the JVM are reclassified. Splitting the category
remains its own fix.

The provisional ablations listed above still need re-running — now with a real guarantee behind the numbers
rather than a warning.

### 4.5 **[M]** `Trail.Applier.apply` recurses on term depth and overflows the stack — reported as `BAD_PROOF`

Found 2026-08-08 by following up a `bad_proof=1` in a corpus run. **It is not an invalid proof**, which is
half the finding: the category is misreported.

`SYN986+1.005.p` comes back `BAD_PROOF`. It reproduces standalone (no contamination, no timeout pressure), so
it is a real defect and not a measurement artifact. What actually happens is a `StackOverflowError`, thrown
in *both* the certified and uncertified pipelines — so it lives in the shared prover path, not in
clausification. The top 400 stack frames contain exactly **two distinct** frames:

```
Core$Trail$Applier.apply:837
Core$Trail$Applier.apply:849
```

[`Applier.apply`](Core.scala) ([836-851](Core.scala)) walks a term structurally, recursing once per level
(`out(i) = apply(bank.arg(dt, i), ds)`), with no depth bound and no iterative fallback. Its `memo` makes
*shared* subterms cheap but does nothing for *depth*. Instantiate a deep enough term — the parameterised
`SYN986+1.00N` family grows exactly this way — and the JVM stack runs out. Related, and evidence that deep
inputs are normal in this corpus rather than exotic: the TPTP parser itself `StackOverflowError`s on several
`LCL` problems (`parse_err=5` in the same run), and `FofHarness` already catches `Throwable` at the parse
site for that reason.

Two things to fix, and the second matters more than the first:

1. **The crash.** `Applier.apply` should be depth-safe — an explicit work stack, or a depth counter that
   fails cleanly with a diagnosable error instead of a `StackOverflowError`. It is worth checking the other
   structural walks for the same shape (`Demodulation.varsOf`, `Superposition.foreachSubterm`, `Bridge.term`)
   before concluding this is one site rather than a class.
2. **The category.** `BAD_PROOF` currently means two unrelated things — *the kernel rejected the proof we
   built*, which is a soundness-grade signal, and *the prover threw*, which is a robustness bug — because
   [`FofHarness`](FofHarness.scala) maps its catch-all `ProverError` and a failed `checkSCProof` to the same
   string. The only way to tell them apart in a summary is that a crash leaves `checkMs == 0.0`, which is
   accidental rather than designed. That is exactly how this one was misread as an invalid proof. They should
   be separate categories (`BAD_PROOF` vs `PROVER_CRASH`), so that a genuine kernel rejection can never hide
   behind a crash count — nor a crash raise a false soundness alarm.

---

## 5. Dead, test-only, and misplaced code

### 5.1 ~~**[M]** Test-support API living in production sources~~ — FIXED 2026-08-09, *list partly stale*

The following exist solely to support tests, but are public members of main-source objects:

- [`Order.compareClause`](Order.scala), `maximalSide`, `isStrictlyMaximal` — no production caller;
  `compareClause`'s doc even claims callers that don't exist (§2).
- [`KBO.checkAdmissibility`](KBO.scala) — only `KBOTest`. Notable because `WeightScheme` and
  `PrecedenceScheme` are user-selectable via `Strategy`, so admissibility (hence *termination* of
  rewriting) is a real runtime property that is never actually validated at runtime. Either call it once in
  `Bridge.solve` behind a debug flag, or accept that it is a test oracle and say so.
- [`FastClausify.skolemizeForTest`](../clausification/FastClausify.scala), `namedNnfSkolem`;
  [`CertifiedFastClausifier.namedFormula`](../clausification/CertifiedFastClausifier.scala), `skolemizeEps`,
  `stripForall`, `namedNnfSkolemEps`, `fastNamedNnfSkolem`, `sameNaming` — eight members whose only consumer
  is `CertifiedFastEquivalenceTest`. `fastNamedNnfSkolem`'s own doc admits it is "routed here so the
  package-private `FastClausify` is reachable from the equivalence test". A name ending `ForTest` in a
  production object is the clearest possible signal of a layering problem.
- [`PrenexPhase.provePrenexDeconstruct`](../clausification/PrenexPhase.scala) and the `forceDeconstruct` /
  `forceRewrite` parameters threaded through `certifyPrenex` and `provePrenex` — test-only strategy
  overrides in the production signature.
- [`Discount.factorAfterCheck`](Discount.scala) + `keptMaximal` — one test.

**Recommendation:** make the test package a friend (`private[automation]`) and drop the `ForTest` suffixes,
or move the oracles into the tests. Either is better than the current state, where a reader cannot tell
which of `CertifiedFastClausifier`'s eleven public members are the API.

**Fix.** `private[automation]` throughout, which the test packages can see and the library's public API cannot.
Applied to `Order.maximalSide`/`isStrictlyMaximal`/`compareClause`, `KBO.checkAdmissibility`,
`FastClausify.namedFormula`/`namedNnfSkolem`, and the six `CertifiedFastClausifier` members, the last
gathered under one banner naming the test that consumes them. `skolemizeForTest` was renamed `skolemizeNnf`:
it has a real internal caller (`namedNnfSkolem`), so the suffix was not merely ugly, it was false. The
`automation` scope rather than the tighter `clausification` is forced by the equivalence test living in the
`superposition` test package — §6.3 would let this tighten.

`KBO.checkAdmissibility` is now labelled a test oracle *and* the gap is stated where a reader will hit it:
`WeightScheme`/`PrecedenceScheme` are user-selectable through `Strategy`, so admissibility — hence
termination of rewriting — is a property of a runtime configuration that nothing validates at runtime.
Calling it from `Bridge.solve` behind a debug flag would close that, and has not been done.

**Two entries were stale, and checking beat trusting the list:**

- **`PrenexPhase.provePrenexDeconstruct` is not test-only** — it is the default strategy, called from
  `provePrenex`. It (and `provePrenexRewrite`) are now `private`. Of the two "test-only" parameters, only
  `forceRewrite` is used by a test; `forceDeconstruct` was set by *nobody*, so it is deleted, along with both
  parameters on `certifyPrenex`, whose single caller passed neither. A knob no caller uses is not a knob known
  to work.
- **`Discount.factorAfterCheck` is no longer test-only.** §3.1 moved it into `SearchOptions` and made
  `Bridge.solve` forward the whole options object, so a production caller can set it. `keptMaximal` was
  already `private`. Nothing to do; the finding was overtaken by §3.1.

### 5.2 ~~**[M]** `RenamingBugDemo.scala` is a debug `main` in production sources~~ — FIXED 2026-08-09

[`RenamingBugDemo.scala`](../clausification/RenamingBugDemo.scala) is a runnable reproduction of a bug that
is now fixed and covered by `ScreenPhaseTest`. It compiles into the library jar. Its narrative value is
real — it explains a subtle failure mode better than the test does — but that value belongs in a test file's
Scaladoc or in the JOURNAL, not in `main`.

**Fix.** Deleted, after moving the two things it said that `ScreenPhaseTest` did not:

- **Why no corpus run ever caught this.** TPTP predicates and functions arrive as *constants*, and the
  pipeline never instantiates a constant, so the bug is unreachable on the whole benchmark set. It needs a
  free *variable* at a schema's sort — which essentially every Lisa goal has and no TPTP problem does. The
  tactic was failing in a way the 944-problem FOF corpus could not express. That is worth keeping: it says
  what the corpus does *not* cover.
- **Why the screening sits above `NegatedPhase`.** Its predecessor renamed from *inside* the assumption
  region, which reintroduced the fault it was meant to avoid — renaming a predicate variable free in the
  negated-conjecture assumption is itself an `InstSchema` under that assumption.

The demo's first trigger (the old `RenamePhase` renaming a non-colliding predicate variable) is not carried
over as a test: it was a property of a design that no longer exists, so there is nothing left to regress.
Its second trigger is already `ScreenPhaseTest`'s `P` case.

### 5.3 ~~**[L]** `Discount` flags that are never exercised together~~ — SKIPPED 2026-08-09, *mostly stale*

`superposition`, `forwardDemodulation`, `backwardDemodulation`, `subsumptionIndexing`,
`demodulationIndexing`, `forwardUnitDeletionIndexThreshold` are constructor flags not reachable from
`Bridge.solve` (which does not forward them). They are settable only by directly constructing `Discount` —
i.e. only from tests. That is defensible for A/B knobs, but it should be stated, because the current reading
is "these are configuration" when in fact `Bridge` hard-codes them.

**The reachability claim is stale**, overtaken by §3.1: all six are now `SearchOptions` fields, and
`Bridge.solve` passes the options object through to `new Discount` whole. A production caller can set them.

What survives is the *title*, not the body: no `Strategy` in the portfolio varies any of the six, and the
tests toggle each alone (`subsumptionIndexing` and `forwardUnitDeletionIndexThreshold` in `DiscountTest`,
`demodulationIndexing` and the three equality switches in `EqualitySaturationTest`), never in combination.
That is the right shape of test for what these are — five of the six are *differential* switches selecting an
indexed retrieval path over a linear scan, and the property that matters is that both reach the same verdict,
which is exactly what those tests assert. Combination coverage would test the indices' mutual independence,
which nothing suggests is at risk.

Skipped by decision: the residue is one or two sentences of Scaladoc marking the A/B group as knobs the
shipped portfolio never moves, distinguishing them from real tuning like `condensation`.

---

## 6. File and documentation organisation

### 6.1 **[H]** Non-source files in the source tree — *`.txt` FIXED 2026-08-09, `.md` outstanding*

`src/main/scala/lisa/automation/superposition/` contains:

- **208 KB of `.txt`** problem lists (`tptp-fof-fo-eq-thm.txt` alone is 140 KB),
- **4 287 lines of `.md`** across 18 files.

Both are packaged into the jar by sbt's default resource handling of non-Scala files under a source
directory, and `BenchUtil.locateList` compensates with hard-coded relative paths
([`BenchUtil.scala:45-53`](BenchUtil.scala)) that guess at the working directory:

```scala
s"lisa-sets/src/main/scala/lisa/automation/superposition/$listFileName",
s"src/main/scala/lisa/automation/superposition/$listFileName",
```

**Recommendation:** `.txt` → `src/test/resources/` (they are benchmark data, used only by harnesses) and
loaded via `getResourceAsStream`, which deletes the path-guessing entirely. `.md` → a `docs/superposition/`
directory at the repo root, or at minimum a `doc/` subdirectory.

**Fix (`.txt`).** Moved to `lisa-sets/src/main/resources/lisa/automation/superposition/` and loaded with
`getResourceAsStream`; `BenchUtil.locateList` is deleted outright, since with a classpath resource there is
nothing left to locate. The `$TPTP_*_LIST` env-var overrides still take precedence, so a hand-made list (a
regression subset, say) needs no rebuild.

**Not `src/test/resources` as recommended** — that would have broken the harnesses. They are `main` objects
launched with `runMain`, and test resources are not on the compile runtime classpath, so the lists would have
become unreachable. `main/resources` is also what makes them reachable from a *forked child JVM* (§4.4),
whose working directory is not the repo root — the old relative-path search would have failed there, which
is a good illustration of why the guessing had to go rather than be extended again.

**`.md` outstanding.** The 18 documents have been moved to an `archive/` subdirectory, which is tidier but
still inside `src/main/scala/`, so they are still packaged. Moving them out of the source tree, and §6.2's
index, remain.

### 6.2 **[M]** The markdown corpus needs a table of contents and a lifecycle

Eighteen documents with no index. They serve at least four distinct purposes, currently indistinguishable
by filename:

| Kind | Files | Status |
|---|---|---|
| Living plan | `PLAN.md` | Stale (§2) |
| Phase design (historical) | `Phase0-5.md` | Superseded by the code; `Phase1.md` is 9 lines and wrong |
| Research surveys | `Phase4Research.md`, `Phase5{Demodulation,Subsumption}Research.md`, `PortfolioStrategy.md`, `ProverHeuristics.md` | Durable reference — the most valuable of the set |
| Results / backlog | `Benchmarks.md`, `BaselineVsE.md`, `PossibleOptimizations.md`, `KBOderef.md` | Living |

A reader arriving today cannot tell that `Phase2.md` is history while `PossibleOptimizations.md` is a live
backlog. **Recommendation:** a `README.md` index with one line per document and an explicit
`Status: historical | living | reference` header in each. Fold `Phase1.md` into `Phase2.md`.

### 6.3 ~~**[M]** Clausification is tested from the superposition test package~~ — FIXED 2026-08-09

`lisa-sets/src/test/scala/lisa/automation/clausification/` holds three files. But the substantive
clausification tests live *next door*: `ClausalTest` (421 lines, over half of it exercising
`certifyClausal`: free-variable conjectures, name collisions, ε-terms, boolean constants, naming, Skolem
binder collisions) and `CertifiedFastEquivalenceTest` (155 lines, entirely about `FastClausify` vs
`CertifiedFastClausifier`).

Consequence: 13 clausification sources have 3 test files in their own package, and someone running
`testOnly lisa.automation.clausification.*` gets a fraction of the real coverage. `NnfPhase`,
`DistributePhase`, `SkolemPhase`, `NamingSupport`, and `ProofIR` have no test file bearing their name at all.

**Recommendation:** move the clausification-focused tests into the clausification test package, and add
per-phase unit tests for the five untested modules. The lowering logic in `ProofIR` in particular — the
assumption-threading that produced this session's bug — has no direct test.

**Fix.** `CertifiedFastEquivalenceTest` moved wholesale, and `ClausalTest` was split: 16 of its 26 tests were
about the clausifier and became `clausification/CertifiedClausificationTest`. What stayed is what genuinely
belongs to `Clausal` — ε-abstraction, clause-slot composition, the prover-contract probe, and the harnesses'
seeded sampling. `testOnly lisa.automation.clausification.*` now runs **6 suites / 34 tests**, against 4
suites and a fraction of the coverage before.

Moving the equivalence test also let §5.1's visibility tighten from `private[automation]` to
`private[clausification]` on all nine oracles, which was the reason that entry had to settle for the looser
scope.

**Partly outstanding: the per-phase tests.** `ProofIR` now has `ProofIRTest` (added for §1.3 and extended for
§4.1's selective threading — the assumption-threading logic this entry singles out). `NnfPhase`,
`DistributePhase`, `SkolemPhase` and `NamingSupport` still have no test file of their own; they are covered
only end-to-end, which is why §4.1's step-count regression had to be measured with a throwaway probe rather
than asserted.

---

## 7. The test suite

### What is done well — keep doing it

- **A/B equivalence testing of every index.** `DiscountTest` (487 lines) checks that indexed and scanned
  retrieval reach the same *verdict* across curated clause sets, for five index paths independently:
  resolution, feature-vector subsumption, `{¬K}` unit-deletion dispatch, backward SR sign-flip, forward SR
  char-2. This is exactly the right invariant for index work (the index is a filter, so the *verdict* must
  be identical while ids and trajectory need not be) and it is the strongest thing in the suite.
- **Ablation symmetry.** Every simplification is tested on *and* off, with the counters asserted at zero
  when off. That catches the classic "flag does nothing" and "flag fires when disabled" bugs.
- **A generic oracle for a specialised implementation.** `Order.termMultisetCompare` is kept
  package-visible purely so the specialised 2-element `compareSamePolarity`/`compareDiffPolarity` can be
  property-checked against the generic multiset extension. That is the right pattern for hand-optimised
  comparison code.
- **The `Sorry`-stub technique** in `ScreenPhaseTest` — stubbing the prover so a failure can only come from
  the certification scaffolding — isolates the layer under test cleanly.

### Gaps, in rough order of value

1. **[H] No randomised/differential test of proof reconstruction.** Full proof reconstruction is the
   project's headline promise, and it is tested only on hand-written examples plus TPTP runs that are
   *canceled* without a local corpus. A generator producing random small clause sets, running the prover,
   and asserting `refuted ⇒ kernel-valid proof concluding ⊢` would exercise the `Justification` replay
   machinery (`replaySurvivors`, applier ordering, `flipEqRight`, hole positions) far harder than any
   curated case. The applier-order replay in `Reconstruction` — which must reproduce the *exact* variable
   numbering the generating code produced — is precisely the kind of code that fails on inputs nobody
   thought of.
2. ~~**[H] 41 of 446 tests silently cancel**~~ — **WARNING ADDED 2026-08-09.** Without a TPTP checkout, ~40
   tests are `assume`d away, including the entire `CertifiedFastEquivalenceTest` and `SynBaselineTest`. A
   green run therefore means much less than it appears to.
   *(2026-08-08: the corpus turned out to be present at `C:\Users\Simon\Work\TPTP-v9.2.1`; with `TPTP` set,
   the suite runs 0 canceled, all passing. So the tests are healthy — the problem is purely that the default
   local run hides them behind an unset environment variable and still reports "All tests passed".)*

   **Fix.** The corpus lookup is now one place, `TptpCorpus`, and the first test to ask for a corpus that is
   not there prints a framed banner saying the corpus-backed tests are being cancelled, that "All tests
   passed" means "all tests that ran", and how to set the variable. On stdout, not stderr: sbt's test output
   is stdout, so a stderr warning can land out of order in a redirected log, and PowerShell turns any
   native-command stderr into a `NativeCommandError` that makes a passing run look failed.

   *A warning only, by decision.* Failing instead would make the suite unrunnable without a multi-gigabyte
   download — the trade the `assume` was making deliberately. This stops the trade being silent, nothing
   more. Vendoring small `.p` files for unconditional coverage remains open, though `CascProverTest` (below)
   now writes its own problems and so needs no corpus at all.
3. **[M] Untested modules** — *`CascProver` DONE 2026-08-09.* Remaining: `Strategy`/`portfolio`,
   `Clausal.distinctObjectAxioms`, `Clausal.cascSetup`, `BenchUtil`, `NnfPhase`, `DistributePhase`,
   `SkolemPhase`. (`ProofIR` lowering gained `ProofIRTest`; `BenchUtil`'s timeout half gained `BenchUtilTest`
   under §4.4.)

   **Fix (`CascProver`).** `CascProverTest`, 9 tests, black-box: every member of `CascProver` is `private`
   and should stay so — its contract is the *text it prints*, which a competition harness parses, not a Scala
   API. Each test writes a small problem, runs `main` with stdout captured, and checks the output. Covered:
   the three SZS verdicts (`Unsatisfiable` without a conjecture, `Theorem` with one, `GaveUp` on a
   saturation — never `Satisfiable`, since an incomplete search must not claim it), `Error` on an unparsable
   input, the delimited refutation block ending in `$false`, distinct objects surviving the parser's
   `$d`/`$s` mangling round trip, and unknown-flag tolerance.

   The sharpest assertion is that the emitted derivation **re-parses**: a proof a harness cannot read is
   worthless however correct the search was. Worth recording how that assertion was got right — the first
   version used `annotatedStatementToKernel` and failed, which looked like a defect in the printer. It was
   the test: that entry point is `fof`-only and the clauses are correctly emitted as `cnf(...)` with
   `inference(...)` records. Re-parsing the block *as a problem file* is both the assertion that passes and
   the one that matches what a harness actually does.

   Not covered, deliberately: the two argument-error paths call `sys.exit(2)`, which would take the test JVM
   with them.
4. **[M] No proof-size regression guard.** Asserting `proof.steps.size` stays under a bound for a few
   representative problems would catch a blow-up. Now worth more than when first written: measuring §4.1
   needed a one-off probe counting steps recursively through every `SCSubproof` occurrence, and that number
   (5070 → 1729 on NLP117) was the one that actually settled the question, after two wrong hypotheses drawn
   from timings. It belongs in the suite, not in a scratch file.
5. ~~**[L] No adversarial input tests**~~ — **DONE 2026-08-09.** The clausifier is dense with `require`s and
   none was tested: malformed sequents, a non-NNF matrix reaching `DistributePhase`, a hypothesis with a
   non-empty LHS. An untested `require` is a comment with a runtime cost — it may already be unreachable, it
   may fire on inputs it was never meant to catch, and nothing notices if a refactor deletes it.

   **Fix.** `AdversarialInputTest`, 14 tests, in four groups:

   - **Malformed input sequents** — non-empty LHS, two right formulas, no right formula, and the same on the
     conjecture. These are the shapes an outside caller can actually hand in, so they are the ones worth
     catching by name.
   - **The prover contract.** `certifyClausal` documents what the prover it is given must return, and that
     prover is the one part of the pipeline a *caller* supplies — so it is the likeliest external fault. A
     prover that declares only the clauses its refutation used (the tempting mistake) and one that invents an
     extra import are both caught at the boundary rather than surfacing later as an unexplained invalid proof.
   - **Phase-ordering invariants** — `certifyDistribute`/`certifySkolem`/`certifyPrenex` rejecting a problem
     that still carries a conjecture, and a `⟹`/`⇔`/`∀`/`∃` reaching the distribution phase. Without the leaf
     check the last falls through to the literal case and becomes a one-literal "clause" whose literal is a
     whole implication: a wrong clause set, failing far from the cause.
   - **`ProofIR` construction invariants** — the assumption/premise split, index range, distinctness, and the
     empty-proof check.

   Each negative group has a **positive control** asserting the same path accepts good input, so a check that
   started rejecting everything could not make the suite pass for the wrong reason. That earned its keep
   immediately: the control caught my own test bug — a prover handed to a *phase* must declare `libImports`
   too, which only `certifyClausal`'s wrapper adds. Messages are matched loosely, since what is being pinned
   is a clean `IllegalArgumentException` at the right boundary, not the wording.

   *(`ProofIRTest` had already covered the `lowerKernelProofWithAssumptions` precondition and §4.1's selective
   assumption threading, 2026-08-08.)*

---

## 8. Prioritised actions

**Do first — cheap, and each removes a real hazard**

1. ~~Self-invalidating `orientCache` (§1.1)~~ — **done 2026-08-08.**
2. ~~Narrow the tactic's catch-all (§1.2)~~ — **declined**, the message already distinguishes the cases.
3. ~~Fix or delete the "NOT kernel-valid" comment in `ProofIR` (§1.3)~~ — **done 2026-08-08**, now an
   enforced `require` + `ProofIRTest`.
4. ~~The stale-comment sweep (§2)~~ — **done 2026-08-08**, plus two stale flag rationales found en route.

**Do next — contained refactors with compounding payoff**

5. ~~`SearchOptions` case class collapsing the four-layer knob chain (§3.1)~~ — **done 2026-08-08**; killed the positional-boolean
   hazard and the dropped-knob asymmetry.
6. Move `.txt` to test resources and `.md` to a docs directory; add the doc index (§6.1, §6.2).
7. Extract the shared test fixture (§3.4) and move the clausification tests into their own package (§6.3).

**Then — larger, but the right direction**

8. ~~Split `ActiveSet` and `Simplifier` out of `Discount` (§3.2)~~ — **done 2026-08-08** (`PassiveSet`,
   `ActiveSet`, `Simplifier`; `Discount` 920 → 391 lines).
9. Add the randomised reconstruction test (§7.1) — highest-value missing coverage.
10. Relocate the test-only API out of production objects (§5.1), and `RenamingBugDemo` into the tests (§5.2).

---

*Note on placement: this document is itself an `.md` file inside `src/main/scala/`, which §6.1 argues
against. It is here because that is where the project's documents currently live and where the review's
scope permits writing; it should move with the rest of them.*
