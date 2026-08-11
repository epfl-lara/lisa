# Benchmark results

Performance/soundness baselines for the superposition prover, produced by [`Evaluation`](Evaluation.scala).
Each entry is a fixed, reproducible run so later phases can be compared against it directly.

## How to reproduce

```
TPTP=/path/to/TPTP-v9.2.1 sbt "lisa-sets/runMain lisa.automation.superposition.Evaluation [seed] [n] [timeoutMs] [maxGiven]"
```

The benchmark draws a seeded random sample from [`tptp-clausal-fo-noeq-uns.txt`](tptp-clausal-fo-noeq-uns.txt)
— 1651 TPTP problems that are **clausal (CNF), first-order, equality-free, and unsatisfiable**
(`CNF_UNS_*_NEQ*`, every one `Status: Unsatisfiable`). Every refutation is reconstructed and run
through the Lisa kernel checker (reusing the solve — no re-proving), so the run is soundness-checked
end to end.

Because the whole list is unsatisfiable, there are two ways the prover can be *wrong*, and both must
stay at **0**:
- `saturated` — claiming a known-unsat set is satisfiable.
- `bad_proof` — a refutation whose reconstruction is not a kernel-valid proof of the empty sequent `⊢`.

`REFUTED` vs `TIMEOUT` is then the clean "did we prove it within budget?" throughput axis.

---

## Phase 1 baseline — seed 42 (2026-06-25)

End of Phase 1: DISCOUNT loop, ordered resolution + positive factoring, full kernel reconstruction.
No simplification (subsumption/demodulation) and no term indexing yet (Phases 2 and 4).

**Config:** `seed=42`, `n=100`, `timeoutMs=15000`, `maxGiven=100000`. Wall time 16:43.

**Summary:**
```
refuted=35   timeout=65   saturated=0   bad_proof=0   hard_timeout=0   error=0   parse_err=0   (of 100)
refute time: total=15184 ms   avg=433 ms
```

| Outcome | Count |
|---|---:|
| REFUTED (kernel-certified) | 35 |
| TIMEOUT (budget hit) | 65 |
| SATURATED | 0 |
| BAD_PROOF | 0 |
| HARD_TIMEOUT / ERROR / PARSE_ERR | 0 / 0 / 0 |

**Observations:**
- **Fully sound:** `saturated=0` and `bad_proof=0` — every one of the 35 refutations reconstructed
  into a kernel-valid proof of `⊢`, and nothing claimed a known-unsat set satisfiable.
- **35/100 solved** within 15 s. The 65 timeouts are the population where Phase-2 simplification
  should help most.
- Refutations are mostly **instant** (~24 of 35 in ≤2 ms; median ~0–1 ms). The `avg=433 ms` is
  tail-skewed by two problems: `SYN231-1` (10 627 ms — a single self-resolving `CNF_UNS_EPR_NEQ_HRN`
  clause; would have timed out under a 10 s budget) and `SYN705-1` (4 356 ms). Those two are 14 983 of
  the 15 184 ms total; the other 33 refutations sum to ~200 ms.

**Use as the Phase-2 yardstick:** re-running this exact `seed=42` (same list, 15 s, 100k) after adding
simplification gives a directly comparable `refuted`/`timeout` split — and `bad_proof`/`saturated`
must remain 0 (any optimization that breaks soundness shows up immediately).

---

## Phase 2 (partial) — forward + backward subsumption — seed 42 (2026-06-25)

Adds θ-**subsumption** to the Phase-1 loop: forward (discard a new/selected clause subsumed by an
active clause) and backward (delete active clauses subsumed by the given), both against the active set
only, with the cheap signature pre-filter, unit/`□` fast paths, and Check-1 per-literal weight skip
(`Subsumption.scala`). Still no demodulation (Phase 3) and no term indexing (Phase 4); the active set is
still scanned linearly. Subsumption deletion needs no reconstruction, so the kernel-certification path
is unchanged.

**Config:** identical to the Phase-1 baseline — `seed=42`, `n=100`, `timeoutMs=15000`, `maxGiven=100000`.
Wall time 8:58.

**Summary:**
```
refuted=66   timeout=34   saturated=0   bad_proof=0   hard_timeout=0   error=0   parse_err=0   (of 100)
refute time: total=19686 ms   avg=298 ms
```

| Outcome | Phase 1 | Phase 2 |
|---|---:|---:|
| REFUTED (kernel-certified) | 35 | **66** |
| TIMEOUT (budget hit) | 65 | 34 |
| SATURATED | 0 | 0 |
| BAD_PROOF | 0 | 0 |
| HARD_TIMEOUT / ERROR / PARSE_ERR | 0 / 0 / 0 | 0 / 0 / 0 |

**Observations:**
- **+31 problems (35 → 66, ~89% more) on the same budget** — subsumption prunes the redundant-clause
  explosion that caused most Phase-1 timeouts, exactly the predicted win.
- **Still fully sound:** `saturated=0` and `bad_proof=0` — subsumption changed only *which* clauses are
  kept, never a SAT/UNSAT verdict, and every refutation reconstructed to a kernel-valid proof of `⊢`.
- The 34 remaining timeouts are the harder population (large EPR non-Horn problems, deep `FLD`/`GRP`
  families) where term indexing (Phase 4) and equality handling (Phase 3) are the next levers.

### Ablation: forward vs. backward (same seed 42 / n=100 / 15 s / 100k)

Run via the `subs` mode of the `Evaluation` main (`both` | `fwd` | `bwd` | `none`), e.g.
`Evaluation 42 100 15000 100000 fwd`. Every refutation is still kernel-certified, so `bad_proof` /
`saturated` stay 0 in all four configurations.

| Config | REFUTED | TIMEOUT | SATURATED | BAD_PROOF | refute total | refute avg |
|---|---:|---:|---:|---:|---:|---:|
| `none` (Phase-1 baseline) | 35 | 65 | 0 | 0 | 15184 ms | 433 ms |
| `bwd` (backward only) | 46 | 54 | 0 | 0 | 15333 ms | 333 ms |
| `fwd` (forward only) | 66 | 34 | 0 | 0 | 26249 ms | 397 ms |
| `both` (default) | 66 | 34 | 0 | 0 | 19686 ms | 298 ms |

**Reading it:**
- **Forward is the dominant lever**: `fwd` alone (66) far outperforms `bwd` alone (46), and `both` = `fwd`
  on coverage — backward contributes **no extra refutations** on this sample, only speed.
- **Backward is a speed complement, not a coverage one**: adding it to forward cuts total refute time
  26249 → 19686 ms (~25%) by keeping the active set small (fewer linear-scan partners), but rescues no
  new problems. Several problems forward solves instantly time out under `bwd`-only (e.g. `PLA021-1`
  11 ms → timeout, `LCL224-1` 458 ms → timeout, `HWV008-2` 5.6 s → timeout).
- **Why**: forward subsumption stops redundant clauses from *entering* passive (controls the search-space
  explosion = coverage); backward only cleans the *active* set, so alone it can't stem the passive flood.
  This is the textbook division of labour, and the reason the default keeps both on.

### Ablation: forward subsumption at generation vs. selection-only (seed 42)

DISCOUNT forward-checks the given at selection regardless; the question is whether to *also* forward-check
freshly **generated** clauses before they enter passive. Run via the `gen`/`nogen` token
(`Evaluation 42 100 15000 100000 both nogen`).

| Config | REFUTED | TIMEOUT | SATURATED | BAD_PROOF | refute total |
|---|---:|---:|---:|---:|---:|
| `gen` — forward subsumption at generation **and** selection | 67 | 33 | 0 | 0 | 30763 ms |
| `nogen` — forward subsumption **only at selection** | 71 | 29 | 0 | 0 | 28171 ms |

Strictly monotonic: `nogen` solved everything `gen` did **plus 4** (`FLD013-3`, `FLD060-4`, `LCL217-1`,
`SYN575-1`), none lost. **Without term indexing**, forward-subsuming every generated clause is an
O(|active|) scan on a high-volume path that mostly re-scans survivors the selection check would re-scan
anyway; dropping it frees time for useful inference, tipping borderline problems over. **Default flipped to
`forwardSimplifyAtGeneration = false`** (revisit once Phase-4 indexing makes the generation check cheap —
the passive-bloat saving would likely tip it back).

### Phase 2 (P1): unit deletion (seed 42)

Adds **unit deletion** (the unit case of subsumption resolution): a unit clause `{L}` deletes any literal
`K` of another clause with `Lσ = ¬K` (one-sided match), forward (at selection) and backward (against
active). The shrunk clause is built via `Inference.resolve`, so it is an ordinary resolvent — **no new
`Justification` or reconstruction code**, and deletion of the original is reconstruction-free. Measured on
top of the new default (subsumption fwd+bwd, `nogen`):

| Config | REFUTED | TIMEOUT | SATURATED | BAD_PROOF | refute total |
|---|---:|---:|---:|---:|---:|
| subsumption only (`unit none`) | 71 | 29 | 0 | 0 | 24549 ms |
| + unit deletion (default) | **74** | 26 | 0 | 0 | 33548 ms |

Strictly monotonic again: **+3, all TIMEOUT → REFUTED, none lost** — `GRP124-3.004`, `GRP124-8.004`,
`GRP130-2.003` (group-theory problems, where ground unit facts trim literals off larger clauses). Still
`saturated=0`, `bad_proof=0`: every unit-deletion refutation reconstructs to a kernel-valid `⊢`.

**Current Phase-2 default** = forward+backward subsumption + forward+backward unit deletion, forward
simplification at selection only → **74/100 refuted on seed 42** (vs. the Phase-1 baseline's 35).

### Phase 2 (P1): general subsumption resolution (seed 42)

Generalises unit deletion to multi-literal side clauses `C' ∨ L` (`Lσ = ¬K`, `C'σ ⊆ main \ {K}`). Built via
`resolve` and kept only when the resolvent `subsumes` `main` — a **completeness gate** (see
`PossibleOptimizations.md`): it is conservative (skips SR steps whose `C'` carries variables outside `L`)
but never deletes a clause it doesn't entail. **Off by default** — it runs `subsumes(rc, main)` per candidate,
much heavier than unit deletion. Run via the `sr` token (`Evaluation … both nogen both both`).

| Config | REFUTED | TIMEOUT | SATURATED | BAD_PROOF | refute total |
|---|---:|---:|---:|---:|---:|
| unit deletion only (`sr none`) | 74 | 26 | 0 | 0 | 35133 ms |
| + general SR (`sr both`) | **79** | 21 | 0 | 0 | 81595 ms |

Strictly monotonic: **+5, all TIMEOUT → REFUTED, none lost** (`SYN442/455/482/488/498-1`), `saturated=0`,
`bad_proof=0`. Cost is real: total refute time ~2.3× (per-candidate `subsumes`), so the +5 came without any
regression *on this sample* but the headroom isn't guaranteed elsewhere — hence the default stays off pending
a multi-seed robustness check.

### Re-ablation after Phase-5 indexing (2026-08-08, seed 42)

The three defaults above were all set **before** term indexing. Phase 5 added the feature-vector subsumption
index, which is what the "revisit once indexing makes it cheap" notes were waiting on, so all three were
re-measured on the same sample (`Evaluation 42 100 15000 100000 …`, TPTP-v9.2.1). Each arm was run to
completion and its REFUTED **set** diffed against the baseline, not just its count — a 2-problem difference is
inside timing noise otherwise, since TIMEOUT is wall-clock-based.

| Config | REFUTED | TIMEOUT | BAD_PROOF | refute total | vs baseline | decision |
|---|---:|---:|---:|---:|---|---|
| baseline (`both nogen`, SR off, cond off) | 74 | 26 | 0 | 20156 ms | — | |
| `gen` — forward simplify at generation | 72 | 28 | 0 | 17423 ms | −2, none gained | **keep off** |
| `sr both` — general subsumption resolution | **80** | 20 | 0 | 45147 ms | **+6, none lost** | **flipped ON** |
| `cond on` — condensation | 71 | 29 | 0 | 31770 ms | −3, none gained | **keep off** |

- **`forwardSimplifyAtGeneration` stays `false`.** Indexing did narrow the gap exactly as predicted (the
  pre-indexing ablation lost 4 problems, this one loses 2) but did not tip it. Still strictly monotone the
  other way: `nogen` refutes everything `gen` does plus `FLD060-4` and `GRP130-2.003`. Both arms were run
  twice with identical counts, so the 2-problem gap is reproducible, not noise.
- **General subsumption resolution flipped to `true`** in `Discount`, `Bridge.solve`,
  `Bridge.solveTPTPProblem` and `Clausal.solveOutcome`. It now gains **6** (`SYN442/455/467/482/488/498-1`)
  and loses none — one better than the pre-indexing +5, with `bad_proof=0` across all 80 reconstructed and
  kernel-checked proofs. Refute time roughly doubles, but that is largely the 6 newly-solved problems being
  the hard ones; the count is what a fixed per-problem budget rewards.
- **Condensation stays `false`** — and is now actually *measured*, which the old "off by default pending its
  seed-42 ablation" note admitted it never had been. It loses 3 (`FLD037-1`, `GRP124-8.004`, `GRP130-2.003`)
  and gains none.

**Caveats.** One seed, one sample of 100, one dataset (clausal, equality-free, unsatisfiable). The SR gains
are entirely in the `SYN` domain, so the win may be narrower than the headline suggests; the monotonicity is
what makes flipping low-risk, not the size of the gain. The `Strategy` portfolio was **not** touched: its
per-strategy SR flags are a deliberate diversity axis (`unary-redundancy` and `subsumption-light` already set
them), and every strategy is documented as differing from `balanced` in exactly two knobs. Re-deriving the
portfolio against the new engine default is a separate exercise.

> **Completeness lesson (the bug behind the gate).** A first cut deleted `main` whenever the guard matched,
> *without* the `subsumes(rc, main)` check. On seed 42 that turned `SYN036-4` `REFUTED → SATURATED`: building
> via `resolve` only yields `main \ {K}` when every side variable is in `L`; otherwise it leaves a variable
> free and the kept clause doesn't entail `main`, so deleting `main` discarded a clause a refutation needed.
> Not a *soundness* failure (no false `□` is ever derived) but a *completeness* one (a real refutation is
> missed and the set wrongly saturates) — which is exactly what the `saturated`-must-stay-0 metric guards.

### Phase 2 (P2): condensation (seed 42)

Replaces a clause by an equivalent shorter factor of itself (a factor that `subsumes` it), applied once at
creation (clause-local). Built via `Inference.factor` + the `subsumes` gate ⇒ ordinary `Factoring`
justification, no new reconstruction. **Off by default.** Run via the `cond` token (`Evaluation … none on`).

| Config | REFUTED | TIMEOUT | SATURATED | BAD_PROOF | refute total |
|---|---:|---:|---:|---:|---:|
| condensation off (default) | 74 | 26 | 0 | 0 | 32652 ms |
| condensation on | 71 | 29 | 0 | 0 | 49778 ms |

**Net loss: −3** (`FLD037-1`, `GRP124-8.004`, `GRP130-2.003`, all REFUTED → TIMEOUT), refute time ~1.5×.
Correct (`saturated=0`, `bad_proof=0`) but not worth it on this fragment: condensation runs an O(n²)
`factor`+`subsumes` scan on *every* new clause, yet condensable clauses (two literals that coincide under a
substitution) are rare in pure no-equality clausal problems — so it is mostly overhead that tips
boundary-timeout problems over the wall. **Default stays off.** (Expected to earn its place once equality /
arithmetic make collapsible literals common — Phase 4.)

**End-of-Phase-2 default** = forward+backward subsumption + forward+backward unit deletion, at selection
only; general subsumption resolution and condensation implemented but **off by default** (neither a net win
on the no-equality fragment without indexing) → **74/100 refuted on seed 42**, `saturated=0`, `bad_proof=0`.

## Phase 3 — FOF (non-clausal) benchmark (`FofEvaluation`, seed 42, clean 944 set)

Second dataset (`tptp-fof-fo-noeq-thm.txt`): non-clausal TPTP theorems selected the same way as the clausal
set but by `SPC = FOF_THM_{RFO,EPR}_NEQ` (no equality, no arithmetic), **CSR/SUMO excluded** (944 problems).
Each problem is parsed, run through `certifyClausal` (or the uncertified `clausalForm`) with `Clausal.prove`,
and **every refutation is kernel-checked** (`bad_proof` must stay 0). Per-problem `clausify / prover / check`
timings are reported. Timeout 10 s, `maxGiven`/`maxSize` 50000.

| Milestone | REFUTED | SATURATED | TIMEOUT | HARD_TIMEOUT | BAD_PROOF | SKIPPED | PARSE_ERR |
|---|---:|---:|---:|---:|---:|---:|---:|
| initial (with CSR in sample, 1303 set) | 45 | 9 | 21 | 9 | 0 | 14 | 2 |
| clean 944 set, before clausifier fixes | 50 | 9 | 21 | 9 | 0 | 0 | 1 |
| + η-expand fix (over-reached into ε)   | 50 | 1 | 21 | 9 | **9** | 0 | 1 |
| + ε left untouched + ⊤/⊥ absorption     | **60** | **0** | ~30 | 9 | **0** | 0 | 1 |

**Certified vs. uncertified clausification** (same clauses, so same solve count): uncertified `clausalForm`
(pure transforms, no proof) is ~**2× faster total, ~20× on the median** refute time — the certified pipeline's
proof-building + kernel-checking dominates most easy problems. Per-phase: on easy solves the `check` of the
composed proof often exceeds the `prover` time.

**Bugs found via this benchmark (both clausification, both fixed — see Phase3.md item 8):** (1) η-reduced
quantifiers stranded as opaque atoms in clauses (`betaNormalForm` η-reduces `λy.p(x,y)→p(x)`; the `Forall`
extractor needs a `Lambda`) → `etaExpandQuantifiers` on ∀/∃ only; (2) `⊤`/`⊥` (`$true`/`$false`) not absorbed
in NNF → survived as uninterpreted atoms → NNF `mkAnd`/`mkOr` absorption laws. `SATURATED 9 → 0`,
`REFUTED 50 → 60`, `bad_proof 0`.

**Remaining failures are dominated by rating-1.00 problems** — the `LCL…+1.0NN` "'naive relational encoding of
modal logic"' family is unsolved by *any* ATP system (rating 1.00), and `LCL648+1.020` even overflows the
recursive TPTP parser's stack. These discriminate nothing; a fair reading of "how many are in reach" should
split the timeouts by TPTP rating.
