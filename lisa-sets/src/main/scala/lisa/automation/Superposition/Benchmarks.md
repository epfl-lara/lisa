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
