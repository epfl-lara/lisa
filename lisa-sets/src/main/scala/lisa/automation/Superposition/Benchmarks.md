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
