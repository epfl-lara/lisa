# Baseline: our prover vs. E — seed 42, 100 problems/dataset

New-machine baseline (Linux). Our prover runs with the **non-proof-producing clausifier** (`UncertifiedClausification.clausalForm`) and **no proof reconstruction** (`Clausal.solveOutcome` — the DISCOUNT loop to a verdict only), fingerprint indexing on. Equality inferences are **off** for the two equality-free sets and **on** for the equality set. E 3.5.1 runs `--auto --cpu-limit=15`.

- **Budget:** 15 s wall per problem, both provers. Sample: `Random(42).shuffle(list).take(100)` (identical for both).
- **Our columns:** `clausify` and `prover` are the two timed phases (ms); `total = clausify + prover`; `given` = given-clause loop iterations; `derived` = clauses ever enqueued to passive.
- **E columns:** `time` = wall-clock (s, includes E's own parsing/axiom-include loading); `given` = E's *Processed clauses*. **E prints statistics only when it finishes** — on a 15 s timeout (`ResourceOut`) it reports no count, shown as `—`.
- **Timing caveat:** our `clausify`/`prover` exclude TPTP parsing (done before timing); E's wall-clock includes it. So totals are indicative, not a controlled head-to-head of identical work.

## Summary

| Dataset | E solved | Ours solved | Both | E-only | Ours-only | E med time (solved) | Ours med total (solved) | E avg given (solved) | Ours avg given (solved) |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| Clausal (FO, equality-free, unsat clause sets) | 82 | 74 | 72 | 10 | 2 | 0.02s | 5.20ms | 11624 | 958 |
| FOF (FO, equality-free theorems) | 75 | 63 | 61 | 14 | 2 | 0.01s | 2.10ms | 10639 | 712 |
| FOF with equality (FO theorems) | 37 | 28 | 25 | 12 | 3 | 0.04s | 115.80ms | 6453 | 3056 |

## Clausal (FO, equality-free, unsat clause sets)

Source list: `tptp-clausal-fo-noeq-uns.txt (1651)`. Rows in seed-42 sample order.

| # | Problem | E status | E time(s) | E given | Ours result | clausify(ms) | prover(ms) | total(ms) | given | derived |
|--:|---|---|--:|--:|---|--:|--:|--:|--:|--:|
| 1 | SYN498-1.p | Unsatisfiable | 4.0 | 75662 | TIMEOUT | 60.1 | 15074.1 | 15134.3 | 25587 | 2291789 |
| 2 | SET015-1.p | Unsatisfiable | 0.1 | 3592 | REFUTED | 1.2 | 2588.8 | 2590 | 4243 | 479638 |
| 3 | ANA037-2.p | Unsatisfiable | 0.0 | 25 | REFUTED | 2.8 | 3.1 | 5.9 | 31 | 59 |
| 4 | LCL090-1.p | Unsatisfiable | 0.1 | 1019 | REFUTED | 1.7 | 88.6 | 90.3 | 558 | 33365 |
| 5 | SWV245-2.p | Unsatisfiable | 0.0 | 56 | REFUTED | 1 | 2.2 | 3.2 | 43 | 88 |
| 6 | SWV336-2.p | Unsatisfiable | 0.0 | 2 | REFUTED | 0.3 | 0.9 | 1.2 | 2 | 2 |
| 7 | SYN701-1.p | Unsatisfiable | 1.9 | 22639 | REFUTED | 2.8 | 24.7 | 27.5 | 653 | 7311 |
| 8 | SYN467-1.p | ResourceOut | 15.0 | — | TIMEOUT | 9.4 | 15005.4 | 15014.8 | 17878 | 2551627 |
| 9 | FLD091-1.p | ResourceOut | 15.1 | — | TIMEOUT | 1.1 | 15000.9 | 15002.1 | 12563 | 3902484 |
| 10 | SYN131-1.p | Unsatisfiable | 0.0 | 41 | REFUTED | 10.3 | 7.6 | 17.8 | 13 | 362 |
| 11 | MSC015-1.022.p | ResourceOut | 15.0 | — | TIMEOUT | 4.3 | 15005.2 | 15009.5 | 13577 | 13578 |
| 12 | SYN111-1.p | Unsatisfiable | 0.0 | 596 | REFUTED | 12.9 | 20.3 | 33.2 | 953 | 3151 |
| 13 | SYN660-1.p | Unsatisfiable | 0.1 | 1596 | REFUTED | 2.2 | 5.8 | 8 | 153 | 704 |
| 14 | SYO619-1.p | ResourceOut | 15.0 | — | TIMEOUT | 1.4 | 15001.3 | 15002.8 | 16426 | 32837 |
| 15 | KRS001-1.p | Unsatisfiable | 0.0 | 27 | REFUTED | 0.7 | 0.9 | 1.6 | 27 | 32 |
| 16 | SWV422-1.300.p | ResourceOut | 15.0 | — | TIMEOUT | 3.1 | 15004.4 | 15007.5 | 37653 | 144902 |
| 17 | SYN819-1.p | Unsatisfiable | 0.2 | 3962 | REFUTED | 94.9 | 122.7 | 217.6 | 921 | 1069 |
| 18 | SYN455-1.p | Unsatisfiable | 11.9 | 204898 | TIMEOUT | 4.6 | 15004.6 | 15009.2 | 23648 | 2490606 |
| 19 | MGT002-1.p | Unsatisfiable | 0.0 | 26 | REFUTED | 0.8 | 1.5 | 2.3 | 45 | 58 |
| 20 | SYN108-1.p | Unsatisfiable | 0.0 | 217 | REFUTED | 3.9 | 4.7 | 8.5 | 192 | 726 |
| 21 | SYN035-1.p | Unsatisfiable | 0.0 | 1 | REFUTED | 0.2 | 0.5 | 0.6 | 4 | 5 |
| 22 | SYN900-1.p | Unsatisfiable | 0.0 | 180 | REFUTED | 95.1 | 158.4 | 253.5 | 200 | 229 |
| 23 | LCL193-1.p | Unsatisfiable | 0.0 | 1155 | REFUTED | 0.4 | 2.6 | 3 | 86 | 346 |
| 24 | SYN285-1.p | Unsatisfiable | 0.0 | 791 | REFUTED | 4.1 | 20.2 | 24.3 | 926 | 3071 |
| 25 | SYN705-1.p | Unsatisfiable | 0.1 | 1565 | REFUTED | 1.9 | 62 | 63.9 | 1196 | 8047 |
| 26 | LAT265-2.p | Unsatisfiable | 0.0 | 2 | REFUTED | 0.1 | 0.6 | 0.7 | 1 | 2 |
| 27 | GRP004-1.p | Unsatisfiable | 0.0 | 70 | REFUTED | 0.3 | 1.6 | 1.8 | 48 | 312 |
| 28 | MGT018-1.p | Unsatisfiable | 0.0 | 51 | REFUTED | 0.5 | 1.2 | 1.7 | 49 | 55 |
| 29 | SYN796-1.p | Unsatisfiable | 0.0 | 1178 | REFUTED | 2.4 | 33.4 | 35.9 | 910 | 4408 |
| 30 | SYO667-1.p | Unsatisfiable | 0.0 | 283 | REFUTED | 0.8 | 13 | 13.8 | 299 | 1094 |
| 31 | SYN169-1.p | Unsatisfiable | 0.0 | 182 | REFUTED | 5.7 | 5.7 | 11.4 | 253 | 846 |
| 32 | SYN488-1.p | Unsatisfiable | 8.5 | 124117 | TIMEOUT | 2.2 | 15041.3 | 15043.5 | 26588 | 2793599 |
| 33 | SYN557-1.p | Unsatisfiable | 0.0 | 158 | REFUTED | 0.4 | 270.9 | 271.3 | 882 | 133533 |
| 34 | NUM014-1.p | Unsatisfiable | 0.0 | 12 | REFUTED | 0.3 | 0.5 | 0.8 | 13 | 22 |
| 35 | LCL110-1.p | Unsatisfiable | 0.0 | 76 | REFUTED | 0.2 | 19.5 | 19.7 | 201 | 6027 |
| 36 | PLA021-1.p | Unsatisfiable | 0.0 | 86 | REFUTED | 0.6 | 3.2 | 3.8 | 117 | 158 |
| 37 | LCL224-1.p | Unsatisfiable | 0.6 | 11649 | REFUTED | 0.2 | 777.8 | 778.1 | 2623 | 162091 |
| 38 | SYN012-1.p | Unsatisfiable | 0.0 | 20 | REFUTED | 0.3 | 0.6 | 0.9 | 18 | 27 |
| 39 | SWV283-2.p | Unsatisfiable | 0.0 | 42 | REFUTED | 0.2 | 0.8 | 1.1 | 22 | 46 |
| 40 | FLD090-1.p | ResourceOut | 15.1 | — | TIMEOUT | 0.3 | 15002.5 | 15002.8 | 11072 | 4209229 |
| 41 | COM001-1.p | Unsatisfiable | 0.0 | 21 | REFUTED | 0.3 | 0.5 | 0.8 | 22 | 24 |
| 42 | SYN300-1.p | Unsatisfiable | 0.0 | 1154 | REFUTED | 4.5 | 10.8 | 15.3 | 666 | 2027 |
| 43 | SWV422-1.360.p | ResourceOut | 15.0 | — | TIMEOUT | 2.8 | 15004.2 | 15007 | 29250 | 102774 |
| 44 | PUZ011-1.p | Unsatisfiable | 0.0 | 28 | REFUTED | 0.2 | 0.5 | 0.7 | 40 | 93 |
| 45 | LCL131-1.p | Unsatisfiable | 0.3 | 6968 | TIMEOUT | 0.1 | 15060.2 | 15060.3 | 5125 | 3582105 |
| 46 | SYN036-4.p | Unsatisfiable | 0.0 | 66 | REFUTED | 1 | 4.5 | 5.5 | 106 | 636 |
| 47 | SWV290-2.p | Unsatisfiable | 0.0 | 21 | REFUTED | 0.5 | 0.9 | 1.4 | 20 | 25 |
| 48 | SYN607-1.p | Unsatisfiable | 0.5 | 15731 | TIMEOUT | 0.8 | 15002.8 | 15003.6 | 15930 | 3637967 |
| 49 | SYN442-1.p | Unsatisfiable | 12.8 | 198617 | TIMEOUT | 2 | 15002.9 | 15004.9 | 21067 | 2914323 |
| 50 | SYN612-1.p | Unsatisfiable | 3.5 | 59819 | TIMEOUT | 0.5 | 15001 | 15001.5 | 16437 | 3201736 |
| 51 | PLA031-1.018.p | ResourceOut | 15.0 | — | TIMEOUT | 38.2 | 15052.2 | 15090.4 | 14859 | 232509 |
| 52 | SYO682-1.p | Unsatisfiable | 1.2 | 8447 | TIMEOUT | 6.9 | 15020.7 | 15027.7 | 4015 | 50483 |
| 53 | GRP124-3.004.p | Unsatisfiable | 0.1 | 1197 | REFUTED | 0.6 | 412.3 | 412.9 | 1152 | 95334 |
| 54 | LCL007-1.p | Unsatisfiable | 0.0 | 11 | REFUTED | 0.1 | 0.3 | 0.5 | 7 | 10 |
| 55 | SYN031-1.p | Unsatisfiable | 0.0 | 8 | REFUTED | 0.1 | 0.3 | 0.4 | 8 | 17 |
| 56 | LCL170-1.p | Unsatisfiable | 0.0 | 4 | REFUTED | 0.2 | 0.3 | 0.5 | 7 | 12 |
| 57 | PUZ035-1.p | Unsatisfiable | 0.0 | 21 | REFUTED | 0.2 | 1.1 | 1.3 | 86 | 193 |
| 58 | SYN704-1.p | Unsatisfiable | 0.2 | 7316 | REFUTED | 1.4 | 130.9 | 132.3 | 2004 | 30806 |
| 59 | FLD037-1.p | Unsatisfiable | 0.4 | 20317 | REFUTED | 0.5 | 3832.2 | 3832.8 | 5945 | 1137524 |
| 60 | SYN482-1.p | Unsatisfiable | 11.7 | 105059 | TIMEOUT | 2 | 15003.5 | 15005.5 | 23856 | 3168268 |
| 61 | SYN614-1.p | ResourceOut | 15.1 | — | TIMEOUT | 0.6 | 15003.4 | 15004 | 16846 | 2388130 |
| 62 | SYN145-1.p | Unsatisfiable | 0.0 | 30 | REFUTED | 4.4 | 4.3 | 8.7 | 5 | 362 |
| 63 | LCL050-1.p | ResourceOut | 15.1 | — | REFUTED | 0.1 | 3634.7 | 3634.8 | 3051 | 944601 |
| 64 | SYN576-1.p | ResourceOut | 15.1 | — | TIMEOUT | 0.6 | 15001.5 | 15002.1 | 12584 | 2545066 |
| 65 | LCL002-1.p | Unsatisfiable | 0.6 | 5700 | TIMEOUT | 0.2 | 15000.4 | 15000.5 | 7966 | 4422086 |
| 66 | SYN659-1.p | Unsatisfiable | 1.1 | 25278 | REFUTED | 1 | 413.6 | 414.6 | 2517 | 120404 |
| 67 | NUM020-1.p | Unsatisfiable | 0.0 | 297 | REFUTED | 0.2 | 1.9 | 2.2 | 61 | 320 |
| 68 | FLD053-3.p | ResourceOut | 15.1 | — | TIMEOUT | 0.8 | 15001.8 | 15002.6 | 10578 | 4216739 |
| 69 | SYN711-1.p | ResourceOut | 15.1 | — | REFUTED | 1.2 | 7.6 | 8.7 | 471 | 2511 |
| 70 | FLD070-4.p | Unsatisfiable | 0.0 | 159 | REFUTED | 0.5 | 9.5 | 10 | 202 | 1895 |
| 71 | FLD013-3.p | Unsatisfiable | 0.3 | 9606 | REFUTED | 0.5 | 4035.8 | 4036.3 | 6252 | 1405709 |
| 72 | GRP130-2.003.p | Unsatisfiable | 0.0 | 694 | REFUTED | 0.3 | 1869 | 1869.3 | 1241 | 409975 |
| 73 | FLD025-5.p | Unsatisfiable | 0.1 | 1139 | REFUTED | 0.6 | 5.7 | 6.3 | 181 | 934 |
| 74 | LAT271-2.p | Unsatisfiable | 0.0 | 5 | REFUTED | 0.1 | 0.3 | 0.5 | 5 | 6 |
| 75 | LCL217-1.p | Unsatisfiable | 0.1 | 1853 | REFUTED | 0.2 | 148.8 | 149 | 1116 | 35396 |
| 76 | FLD044-2.p | ResourceOut | 15.1 | — | TIMEOUT | 0.5 | 15015.5 | 15015.9 | 14039 | 3511471 |
| 77 | MGT009-1.p | Unsatisfiable | 0.0 | 39 | REFUTED | 0.5 | 1.6 | 2.1 | 67 | 75 |
| 78 | SYN650-1.p | ResourceOut | 15.1 | — | TIMEOUT | 1.1 | 15002.5 | 15003.6 | 16979 | 1992463 |
| 79 | SYN231-1.p | Unsatisfiable | 0.0 | 183 | REFUTED | 5.9 | 7.6 | 13.5 | 278 | 940 |
| 80 | GRP124-8.004.p | Unsatisfiable | 0.0 | 383 | REFUTED | 0.7 | 616 | 616.7 | 1009 | 140112 |
| 81 | LCL399-1.p | Unsatisfiable | 0.0 | 234 | REFUTED | 0.1 | 62.8 | 62.9 | 468 | 24912 |
| 82 | LCL199-1.p | Unsatisfiable | 0.0 | 115 | REFUTED | 0.2 | 5.7 | 5.8 | 154 | 1061 |
| 83 | SET009-1.p | Unsatisfiable | 0.0 | 45 | REFUTED | 0.3 | 3.9 | 4.2 | 119 | 772 |
| 84 | SYN068-1.p | Unsatisfiable | 0.0 | 9 | REFUTED | 0.2 | 0.4 | 0.5 | 9 | 10 |
| 85 | SYN575-1.p | Unsatisfiable | 0.3 | 14832 | REFUTED | 0.5 | 12648.1 | 12648.6 | 14106 | 1662656 |
| 86 | GRP028-4.p | Unsatisfiable | 0.0 | 9 | REFUTED | 0.2 | 0.4 | 0.6 | 9 | 19 |
| 87 | PUZ029-1.p | Unsatisfiable | 0.0 | 25 | REFUTED | 0.2 | 0.4 | 0.6 | 26 | 28 |
| 88 | PLA001-1.p | ResourceOut | 15.1 | — | TIMEOUT | 0.2 | 15001.1 | 15001.4 | 9345 | 3263469 |
| 89 | FLD060-4.p | Unsatisfiable | 0.2 | 7271 | REFUTED | 0.5 | 1668.4 | 1668.9 | 4182 | 560429 |
| 90 | SYN064-1.p | Unsatisfiable | 0.0 | 1 | REFUTED | 0.1 | 0.2 | 0.3 | 1 | 2 |
| 91 | GRP041-2.p | Unsatisfiable | 0.0 | 10 | REFUTED | 0.3 | 0.4 | 0.7 | 9 | 19 |
| 92 | SYN143-1.p | Unsatisfiable | 0.0 | 1825 | REFUTED | 4.4 | 19.5 | 23.9 | 751 | 2352 |
| 93 | LCL362-1.p | Unsatisfiable | 0.0 | 20 | REFUTED | 0.1 | 0.7 | 0.8 | 29 | 119 |
| 94 | FLD050-1.p | ResourceOut | 15.1 | — | TIMEOUT | 0.3 | 15002.3 | 15002.6 | 12506 | 4011004 |
| 95 | SYN150-1.p | Unsatisfiable | 0.0 | 124 | REFUTED | 4.1 | 3.9 | 8 | 204 | 715 |
| 96 | HWV008-2.002.p | Unsatisfiable | 0.0 | 370 | REFUTED | 1 | 2269.7 | 2270.6 | 7604 | 68288 |
| 97 | LCL226-1.p | Unsatisfiable | 0.0 | 315 | REFUTED | 0.2 | 0.7 | 0.9 | 46 | 151 |
| 98 | SYN129-1.p | Unsatisfiable | 0.1 | 1656 | REFUTED | 2.6 | 14.8 | 17.4 | 862 | 2885 |
| 99 | PUZ017-1.p | ResourceOut | 15.0 | — | TIMEOUT | 2 | 15003 | 15005 | 8734 | 3223237 |
| 100 | LCL205-1.p | Unsatisfiable | 0.0 | 122 | REFUTED | 0.1 | 1.3 | 1.4 | 93 | 393 |

## FOF (FO, equality-free theorems)

Source list: `tptp-fof-fo-noeq-thm.txt (944)`. Rows in seed-42 sample order.

| # | Problem | E status | E time(s) | E given | Ours result | clausify(ms) | prover(ms) | total(ms) | given | derived |
|--:|---|---|--:|--:|---|--:|--:|--:|--:|--:|
| 1 | GEO242+3.p | Theorem | 0.0 | 32 | REFUTED | 89 | 84.1 | 173 | 78 | 119 |
| 2 | NLP117+1.p | Theorem | 0.0 | 479 | REFUTED | 9438.3 | 538.1 | 9976.4 | 272 | 311 |
| 3 | LCL374+2.p | ResourceOut | 15.1 | — | TIMEOUT | 0.9 | 15010.6 | 15011.5 | 5495 | 3149479 |
| 4 | GEO204+2.p | Theorem | 0.1 | 2169 | REFUTED | 5.6 | 855.9 | 861.5 | 1561 | 130346 |
| 5 | GEO222+2.p | Theorem | 1.6 | 11378 | REFUTED | 3.8 | 1435.3 | 1439.1 | 2257 | 439903 |
| 6 | GEO258+3.p | Theorem | 0.0 | 253 | REFUTED | 9.6 | 326.2 | 335.8 | 1333 | 180782 |
| 7 | LCL372+2.p | ResourceOut | 15.1 | — | TIMEOUT | 0.6 | 15004.2 | 15004.8 | 5522 | 3226022 |
| 8 | GEO218+2.p | Theorem | 0.0 | 64 | REFUTED | 3.6 | 13.4 | 17.1 | 190 | 2928 |
| 9 | GEO184+1.p | Theorem | 0.0 | 191 | REFUTED | 7 | 3.5 | 10.5 | 86 | 798 |
| 10 | GEO195+2.p | Theorem | 0.2 | 5569 | REFUTED | 4.9 | 28.4 | 33.3 | 412 | 14008 |
| 11 | SYN721+1.p | Theorem | 0.0 | 8 | REFUTED | 1.2 | 1.1 | 2.3 | 14 | 14 |
| 12 | PRD001+1.p | ResourceOut | 15.0 | — | TIMEOUT | 44.1 | 15041.1 | 15085.3 | 32853 | 271353 |
| 13 | SYN968+1.p | Theorem | 0.0 | 1 | REFUTED | 3.8 | 0.5 | 4.3 | 2 | 3 |
| 14 | LCL648+1.020.p | ResourceOut | 15.1 | — | PARSE_ERR | 0 | 0 | 0 | 0 | 0 |
| 15 | GEO222+1.p | Theorem | 2.1 | 16957 | REFUTED | 1.5 | 14216.3 | 14217.7 | 7569 | 3516596 |
| 16 | GEO177+1.p | ResourceOut | 15.1 | — | TIMEOUT | 16.9 | 15002.7 | 15019.6 | 8554 | 3007435 |
| 17 | SYN958+1.p | Theorem | 0.0 | 2 | REFUTED | 0.7 | 0.5 | 1.2 | 8 | 8 |
| 18 | LCL670+1.001.p | Theorem | 10.5 | 47099 | TIMEOUT | 40.6 | 15003.7 | 15044.3 | 27980 | 193606 |
| 19 | NUN069+1.p | Theorem | 0.0 | 59 | REFUTED | 11.5 | 2.1 | 13.6 | 105 | 186 |
| 20 | SYN363+1.p | Theorem | 0.0 | 4 | REFUTED | 0.8 | 0.5 | 1.4 | 7 | 7 |
| 21 | PUZ031+1.p | Theorem | 0.0 | 125 | REFUTED | 1.9 | 1039.8 | 1041.7 | 3892 | 74662 |
| 22 | GEO245+3.p | Theorem | 0.0 | 12 | REFUTED | 4.9 | 3.2 | 8.1 | 72 | 116 |
| 23 | LCL666+1.010.p | ResourceOut | 15.1 | — | HARD_TIMEOUT | 0 | 0 | 0 | 0 | 0 |
| 24 | GEO239+1.p | Theorem | 0.0 | 3 | REFUTED | 2.3 | 1.3 | 3.6 | 45 | 100 |
| 25 | SYN353+1.p | Theorem | 0.0 | 92 | REFUTED | 16.9 | 23.2 | 40.1 | 974 | 4904 |
| 26 | LCL382+1.p | ResourceOut | 15.1 | — | TIMEOUT | 0.2 | 15001.8 | 15002 | 5671 | 3205025 |
| 27 | GEO246+1.p | Theorem | 0.0 | 16 | REFUTED | 3.5 | 2.8 | 6.3 | 77 | 126 |
| 28 | MED001+1.p | Theorem | 0.0 | 93 | REFUTED | 3.4 | 1.5 | 4.8 | 162 | 336 |
| 29 | NLP079+1.p | Theorem | 0.0 | 123 | HARD_TIMEOUT | 0 | 0 | 0 | 0 | 0 |
| 30 | MED008+1.p | Theorem | 0.3 | 2848 | TIMEOUT | 8.6 | 15024.8 | 15033.4 | 20455 | 3225681 |
| 31 | SYN476+1.p | ResourceOut | 15.0 | — | TIMEOUT | 59.3 | 15048.9 | 15108.3 | 31943 | 1349051 |
| 32 | SYN503+1.p | Theorem | 11.4 | 115062 | TIMEOUT | 29.1 | 15026.6 | 15055.6 | 28156 | 2363938 |
| 33 | SYN349+1.p | Theorem | 0.0 | 19 | REFUTED | 14.8 | 1.8 | 16.6 | 135 | 257 |
| 34 | LCL660+1.015.p | ResourceOut | 15.1 | — | HARD_TIMEOUT | 0 | 0 | 0 | 0 | 0 |
| 35 | KRS190+1.p | Theorem | 0.1 | 8888 | TIMEOUT | 17.7 | 15007.9 | 15025.6 | 16770 | 4855464 |
| 36 | SYN386+1.p | Theorem | 0.0 | 10 | REFUTED | 2.6 | 1.1 | 3.6 | 23 | 25 |
| 37 | KRS178+1.p | Theorem | 0.0 | 32 | REFUTED | 6.2 | 2.5 | 8.7 | 70 | 84 |
| 38 | GEO184+2.p | Theorem | 0.0 | 475 | REFUTED | 4.5 | 81.7 | 86.3 | 576 | 34892 |
| 39 | NUN080+1.p | Theorem | 0.7 | 28044 | REFUTED | 5.1 | 19 | 24.1 | 714 | 5254 |
| 40 | COM003+1.p | ResourceOut | 15.1 | — | REFUTED | 3.2 | 17 | 20.2 | 886 | 3422 |
| 41 | SET627+3.p | Theorem | 0.0 | 13 | REFUTED | 0.8 | 0.7 | 1.5 | 21 | 29 |
| 42 | KRS251+1.p | ResourceOut | 15.1 | — | TIMEOUT | 15.7 | 15005.3 | 15021 | 17973 | 5557045 |
| 43 | SYN506+1.p | Theorem | 0.7 | 21245 | TIMEOUT | 17.5 | 15022.3 | 15039.8 | 30008 | 2263215 |
| 44 | MGT009+1.p | Theorem | 0.0 | 39 | HARD_TIMEOUT | 0 | 0 | 0 | 0 | 0 |
| 45 | MGT022+2.p | Theorem | 0.0 | 15 | REFUTED | 1.8 | 0.8 | 2.6 | 25 | 30 |
| 46 | LCL674+1.001.p | Theorem | 0.0 | 16 | REFUTED | 2.6 | 1.7 | 4.3 | 85 | 144 |
| 47 | LCL109+2.p | ResourceOut | 15.1 | — | TIMEOUT | 0.3 | 15008.6 | 15008.9 | 4523 | 598887 |
| 48 | LCL421+2.p | ResourceOut | 15.1 | — | TIMEOUT | 0.4 | 15008.2 | 15008.6 | 4621 | 1181945 |
| 49 | NUN078+1.p | ResourceOut | 15.1 | — | TIMEOUT | 5.6 | 15003.4 | 15009 | 18552 | 3733710 |
| 50 | LCL369+1.p | ResourceOut | 15.1 | — | TIMEOUT | 0.2 | 15001.4 | 15001.7 | 6137 | 3494549 |
| 51 | LCL678+1.001.p | Theorem | 0.0 | 7 | REFUTED | 1 | 0.6 | 1.6 | 19 | 24 |
| 52 | SYN384+1.p | Theorem | 0.0 | 2 | REFUTED | 0.7 | 0.4 | 1 | 3 | 3 |
| 53 | LCL686+1.001.p | Theorem | 0.0 | 35 | REFUTED | 3.3 | 1.8 | 5.1 | 131 | 378 |
| 54 | SYN917+1.p | Theorem | 0.0 | 646 | TIMEOUT | 12.6 | 15006.2 | 15018.8 | 6223 | 1511875 |
| 55 | GEO207+1.p | Theorem | 0.0 | 4 | REFUTED | 1 | 0.6 | 1.6 | 4 | 18 |
| 56 | LCL638+1.020.p | ResourceOut | 15.1 | — | HARD_TIMEOUT | 0 | 0 | 0 | 0 | 0 |
| 57 | SYO525+1.021.p | ResourceOut | 15.0 | — | TIMEOUT | 3.5 | 15001.9 | 15005.4 | 12374 | 12381 |
| 58 | GEO174+1.p | Theorem | 0.0 | 39 | REFUTED | 6 | 5.2 | 11.2 | 99 | 1013 |
| 59 | SEV515+1.p | Theorem | 0.1 | 1581 | REFUTED | 2.7 | 2.1 | 4.8 | 165 | 336 |
| 60 | LCL422+2.p | ResourceOut | 15.1 | — | TIMEOUT | 0.4 | 15002.6 | 15003 | 4743 | 1212812 |
| 61 | LCL981+1.p | Theorem | 14.6 | 111064 | TIMEOUT | 0.7 | 15000.8 | 15001.5 | 7544 | 4082776 |
| 62 | GEO260+1.p | Theorem | 0.0 | 158 | TIMEOUT | 8.9 | 15003.9 | 15012.8 | 14506 | 4345170 |
| 63 | SYN465+1.p | Theorem | 6.5 | 118350 | TIMEOUT | 21.2 | 15017.8 | 15039 | 28135 | 2057488 |
| 64 | GEO170+2.p | Theorem | 0.0 | 244 | REFUTED | 2 | 22.1 | 24.1 | 192 | 7346 |
| 65 | LCL656+1.020.p | ResourceOut | 15.0 | — | TIMEOUT | 134.4 | 15009.5 | 15143.9 | 9171 | 281106 |
| 66 | SWB001+3.p | Theorem | 0.0 | 539 | REFUTED | 11.3 | 6.6 | 17.9 | 426 | 1296 |
| 67 | SWB022+2.p | Theorem | 0.0 | 156 | REFUTED | 4990.4 | 851.4 | 5841.8 | 427 | 565 |
| 68 | SEU167+3.p | Theorem | 0.0 | 20 | REFUTED | 1.3 | 0.5 | 1.7 | 22 | 36 |
| 69 | SYN447+1.p | ResourceOut | 15.1 | — | TIMEOUT | 26.8 | 15031.4 | 15058.2 | 29362 | 3090823 |
| 70 | SYO607+1.p | Theorem | 0.0 | 536 | REFUTED | 1.7 | 16.9 | 18.6 | 269 | 2199 |
| 71 | SYN927+1.p | Theorem | 0.0 | 1 | REFUTED | 0.3 | 0.3 | 0.6 | 2 | 3 |
| 72 | GEO216+1.p | Theorem | 0.0 | 5 | REFUTED | 0.7 | 0.5 | 1.2 | 8 | 23 |
| 73 | SYN057+1.p | Theorem | 0.0 | 11 | REFUTED | 0.4 | 0.4 | 0.7 | 15 | 16 |
| 74 | NUN062+1.p | Theorem | 0.1 | 2971 | REFUTED | 5 | 7.5 | 12.5 | 290 | 1071 |
| 75 | KRS217+1.p | ResourceOut | 15.1 | — | TIMEOUT | 12.2 | 15003.3 | 15015.6 | 16833 | 4883986 |
| 76 | SYN370+1.p | Theorem | 0.0 | 2 | REFUTED | 0.8 | 0.5 | 1.2 | 4 | 4 |
| 77 | KRS194+1.p | Theorem | 0.1 | 7491 | REFUTED | 13 | 10096 | 10109.1 | 13958 | 3580441 |
| 78 | GRP001+6.p | Theorem | 0.0 | 182 | REFUTED | 2.9 | 17.9 | 20.8 | 298 | 10262 |
| 79 | SYN051+1.p | Theorem | 0.0 | 5 | REFUTED | 0.4 | 0.3 | 0.7 | 12 | 15 |
| 80 | KRS149+1.p | Theorem | 0.0 | 418 | REFUTED | 9.4 | 122.9 | 132.3 | 4223 | 8275 |
| 81 | GEO252+1.p | Theorem | 0.0 | 2 | REFUTED | 2.5 | 1.1 | 3.6 | 51 | 103 |
| 82 | PHI014+1.p | Theorem | 0.0 | 22 | REFUTED | 0.7 | 0.7 | 1.4 | 42 | 50 |
| 83 | SYN986+1.001.p | Theorem | 0.0 | 6 | REFUTED | 0.2 | 0.2 | 0.4 | 6 | 7 |
| 84 | GEO263+1.p | Theorem | 0.0 | 132 | REFUTED | 147.6 | 27.7 | 175.3 | 153 | 433 |
| 85 | SYN974+1.p | Theorem | 0.0 | 2 | REFUTED | 0.2 | 0.2 | 0.4 | 3 | 3 |
| 86 | SYN954+1.p | Theorem | 0.0 | 5 | REFUTED | 0.4 | 0.3 | 0.8 | 19 | 27 |
| 87 | KRS170+1.p | Theorem | 0.0 | 24 | REFUTED | 0.9 | 0.5 | 1.5 | 27 | 31 |
| 88 | SYN924+1.p | Theorem | 0.0 | 8 | REFUTED | 0.5 | 0.6 | 1.1 | 46 | 86 |
| 89 | NUN077+1.p | ResourceOut | 15.1 | — | TIMEOUT | 2.1 | 15001.5 | 15003.6 | 18801 | 3840847 |
| 90 | GEO187+1.p | ResourceOut | 15.1 | — | TIMEOUT | 25.6 | 15013 | 15038.6 | 6947 | 2595084 |
| 91 | SYN381+1.p | Theorem | 0.0 | 7 | REFUTED | 0.5 | 0.4 | 1 | 15 | 17 |
| 92 | GEO257+1.p | Theorem | 0.0 | 5 | REFUTED | 38 | 7.7 | 45.7 | 94 | 150 |
| 93 | GEO179+2.p | Theorem | 0.0 | 344 | REFUTED | 4.2 | 59.9 | 64.1 | 330 | 15200 |
| 94 | KRS191+1.p | Theorem | 0.2 | 9394 | TIMEOUT | 11.3 | 15004.7 | 15016 | 17215 | 5159135 |
| 95 | LCL638+1.010.p | ResourceOut | 15.1 | — | HARD_TIMEOUT | 0 | 0 | 0 | 0 | 0 |
| 96 | SYN945+1.p | Theorem | 0.0 | 1 | REFUTED | 0.2 | 0.2 | 0.4 | 3 | 3 |
| 97 | SYN480+1.p | Theorem | 9.7 | 101269 | TIMEOUT | 34.9 | 15022.6 | 15057.6 | 23408 | 377617 |
| 98 | SWB003+4.p | Theorem | 0.0 | 68 | REFUTED | 1.2 | 0.9 | 2.1 | 110 | 248 |
| 99 | NUN066+1.p | ResourceOut | 15.1 | — | REFUTED | 21.8 | 91.5 | 113.3 | 1716 | 35178 |
| 100 | SYN468+1.p | Theorem | 10.8 | 180722 | TIMEOUT | 22.5 | 15014.5 | 15037 | 31649 | 1524336 |

## FOF with equality (FO theorems)

Source list: `tptp-fof-fo-eq-thm.txt (5589)`. Rows in seed-42 sample order.

| # | Problem | E status | E time(s) | E given | Ours result | clausify(ms) | prover(ms) | total(ms) | given | derived |
|--:|---|---|--:|--:|---|--:|--:|--:|--:|--:|
| 1 | COM130+1.p | Theorem | 0.0 | 529 | REFUTED | 2249.6 | 494.2 | 2743.8 | 919 | 11757 |
| 2 | LCL466+1.p | ResourceOut | 15.1 | — | TIMEOUT | 19.8 | 15008.2 | 15028 | 12867 | 3048831 |
| 3 | LAT369+4.p | ResourceOut | 15.0 | — | SKIPPED | 0 | 0 | 0 | 0 | 0 |
| 4 | SET798+4.p | ResourceOut | 15.1 | — | REFUTED | 21.5 | 21 | 42.5 | 547 | 4260 |
| 5 | KLE140+1.p | Theorem | 0.1 | 3973 | TIMEOUT | 1.6 | 15017.8 | 15019.3 | 1839 | 3043847 |
| 6 | LCL500+1.p | Theorem | 3.0 | 56948 | REFUTED | 17.4 | 425.3 | 442.7 | 1198 | 81974 |
| 7 | SWV083+1.p | Theorem | 0.0 | 1 | REFUTED | 18.3 | 8.4 | 26.7 | 287 | 1597 |
| 8 | SWW251+1.p | ResourceOut | 15.1 | — | TIMEOUT | 34.7 | 15031 | 15065.7 | 16990 | 2127739 |
| 9 | SWC027+1.p | Theorem | 0.0 | 135 | REFUTED | 182.7 | 79.3 | 261.9 | 1493 | 6366 |
| 10 | SET694+4.p | ResourceOut | 15.1 | — | TIMEOUT | 1.6 | 15002.5 | 15004.1 | 8313 | 4489663 |
| 11 | SET768+4.p | ResourceOut | 15.1 | — | TIMEOUT | 81.6 | 15012.1 | 15093.7 | 11052 | 4231806 |
| 12 | LAT343+2.p | ResourceOut | 15.1 | — | SKIPPED | 0 | 0 | 0 | 0 | 0 |
| 13 | TOP047+2.p | ResourceOut | 15.0 | — | SKIPPED | 0 | 0 | 0 | 0 | 0 |
| 14 | GEO655+1.p | Theorem | 1.7 | 22585 | HARD_TIMEOUT | 0 | 0 | 0 | 0 | 0 |
| 15 | SCT145+1.p | ResourceOut | 15.1 | — | TIMEOUT | 309.4 | 15049.3 | 15358.7 | 12690 | 1613443 |
| 16 | SEU316+1.p | ResourceOut | 15.1 | — | TIMEOUT | 30.6 | 15003.6 | 15034.2 | 28199 | 534412 |
| 17 | MGT061+1.p | Theorem | 0.1 | 779 | TIMEOUT | 30 | 15007.8 | 15037.9 | 7015 | 5754383 |
| 18 | GEO536+1.p | ResourceOut | 15.1 | — | TIMEOUT | 439.8 | 15070.9 | 15510.6 | 12054 | 2418203 |
| 19 | NUM726+4.p | ResourceOut | 15.1 | — | TIMEOUT | 22.9 | 15023.2 | 15046.2 | 20436 | 1177297 |
| 20 | LAT347+1.p | Theorem | 0.2 | 6306 | REFUTED | 5.7 | 296.3 | 302 | 3895 | 12924 |
| 21 | NUM544+1.p | ResourceOut | 15.1 | — | TIMEOUT | 11.7 | 15003.6 | 15015.2 | 13065 | 485071 |
| 22 | NUM430+1.p | Theorem | 0.0 | 189 | TIMEOUT | 2.1 | 15001.4 | 15003.5 | 12423 | 416135 |
| 23 | GEO283+1.p | ResourceOut | 15.1 | — | TIMEOUT | 115.1 | 15012.7 | 15127.8 | 17052 | 137380 |
| 24 | SEU069+1.p | ResourceOut | 15.1 | — | TIMEOUT | 6.3 | 15003.6 | 15010 | 19964 | 2915465 |
| 25 | NUM332+1.p | ResourceOut | 15.0 | — | TIMEOUT | 4.7 | 15004.3 | 15009 | 23470 | 69310 |
| 26 | LAT287+3.p | ResourceOut | 15.0 | — | SKIPPED | 0 | 0 | 0 | 0 | 0 |
| 27 | KLE020+2.p | ResourceOut | 15.1 | — | TIMEOUT | 13 | 15053.9 | 15066.9 | 1310 | 3086700 |
| 28 | SWC187+1.p | Theorem | 0.1 | 2570 | TIMEOUT | 78.3 | 15011.9 | 15090.2 | 21455 | 634478 |
| 29 | RNG109+4.p | Theorem | 0.2 | 6560 | REFUTED | 10.8 | 219.4 | 230.2 | 2222 | 22898 |
| 30 | SET723+4.p | ResourceOut | 15.1 | — | TIMEOUT | 870.7 | 15112 | 15982.7 | 13903 | 4129788 |
| 31 | TOP035+3.p | ResourceOut | 15.0 | — | SKIPPED | 0 | 0 | 0 | 0 | 0 |
| 32 | LAT382+1.p | Theorem | 0.0 | 82 | REFUTED | 2.6 | 6 | 8.6 | 190 | 427 |
| 33 | SWW271+1.p | Theorem | 0.5 | 12398 | TIMEOUT | 35.1 | 15024.2 | 15059.4 | 16423 | 2325054 |
| 34 | NUM322+1.p | Theorem | 0.4 | 8228 | REFUTED | 2.4 | 11103.8 | 11106.2 | 19037 | 65175 |
| 35 | TOP038+2.p | ResourceOut | 15.0 | — | SKIPPED | 0 | 0 | 0 | 0 | 0 |
| 36 | LCL475+1.p | ResourceOut | 15.1 | — | TIMEOUT | 4.2 | 15011.4 | 15015.7 | 4763 | 1938790 |
| 37 | SWC001+1.p | Theorem | 0.0 | 98 | REFUTED | 85.1 | 15.9 | 101 | 468 | 1061 |
| 38 | SWC206+1.p | Theorem | 0.0 | 126 | REFUTED | 69.2 | 16.2 | 85.5 | 583 | 1544 |
| 39 | SEU442+1.p | ResourceOut | 15.1 | — | TIMEOUT | 115.6 | 15046.1 | 15161.7 | 14894 | 1543523 |
| 40 | SWC202+1.p | ResourceOut | 15.1 | — | TIMEOUT | 160.8 | 15023.2 | 15184 | 22223 | 646894 |
| 41 | SWC201+1.p | ResourceOut | 15.1 | — | TIMEOUT | 57.6 | 15010.3 | 15067.9 | 22153 | 561854 |
| 42 | REL049+1.p | Theorem | 0.0 | 32 | REFUTED | 1.8 | 3 | 4.8 | 23 | 123 |
| 43 | KLE146+1.p | Theorem | 0.0 | 25 | REFUTED | 0.4 | 111.8 | 112.3 | 195 | 30412 |
| 44 | HWV128+1.p | ResourceOut | 15.1 | — | SKIPPED | 0 | 0 | 0 | 0 | 0 |
| 45 | NUM292+1.p | ResourceOut | 15.0 | — | REFUTED | 2 | 12081.5 | 12083.6 | 20922 | 66931 |
| 46 | GEO616+1.p | ResourceOut | 15.1 | — | HARD_TIMEOUT | 0 | 0 | 0 | 0 | 0 |
| 47 | SEU359+2.p | ResourceOut | 15.1 | — | TIMEOUT | 718.8 | 15070.4 | 15789.2 | 26164 | 954809 |
| 48 | TOP048+2.p | ResourceOut | 15.0 | — | SKIPPED | 0 | 0 | 0 | 0 | 0 |
| 49 | KLE052+1.p | Theorem | 0.0 | 131 | REFUTED | 0.5 | 709.9 | 710.4 | 313 | 118475 |
| 50 | SEU445+4.p | ResourceOut | 15.0 | — | SKIPPED | 0 | 0 | 0 | 0 | 0 |
| 51 | NUM404+1.p | ResourceOut | 15.1 | — | REFUTED | 2.8 | 6338.9 | 6341.6 | 5420 | 1068576 |
| 52 | TOP028+1.p | Theorem | 0.1 | 2103 | REFUTED | 5.7 | 22.8 | 28.5 | 1087 | 2629 |
| 53 | SEU186+2.p | Theorem | 7.5 | 44492 | REFUTED | 17 | 1620.6 | 1637.6 | 5084 | 328216 |
| 54 | ALG212+1.p | ResourceOut | 15.1 | — | TIMEOUT | 24 | 15033 | 15057 | 494 | 1784913 |
| 55 | NUM525+3.p | Theorem | 0.0 | 801 | TIMEOUT | 3.8 | 15003.1 | 15006.9 | 18544 | 863366 |
| 56 | GEO088+1.p | ResourceOut | 15.1 | — | TIMEOUT | 4.2 | 15002.8 | 15007 | 15458 | 2967407 |
| 57 | SWC148+1.p | ResourceOut | 15.1 | — | TIMEOUT | 57.3 | 15012.3 | 15069.6 | 21124 | 507126 |
| 58 | AGT002+2.p | Theorem | 0.0 | 673 | REFUTED | 2.1 | 18.6 | 20.6 | 1061 | 1676 |
| 59 | SCT152+1.p | ResourceOut | 15.1 | — | TIMEOUT | 193 | 15042.3 | 15235.4 | 17597 | 1672216 |
| 60 | RNG105+2.p | Theorem | 0.0 | 183 | REFUTED | 4.3 | 223.6 | 227.9 | 2240 | 21629 |
| 61 | SET715+4.p | ResourceOut | 15.1 | — | TIMEOUT | 78.4 | 15010.8 | 15089.2 | 13504 | 3931412 |
| 62 | SEU402+2.p | ResourceOut | 15.0 | — | SKIPPED | 0 | 0 | 0 | 0 | 0 |
| 63 | SWC331+1.p | Theorem | 0.0 | 666 | REFUTED | 90.6 | 85.9 | 176.5 | 1908 | 11412 |
| 64 | CAT030+4.p | ResourceOut | 15.1 | — | SKIPPED | 0 | 0 | 0 | 0 | 0 |
| 65 | SWW262+1.p | ResourceOut | 15.1 | — | TIMEOUT | 33.7 | 15023.9 | 15057.6 | 15380 | 1413217 |
| 66 | NUM621+3.p | Theorem | 0.2 | 2345 | REFUTED | 23.4 | 720.3 | 743.7 | 6546 | 47842 |
| 67 | KLE023+1.p | ResourceOut | 15.1 | — | TIMEOUT | 4.9 | 15048.6 | 15053.5 | 1269 | 2807503 |
| 68 | SWB091+1.p | ResourceOut | 15.0 | — | TIMEOUT | 345.3 | 15048.5 | 15393.8 | 30802 | 667559 |
| 69 | SEU296+1.p | ResourceOut | 15.1 | — | TIMEOUT | 4 | 15002 | 15006 | 20064 | 664735 |
| 70 | SEU211+1.p | ResourceOut | 15.1 | — | TIMEOUT | 1.7 | 15004.5 | 15006.2 | 1674 | 1025592 |
| 71 | LAT351+4.p | ResourceOut | 15.0 | — | SKIPPED | 0 | 0 | 0 | 0 | 0 |
| 72 | SEU257+2.p | ResourceOut | 15.1 | — | TIMEOUT | 29.1 | 15010.9 | 15039.9 | 20548 | 1971357 |
| 73 | GEO447+1.p | ResourceOut | 15.1 | — | SKIPPED | 0 | 0 | 0 | 0 | 0 |
| 74 | LAT361+1.p | ResourceOut | 15.1 | — | TIMEOUT | 14.3 | 15005.8 | 15020.1 | 21368 | 1446207 |
| 75 | SWC383+1.p | ResourceOut | 15.1 | — | TIMEOUT | 99.4 | 15015.8 | 15115.2 | 22772 | 791053 |
| 76 | SET069+1.p | ResourceOut | 15.1 | — | TIMEOUT | 1.9 | 15006 | 15007.9 | 12965 | 2810362 |
| 77 | KLE008+1.p | ResourceOut | 15.1 | — | TIMEOUT | 8.1 | 15003.1 | 15011.2 | 1165 | 2770422 |
| 78 | SEU224+2.p | Theorem | 0.1 | 1914 | TIMEOUT | 28.5 | 15009 | 15037.5 | 19654 | 2023695 |
| 79 | SWB077+1.p | ResourceOut | 15.1 | — | TIMEOUT | 370.4 | 15046.3 | 15416.7 | 30383 | 600645 |
| 80 | SWC012+1.p | Theorem | 0.0 | 533 | REFUTED | 73.5 | 1850 | 1923.4 | 7146 | 90916 |
| 81 | SWV474+1.p | ResourceOut | 15.1 | — | TIMEOUT | 3678.6 | 15385.8 | 19064.3 | 7580 | 7044090 |
| 82 | SEU417+4.p | ResourceOut | 15.0 | — | SKIPPED | 0 | 0 | 0 | 0 | 0 |
| 83 | SEU442+2.p | ResourceOut | 15.1 | — | SKIPPED | 0 | 0 | 0 | 0 | 0 |
| 84 | NUN084+2.p | Theorem | 0.0 | 179 | REFUTED | 4 | 10.4 | 14.4 | 306 | 1278 |
| 85 | SEU230+3.p | Theorem | 0.0 | 73 | REFUTED | 2.1 | 19 | 21.1 | 372 | 2623 |
| 86 | SWX062+1.p | ResourceOut | 15.1 | — | TIMEOUT | 54.7 | 15013.1 | 15067.8 | 19454 | 2199286 |
| 87 | SWC081+1.p | Theorem | 0.2 | 6014 | TIMEOUT | 70 | 15011.8 | 15081.8 | 23915 | 694776 |
| 88 | NUM344+1.p | ResourceOut | 15.0 | — | TIMEOUT | 2 | 15003.9 | 15005.8 | 25795 | 71360 |
| 89 | SWX056+1.p | ResourceOut | 15.1 | — | TIMEOUT | 34.2 | 15009.5 | 15043.7 | 16450 | 2408721 |
| 90 | SEU451+2.p | ResourceOut | 15.1 | — | SKIPPED | 0 | 0 | 0 | 0 | 0 |
| 91 | SEU287+1.p | ResourceOut | 15.1 | — | TIMEOUT | 610.9 | 15068.9 | 15679.8 | 5107 | 1378326 |
| 92 | SEU197+1.p | ResourceOut | 15.1 | — | TIMEOUT | 9.8 | 15018.7 | 15028.5 | 1308 | 1051845 |
| 93 | COM019+4.p | Theorem | 2 | 21312 | TIMEOUT | 16.4 | 15006.3 | 15022.8 | 21812 | 1521116 |
| 94 | HAL002+1.p | Theorem | 0.0 | 259 | TIMEOUT | 4.7 | 15002.8 | 15007.5 | 23874 | 1104316 |
| 95 | SET988+1.p | Theorem | 1.8 | 35173 | REFUTED | 4.3 | 13501.8 | 13506.1 | 1636 | 962664 |
| 96 | SWV411+1.p | Theorem | 0.0 | 52 | TIMEOUT | 3.7 | 15016.8 | 15020.5 | 490 | 1417145 |
| 97 | SEU392+2.p | ResourceOut | 15.0 | — | TIMEOUT | 530.2 | 15075.7 | 15606 | 28348 | 729332 |
| 98 | SEU198+1.p | Theorem | 0.0 | 277 | REFUTED | 1.4 | 8.5 | 9.9 | 259 | 1400 |
| 99 | KLE085+1.p | Theorem | 0.0 | 26 | REFUTED | 0.5 | 119.8 | 120.3 | 209 | 27026 |
| 100 | SWC338+1.p | ResourceOut | 15.1 | — | TIMEOUT | 221.2 | 15035.2 | 15256.5 | 20616 | 668389 |
