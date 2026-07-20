# Portfolio / strategy-scheduling in E and Vampire — and what it means for us

Source-grounded study of how **E** and **Vampire** turn a bag of individual strategies into a competition-winning
portfolio, from the read-only clones under `othersolvers/`. Companion to [ProverHeuristics.md](ProverHeuristics.md)
(which covers the *individual* heuristics). All `che_*`/`cco_*`/`CASC/*`/`Shell/*` references are into those clones.

---

## TL;DR — the convergent design

Both provers run an **offline-learned, class-indexed, time-sliced schedule of fully-encoded strategies**, executed by
**forking parallel workers**, **first-to-succeed wins**, and **re-run with grown budgets** if time remains. They
differ mainly in *encoding* and *how a problem is mapped to a schedule*: **E** = nearest-neighbour over a learned
feature-string → schedule table; **Vampire** = a hand-written decision tree on a computed category/property mask, with
the schedule *contents* learned. The schedule *content* is learned in both; the *router* is data-driven in E and
hand-structured in Vampire.

---

## 1. Which parameters/heuristics they vary

| Axis | E (a "conf" = a full `HeuristicParms` block) | Vampire (a positional encoded string) |
|---|---|---|
| Saturation algorithm | **fixed** DISCOUNT-style | **varied**: `sa` ∈ {lrs(def), discount, otter, fmb, z3} |
| Clause selection | HCB = list of `ratio.WeightFn(PriorityFn,…)` queues (`Default=(3·rweight21_a,1·rweight21_g)`, `che_proofcontrol.c:59`); conjecture-relative + FIFO slices | `awr` age:weight ratio (def 1:1) + `nwc` nongoal coeff (def 10) |
| Literal selection | `selection_strategy` (e.g. `PSelectComplexExceptUniqMaxHorn`) + min/max gating bounds (`che_proofcontrol.c:263`) | `s` selector code (complete 2/3/4/10/11 vs incomplete 10xx; sign reverses polarity, `Options.cpp:962`) |
| Term ordering | `ordertype` KBO6/LPO, **`to_weight_gen`**, **`to_prec_gen`** (e.g. `invfreqhack`), `che_hcb.c:571` | `to` {auto_kbo(def),kbo,lpo,qkbo,…}, `sp` symbol precedence (13 schemes, `frequency` def, `Options.cpp:2397`) |
| Simplification | context-SR, subsumption (aggressive), demod, condensing, ER, splitting (`schedule.vars:4`) | `fsr/bsr/bd`, `gs` global subsumption, `urr`, `drc`, `updr`, `gsp` |
| Axiom selection | **SInE** (`sine`) | **SInE** `ss/sd/st` + `s2a` sine-to-age |
| Preprocessing/CNF | eq-def unfolding, goal defs, naming, presat-interreduction | `nm` naming (def 8), `fde`, `tgt` twee-goal, newcnf |
| Budget / randomisation | (time fraction only) | `i=` instruction cap, `sil`, shuffling `si/rtra/rawr/rp` |

Both vary the **same conceptual core**: clause selection, literal selection, term ordering + precedence (E also
weight-gen), SInE, simplification toggles, naming. Vampire additionally varies the **saturation algorithm and
AVATAR**; E keeps one loop and expresses diversity through the HCB queues and orderings.

---

## 2. In which combinations

**E.** A **schedule = a time-sliced sequence of ~12 confs** (each ≈ 1/12 of the time), run *after* a separate
preprocessing schedule. Tables are generated into `HEURISTICS/schedule.vars` and `#include`d
(`che_new_autoschedule.c:24`): **419** distinct confs (`num_confs = 419`, header `// Found 1615 confs, using 419`),
**1358** search-class → schedule entries, **259** preproc entries. A conf is one mnemonic-named parameter block, e.g.
`G-E--_208_C12_11_nc_F1_SE_CS_SP_PS_S5PRR_S04BN`.

**Vampire.** A **schedule = an ordered `Stack<string>`** (`Schedules.hpp:23`) of encoded strategies. `CASC_2025` has
**≈ 1178 strings** across category branches, internally grouped into **escalating instruction-cap sub-schedules**
("2000Mi → 4000Mi → … → 960000Mi"). The string grammar (parsed positionally by
`Options::readFromEncodedOptions`, `Options.cpp:3385`): `<3-char sa><±selection>_<awr>_<key=value:…>_<budget>`.
Examples (verbatim from `Schedules.cpp`):
- `lrs+1011_1:1_sp=occurrence:st=6.0:sd=4:ss=included_0` — FOF champion
- `dis+1010_1:1_s2a=on:sd=3:sil=128000:ss=axioms:st=3.0:i=327:si=on_0`
- `fmb+10_1:1_i=150016:sas=cadical_0` — EPR → finite model building
**Champions** (`numWorkers/2` of them, `PortfolioMode.cpp:231`) are trimmed and **prepended**, each chosen to cover as
many problems as possible alone, run with unlimited wall time bounded only by a large `i=`.

---

## 3. Timing / when

- **Execution: both fork.** E forks one child per conf (`EGPCtrlCreate`, `cco_scheduling.c:270`) up to `max_cores`,
  launching the next as a core frees; `--serialize-schedule` forces sequential. Vampire forks up to
  `_numWorkers = min(hw_concurrency, --cores)` and keeps the pool full (`PortfolioMode.cpp:400`).
- **Per-slice budget.** E: `time_absolute = ceil(time_fraction × cores × total_limit)` (`cco_scheduling.c:221`),
  default total **300 s** (`cco_scheduling.h:53`), fractions baked into the table (mostly equal 1/N). Vampire: each
  string's `i=` mega-instructions (`sliceTime ≈ 1 + i/200` @ ~2 GHz, `PortfolioMode.cpp:541`) or a trailing wall-clock
  deciseconds field; scaled by `--slowness`.
- **Restart / exhaustion.** E is **two-phase**: preprocessing schedule → search schedule → if **> 2 s** remain
  (`RETRY_DEFAULT_SCHEDULE_THRESHOLD`), a **filtered default schedule** (default minus already-tried, times
  re-normalised, `cco_scheduling.c:390`). Vampire **rescales the whole schedule ×2 and re-runs indefinitely**
  (`rescaleScheduleLimits(…, 2.0)`, `PortfolioMode.cpp:403`), force-enabling input shuffling on repeats.
- **Winner.** First child to **exit 0** (after writing its proof/model to a temp file) wins; the parent `SIGINT`-kills
  the rest (`PortfolioMode.cpp:441`).
- **When is the schedule chosen? Once, at startup** — classification is a single pre-solve step; neither re-classifies
  adaptively mid-run.

---

## 4. On what criteria a schedule is chosen

**E — learned nearest-neighbour over a feature string.** Two classifiers each emit a fixed-width class string:
- preproc: **15-char** raw features (FO/HO, #sentences S/M/L, term/sig sizes, #preds/funcs, #defs, …),
  `che_rawspecfeatures.c:141`;
- search: **21-char** SpecFeatures (F/H; axioms U/H/G; goals U/H/G; equality N/S/P; non-ground-units; arities; depth;
  …), `SpecTypeString`, `che_clausesetfeatures.c:1526` — masked (`DEFAULT_MASK` blanks positions 5 & 12), giving keys
  like `FGHSM-FFMM31-MFFFFFNN`.
- `class_to_schedule` (`che_new_autoschedule.c:42`) picks the map key of **minimum `StrDistance`** (positional
  **Hamming + length-diff**, *not* Levenshtein, `clb_simple_stuff.c:71`); **exact match wins**, ties broken by
  **largest `class_size`** (most training problems in that bucket).

**Vampire — hand-written decision tree on a computed `Property`.** (a) `--schedule` enum picks the *family* (CASC /
CASC_SAT / SMTCOMP / SNAKE / …, `PortfolioMode.cpp:309`); (b) within a family, a hard if/else chain on `Property`
(`Schedules.cpp:5212`): `higherOrder()?` → `hasNumerals/interpreted?` → `category==UEQ?` → mask
`PR_ESSENTIALLY_BSR|GROUND?` (→ EPR/FMB) → `formulas()>0?` (FOF vs CNF). The 43-bit property mask + a hard **CASC
category decision tree** (FEQ/FNE/UEQ/PEQ/EPR/HEQ/HNE/NEQ/NNE, `Property.cpp:164`) do the branching. SMTCOMP instead
switches on the **SMT-LIB logic**.

So **E's routing is data-driven** (feature vector → nearest learned schedule); **Vampire's routing is
hand-structured** (category tree), while the schedule *contents* in each branch are learned in both.

---

## 5. Other important findings

- **Both schedules are learned offline, not hand-written.** E: header `// Found 1615 confs, using 419` + per-class
  training-set sizes. Vampire: the **"Spider"** tuner — comments like `// Improves by expected 2470 probs costing
  1998 Mi`, the champion cover-set design (`PortfolioMode.cpp:227`), and `"… as soon as we have new schedules from
  spider"`.
- **Distinct schedule *sets*** for different goals: unsat (CASC), **satisfiability** (CASC_SAT — FMB-heavy, models
  count as wins), SMT-COMP (logic-keyed), incremental/LTB, induction. E has `--satauto-schedule` similarly.
- **`--auto` vs `--auto-schedule` (E).** `--auto` classifies and runs **only the first conf** of the chosen schedule
  (one good strategy, no forking); `--auto-schedule` runs the full time-sliced, multi-core schedule.
- **Default when portfolio is off**: one strategy from current option values (Vampire `Mode::VAMPIRE`: lrs, s=10,
  awr 1:1, nwc 10, av on, sp frequency, …; E: the raw user strategy).

---

## 6. What this means for *our* prover (the in-scope path to MD #6)

We're a **single JVM process**, so the fork-parallel model is awkward — the natural fit is E's `--serialize-schedule`
mode: a **sequential, time-sliced schedule in-process**, each slice a fresh `Bridge.solve` with its own `maxMillis`,
first refutation wins, and (Vampire-style) a **budget-doubling re-run** if time remains.

**Axes we can already vary** (from `Bridge.solve`/`Discount` today):
- `ageRatio:weightRatio` (awr, currently 1:1), `nonGoalWeightCoefficient` (currently 10),
- literal selector (currently hard-wired to `CompleteBestLiteralSelector` — trivially exposable to vary),
- `precedenceScheme` (InvFrequency → Frequency / Arity / Occurrence / …),
- equality / superposition / demodulation / subsumption toggles, indexing A/B flags, clausifier naming threshold.

**Axes we lack** vs them: saturation-algorithm choice (we're DISCOUNT-only, like E — fine), KBO **weight-gen** (a
portfolio ingredient — see [ProverHeuristics.md](ProverHeuristics.md)), **SInE**, **AVATAR**, term-ordering choice
(KBO-only).

**Minimal viable portfolio:** a **fixed 3–5 strategy sequential schedule** varying `{awr, selector, precedenceScheme,
nwc, equality}` — no classifier needed to start (even a hand-picked schedule likely beats any single config). Then, as
E-style refinement, a cheap **feature classifier** (Horn/unit/equality/size — some already computed) to pick among a
few schedules, and, as the Vampire-style tail, **budget-doubling re-runs** of the whole schedule while time remains.
