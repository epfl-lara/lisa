# Prover heuristics — E and Vampire, and where we stand

Source-grounded survey of how **E** and **Vampire** make their heuristic decisions (from the read-only
clones under `othersolvers/eprover/` and `othersolvers/vampire/`), followed by an inventory of what **our**
solver already does and what it could do next, in order of importance.

All `che_*`, `cco_*`, `Kernel/*`, `Saturation/*`, `Shell/*` line references are into those two clones; all
`*.scala` references are into this directory.

---

## Part 1 — Observations on E and Vampire

Both are superposition provers running the **given-clause loop** over an *active* set (kept fully
inter-reduced and indexed) and a *passive* set (waiting to be processed). Almost every heuristic is a policy
attached to one step of that loop: **which passive clause to activate**, **which literals of it are open to
inference**, **how terms are ordered**, **what simplifications run**, and — above the loop — **preprocessing**
and **strategy scheduling**.

### 1.1 Clause (given-clause) selection — the central lever

The core tension: **age** (oldest-first ≈ breadth-first, fair, complete) vs **weight** (lightest-first ≈
greedy best-first, fast but starves). Both provers interleave several priority queues by a fixed integer
ratio.

**E — Heuristic Control Block (HCB).** The passive set is *N* parallel priority queues, each a
`(weight function, priority function)` pair; every clause is scored by all N and lives in all N at once
(`che_hcb.c:873`). Selection is weighted round-robin via a cumulative-threshold counter — draw `rᵢ` clauses
from queue *i*, then advance (`che_hcb.c:903` `HCBStandardClauseSelect`). Inside a queue the key is
`(priority, weight, age)` (`ccl_neweval.c:388` `EvalCompare`): **priority** is a coarse integer override
(goals-first, watchlist-first, SOS-defer…), **weight** the fine key, **age** (insertion counter) the final
tiebreak.
- **Weight** = Σ over literals of a symbol-counted term weight `vweight·#vars + fweight·#syms` (defaults 1, 2),
  with positive-literal / maximal-literal / maximal-side multipliers (`ccl_eqn.c:3122` `LiteralWeight`).
  `Clauseweight` fixes the maximal multipliers to 1; `Refinedweight` exposes them.
- The default HCB is `Default = (3·rweight21_a, 1·rweight21_g)` (`che_proofcontrol.c:35`): 3 clauses
  "non-goals-first, lightest", then 1 "goals-first, lightest". The textbook age:weight ratio appears as
  `StandardPG = (5·weight21_f, 1·fifo_f)` — 5 by weight, 1 by pure FIFO.
- Modern auto strategies add **conjecture-relative weights** (`ConjectureRelativeSymbolWeight`,
  `che_funweights.c`): symbols occurring in the goal are scaled *lighter*, biasing search toward the goal,
  plus a FIFO slice against starvation — e.g. a 5-queue `1:4:1:1:4` mix.
- **Priority functions** (`che_prio_funs.c`) are the cheap coarse override: `PreferGoals`, `PreferWatchlist`,
  `SimulateSOS`, `ByCreationDate` (clean FIFO), `PreferGroundGoals`, etc.

**Vampire — Age-Weight Ratio (AWR) + LRS.** Two queues (age, weight), one signed **balance** counter
alternating them at `--age_weight_ratio` (default **1:1**, `AWPassiveClauseContainers.cpp:199`). Weight carries
a **goal knob**: `--nongoal_weight_coefficient` (default **10**, `Clause.cpp:610`) multiplies non-goal clauses'
weight by 10, so conjecture-derived clauses look 10× lighter and are picked far earlier.
- **LRS (Limited Resource Strategy)** — Vampire's signature: periodically extrapolate the activation rate
  (`reachable ≈ activations/elapsed × time_left`, `LRS.cpp:132`), simulate the AWR selection to find the
  age/weight horizon, and **discard passive clauses that can't be reached before timeout**. Incomplete but
  spends the whole budget on the reachable frontier — the default saturation algorithm.
- **Layered split queues** (Gleiss–Suda, `PredicateSplitPassiveClauseContainers.cpp`) optionally bucket passive
  by a feature (theory content, AVATAR-split count, SInE level, #positive literals); a weighted round-robin
  picks a bucket, then AWR runs inside it.

**Convergence:** E = "N queues, integer ratio, per-queue weight+priority"; Vampire = "2 queues + AWR, plus LRS
pruning and optional feature-layered buckets." Same idea; E generalizes the *number* of queues, Vampire adds
*resource-aware pruning*.

### 1.2 Literal selection

Restricting inferences to *selected* literals (Bachmair–Ganzinger: select a negative literal, **or** all
maximal literals) sharply cuts branching. Selecting a **big/complex negative literal** is maximally
restrictive.
- **E** (`che_litselection.c`, ~130 strategies): code default is `NoSelection`, but auto-mode uses workhorses
  like `PSelectComplexExceptUniqMaxHorn` — select the largest complex maximal negative literal, but select
  *nothing* on unique-maximal Horn clauses (where selection hurts). "Diff weight"
  `100·(eq-side size difference) + weight` favours lopsided literals like `f(x) ≠ a`. Whole families avoid
  selecting a negative literal that shares a predicate with a positive one (`SelectMaxLComplexAvoidPosPred`).
- **Vampire** (`Kernel/LiteralSelector.cpp`): integer `--selection` codes, default **10** = complete
  best-literal by quality chain `ColoredFirst → NegativeEquality → MaximalSize → Negative → Lex`
  (`LiteralComparators.hpp`). **Sign convention:** negative codes reverse polarity; magnitude ≥ 1000 = the
  *incomplete/greedy* variant (no completeness fallback). **Lookahead** (code 11) picks the literal that
  generates the *fewest* actual inferences against the live indexes, evaluated lazily
  (`LookaheadLiteralSelector.cpp:174`).

### 1.3 Term ordering, precedence & weight generation

The reduction ordering is what makes superposition terminate and stay complete.
- **KBO vs LPO:** both default to **KBO** (cheap, linear). E always uses KBO6 in auto-mode (diversity comes
  from the *schedule*, not a per-problem classifier, `che_to_autoselect.c:57`); Vampire's `auto_kbo` resolves
  to KBO unless arithmetic is present (`Options.cpp:3564`).
- **Precedence generation** (symbol order): **E default `unary_first`** (unary symbols biggest,
  `che_to_precgen.c:138`); **Vampire default `frequency`** (rare symbols large, `Ordering.cpp:767`,
  `Options.cpp:2397`). Both offer arity / inv-arity / frequency / inv-frequency / occurrence variants; E's
  `invfreqhack` (rare-large but frequent-unary maximal) is common in its schedules. **Occurrence order is the
  weak default both provers deliberately avoid.**
- **KBO weights:** E default `firstmaximal0` (all 1 except the first maximal symbol → 0, keeping KBO
  admissible, `che_to_weightgen.c:333`); Vampire default `const` (all function symbols 1, `KBO.cpp:937`).
  Both allow arity/precedence/frequency-derived weights and per-symbol weight files; both enforce KBO
  admissibility.

### 1.4 Saturation algorithm & simplification/redundancy

**Loop variants** differ only in *what is visible to simplification*:
- **Discount** — only *active* clauses simplify (small indexes, cheaper) (`Saturation/Discount.cpp:25`).
- **Otter** — active *and* passive simplify (stronger reductions, bigger indexes) (`Saturation/Otter.cpp`).
- **LRS** — Otter + resource pruning (`Saturation/LRS.hpp:27`). **Vampire's default.** E runs a DISCOUNT-style
  loop.

**Redundancy machinery** (both, similar defaults): forward subsumption (on), forward
subsumption-resolution (on), forward demodulation (on), tautology deletion, simplify-reflect. **Backward**
demodulation/subsumption default **off** (expensive — re-scan kept clauses). Vampire extras: **global
subsumption** (ground-abstract into a SAT solver, delete a clause whose grounding is already implied,
`Inferences/GlobalSubsumption.cpp`), forward-subsumption-demodulation, ground joinability. E's
forward-contraction fixpoint order is precise (`cco_forward_contraction.c:242`): rewrite→NF →
remove-superfluous → re-orient → condense → simplify-reflect → subsumption → contextual-SR.

### 1.5 Clausification & preprocessing

- **CNF naming (definitional):** **Vampire default `--naming 8`** (`Shell/Naming.cpp`, `Options.cpp:630`) uses
  the *same* add-under-∧ / multiply-under-∨ clause-count estimate we implemented in `FastClausify`
  (independent validation of the algorithm; they threshold at 8, we at 4). E does the equivalent in
  preprocessing.
- **On by default in Vampire, reshaping the clause set:** `updr` (unused/pure predicate-definition removal),
  `erd` (eagerly resolve `X ≠ t` disequations), naming. Opt-in: inequality splitting, equality proxy,
  blocked-clause elimination.
- **SInE axiom selection** (both, off by default): for huge axiom sets keep only axioms reachable from the
  goal via a "least-general symbol triggers the axiom" relation, transitively, with tolerance/depth/generality
  knobs (`Shell/SineUtils.cpp`; E's GSinE, `ccl_sine.c:539`). A large-theory portfolio option.

### 1.6 Big architectural heuristics

- **Vampire AVATAR** (on by default, `Saturation/Splitter.cpp`) — split clauses into variable-disjoint
  components named by SAT literals; a SAT solver picks which components are asserted, FO saturation runs only
  on that branch, empty-up-to-splits clauses become SAT conflicts, SAT UNSAT = refutation. Two-solver
  architecture; arguably Vampire's single biggest advantage. Includes greedy model *minimization*
  (`SAT/MinimizingSolver.cpp`) to assert as few components as possible.
- **E watchlist** (`cco_proofproc.c:394`) — a user/goal-supplied set of "interesting" clauses; clauses hitting
  it get selection priority. E's main explicit goal-direction mechanism, alongside conjecture-relative
  weights.
- **Set-of-support** (both, off by default): seed active with axioms, drive from the goal.

### 1.7 Strategy scheduling — neither prover runs one fixed configuration

This is where most competition performance comes from.
- **E `--auto-schedule`** (`che_new_autoschedule.c`, `schedule.vars`): compute a short feature-class string
  (Horn/unit/general, equality none/some/pure, groundness, arity, order…) and look up a **learned
  class→schedule table** (419 configs) by exact match or minimal edit distance. Each schedule = a time-sliced
  sequence of full strategies.
- **Vampire portfolio/CASC** (`CASC/PortfolioMode.cpp`, `Schedules.cpp`): scan the problem into a `Property`
  (9 CASC categories + 64-bit feature mask, `Shell/Property.cpp:164`), branch to a schedule family, fork `N`
  workers running encoded strategies (each budgeted by trailing time or `i=` mega-instructions), first to exit
  0 wins; an exhausted schedule reruns with all limits doubled.

**Recurring lesson:** raw calculus + indexing gets a fast engine; **clause selection + literal selection + a
portfolio** are what convert speed into solved problems.

---

## Part 2 — Where our solver stands: what it does, and what it could do

Ordered by importance (expected impact on problems solved), with effort noted. Several items I expected to be
gaps are in fact **already done** — listed first so the roadmap is honest.

### Already implemented

- **Age/weight clause selection** (Vampire-style AWR). Two lazy-deletion queues (`byAge` FIFO, `byWeight`
  min-heap on `(weight, id)`) with a signed `balance` counter, ratio `ageRatio:weightRatio` default **1:1**
  ([Discount.scala:45](Discount.scala#L45), [Discount.scala:265](Discount.scala#L265) `popGiven`). This is the
  single most important selection heuristic and it is in place.
- **Clause weight** = Σ literal KBO weights (symbol-counting), cached at construction
  ([Core.scala:303](Core.scala#L303) `mkClause`). Matches Vampire's `const`-scheme base weight.
- **Literal selection** with the real quality order: `compareLiteralQuality` = Vampire's Comparator10 minus
  colours (`NegativeEquality → MaximalSize → Negative → Lex`, [Selectors.scala](Selectors.scala)). Three
  selectors exist — `FirstNegativeSelector`, `BestLiteralSelector` (greedy, selector-1010), and
  `CompleteBestLiteralSelector` (BG-complete, selector-10). **Default is `BestLiteralSelector`**
  ([Core.scala:178](Core.scala#L178)).
- **KBO** term ordering with live per-symbol weight/precedence ([KBO.scala](KBO.scala), [Core.scala:77](Core.scala#L77)).
- **Discount** saturation loop (active-only simplification), the cheaper of the two loop variants.
- **Indexed simplification/generation:** fingerprint indices for resolution + backward demodulation, a
  **perfect discrimination tree** for forward demodulation, a **feature-vector index** for subsumption
  (Phase 5). Forward *and* backward subsumption and demodulation.
- **Single-pass definitional clausification** with polarity-sensitive selective naming, threshold 4
  ([../clausification/FastClausify.scala](../clausification/FastClausify.scala)) — the same scheme Vampire uses
  at threshold 8.

### Could do — in order of importance

1. **Symbol precedence generation (occurrence → frequency / arity).** *Biggest impact-per-effort gap.* Our
   precedence is the **interning (occurrence) order** ([Core.scala:78](Core.scala#L78),
   [Core.scala:91](Core.scala#L91)) — exactly the weak default both provers avoid. Every superposition and
   demodulation orientation depends on the precedence, so generating it by symbol **frequency** (rare-large,
   Vampire's default) or **inv-frequency/arity** (E's `invfreqhack`/`unary_first`) is a small, one-time,
   signature-level change with broad effect on equational problems. **Effort: low.**

2. **Goal-directed clause weight (nongoal coefficient / conjecture-relative).** We have **no** goal bias in
   weight (grep finds no `nongoal`/`isGoal`/conjecture-weight). Adding a per-clause "derived-from-goal" bit and
   multiplying non-goal weight (Vampire `nwc`, default 10) — or scaling goal-symbol weight down (E's
   conjecture-relative) — is cheap and both provers rely on it heavily. Needs a goal flag threaded from the
   negated conjecture through the derivation. **Effort: low–medium.**

3. **KBO weight generation.** All symbols currently share one default weight (`const` scheme). Cheap to add
   arity- or frequency-derived weights and the `firstmaximal0` admissibility trick (a weight-0 maximal unary),
   which E uses by default. **Effort: low.** (Pairs naturally with #1.)

4. **Richer clause-selection queues (E-style HCB).** We interleave exactly two queues (age, weight). Adding a
   third **conjecture-relative weight** queue and/or coarse **priority functions** (prefer-goal,
   prefer-ground-negative, SOS-defer) turns selection from 2-way into the N-queue mix E's auto strategies use.
   Builds directly on #2. **Effort: medium.**

5. **Literal-selection default & completeness.** Our default (`BestLiteralSelector`) is the **incomplete**
   greedy variant (Vampire's 1010). Vampire defaults to the **complete** best-literal (10). Consider defaulting
   to `CompleteBestLiteralSelector` (we already have it) or making it strategy-selectable, and check the
   completeness implications for our calculus. **Effort: low** (flip a default) **to medium** (tune/verify).

6. **Strategy portfolio / auto-scheduling.** The biggest *real-world* lever — how E and Vampire actually win —
   but the largest effort. Needs (a) a handful of tuned strategies (varying awr, selector, precedence scheme,
   equality on/off), (b) a problem-feature classifier (Horn/unit/equality/groundness — we already compute some
   of these), and (c) a sequential/parallel time-sliced runner. Even a hand-written 3–5 strategy schedule
   would likely move the benchmark more than any single knob. **Effort: high.**

7. **LRS-style resource pruning.** Discard passive clauses unreachable before timeout. Strong wall-clock win,
   but its natural home is Otter/LRS (passive visible to the reachability estimate); on a pure Discount loop it
   needs the same activation-rate extrapolation bolted onto our two queues. **Effort: medium–high.**

8. **AVATAR-style clause splitting.** Large architectural win on problems with variable-disjoint structure,
   but a two-solver (SAT + FO) redesign of the loop and proof reconstruction. High risk/effort; defer until the
   cheaper levers are exhausted. **Effort: high.**

9. **SInE axiom selection.** Only helps large-axiom-set problems (specific TPTP categories); a targeted win,
   not a general one. **Effort: medium.**

10. **Global subsumption, extensionality resolution, URR, ground joinability.** Incremental redundancy/​
    inference refinements. Each a modest, isolated add once the above are in. **Effort: low–medium each.**

**Summary:** our engine already has the two heuristics that matter most (age/weight selection, real literal
selection) plus strong indexing and a fast clausifier. The cheapest high-value next steps are **precedence
generation (#1)** and **goal-directed weighting (#2)** — both small, both currently at the weak default. The
largest untapped lever is a **strategy portfolio (#6)**, which is where E and Vampire get most of their solved
problems, at correspondingly higher effort.
