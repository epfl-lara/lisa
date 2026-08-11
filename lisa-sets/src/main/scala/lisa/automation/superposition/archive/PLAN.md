We are constructing a prover for problems in clausal form using ordered resolution and superposition for Lisa in Scala. We want to make it super efficient, low level, and with full proof reconstruction. We take heavy inspiration from Vampire, E and Prover9 to implement things optimally.

Phase 0 [done]: Core datastructures and utilities (terms, clauses, unification, KBO).
Phase 1 [done]: Ordered resolution via the DISCOUNT loop, factoring, and proof reconstruction into Lisa.
Phase 2 [done]: Redundancy elimination — forward/backward subsumption, unit deletion, subsumption resolution, condensation. (Demodulation is deferred to Phase 4, where it lands with equality.)
Phase 3 [done]: Clausification wiring. Connects Lisa's certified clausification
  (`lisa.automation.clausification`, entry point `CertifiedFastClausifier.certifyClausal(problem, prover)`) to
  the clausal prover (`Bridge.solve`), so a general — non-clausal — first-order Lisa sequent is proved end to
  end: clausify (screen → name → NNF → Skolemize → prenex → distribute) → refute the clauses with
  superposition → compose the clausification proof and the refutation into a single kernel `SCProof` of the
  original goal. Delivered as `Clausal` (the ε-abstraction + prover adapter) and the `Superpose` proof tactic.
Phase 4 [done]: Equality handling — superposition, demodulation (forward + backward), equality
  resolution/factoring, the equality-aware literal ordering (`Order`) and the redundancy criteria.
Phase 5 [done]: Performance — term indexing (fingerprint indices for superposition and resolution, a
  feature-vector index for subsumption, a perfect discrimination tree for demodulation), KBO precedence/weight
  generation, literal selection, and the portfolio strategies.

Phases are done one at a time and only after the previous one is complete, tested, and the user asks to
start the next. The detailed per-phase design lives in `Phase<n>.md`, written when the phase begins; those
documents are **historical** — they record the design as planned, not necessarily as it now stands. The code
and its Scaladoc are authoritative.

Current work sits past Phase 5: hardening the `Superpose` tactic and the clausification pipeline. `CodeReview.md`
holds a full review of both packages with a prioritised action list.

---

## Phase 3 — Clausification wiring (detailed plan)

**Goal.** Make the superposition prover usable on arbitrary (non-clausal) first-order Lisa sequents, with a
single certified kernel proof of the original goal — not just on pre-clausified CNF. The clausal engine
(Phases 0–2) and the certified clausifier (`lisa.automation.clausification`) already exist independently;
Phase 3 is the **integration** that joins them.

**The hand-off already exists.** `Clausification.certifyClausal(problem: Problem, prover: Problem => SCProof)`
runs the full certified pipeline and calls `prover` on the resulting clausal `Problem`
(`Problem(hypotheses: Seq[K.Sequent], conjecture: Option[K.Sequent])`), then composes the clausification
derivation with the prover's `SCProof` into one proof of the original `problem`. Our `Bridge.solve` already
takes `Iterable[K.Sequent]` (clause-sequents) and yields a refutation with `reconstructKernelProof: SCProof`
concluding the empty sequent `⊢`. So the core adapter is just:
```
Clausification.certifyClausal(problem, p => Bridge.solve(p.hypotheses, budgets) match {
  case s: Bridge.Outcome.Success => s.reconstructKernelProof
  case _ => /* no refutation: the goal is not provable in budget — fail the tactic */
})
```
The work is in the **seams**, not this line.

### Integration risks to resolve first (a short spike before committing)

1. **Clausal-output format ↔ `Bridge`'s clause converter.** `Bridge.clauseOfSequent`/`formulaToSequent`
   expect *pure clauses* (left = negative atoms, right = positive atoms; `∀` stripped; `∨` flattened;
   per-clause variable numbering). Verify the clausifier's output sequents are exactly that — in
   particular how it represents clause variables (free vars vs explicit `∀`) and **Tseitin atoms** (fresh
   predicate symbols `tsi(fv…)` — they must convert as ordinary predicates).

2. **Skolem/epsilon terms — the crux.** Lisa clausifies existentials with **Hilbert ε terms**
   (`existsEpsilonIffStatement`: `∃x.φ ⟺ φ[ε(λx.φ)/x]`), so Skolemized terms contain `ε(λx.φ)` subterms
   with *embedded lambdas* and the enclosing universals free in `φ`. Our prover is first-order over a flat,
   hash-consed term bank with no lambda support. Options to evaluate: (a) the term converter maps each
   distinct ε-term `ε(λx.φ)` to a fresh **Skolem function symbol** applied to its free variables
   (`sk_i(fv…)`) — first-order, clean, but the mapping must be consistent and invertible for
   reconstruction; (b) treat ε-headed terms opaquely as functor + children, which risks the lambda body
   leaking into unification. (a) is almost certainly the right answer. **This is the highest-risk seam and
   the first thing to prototype.**

3. **Library-theorem import discharge.** `certifyClausal`'s `SCProof` keeps five library lemmas
   (`existsEpsilonIffStatement` + four `forallAnd/Or` prenex lemmas) and the user hypotheses as *imports*.
   To get a closed Lisa theorem the lemmas must be discharged by cutting against their library proofs
   (the JOURNAL notes this is "supplied externally when wrapped as a tactic"). Phase 3 must locate/prove
   these in Lisa's library and cut them in.

### Deliverables

- **A wiring module in `superposition/`** (e.g. `Clausal.scala` / extend `Bridge`): `Problem`→refutation
  adapter (with the no-refutation/timeout failure path), the ε→Skolem-function term handling decided by the
  spike, and library-import discharge.
- **A `ProofTactic`** (mirroring `Tableau`/`Tautology`) that takes a Lisa proof sequent, builds the
  `Clausification.Problem` (hypotheses + negated conjecture), runs the adapter, and returns the certified
  proof — failing cleanly when the prover saturates (goal invalid) or hits budget.
- **Tests** in `superposition/`: end-to-end on small non-clausal **no-equality** goals (e.g. a quantified
  propositional tautology, the drinker's paradox, `∀`/`∃`-mixed validities), each **kernel-checked** to
  conclude the original sequent; plus a regression that the existing clausal path is unaffected.

### Scope boundary (important)

Per the project rule, code may only be added under `superposition/`. The clausifier in
`lisa.automation.clausification` is **read-only** here: the wiring calls its public `certifyClausal`. If the
integration needs a change there (e.g. a public Skolem-function mode, or a format tweak), **stop and ask** —
do not edit outside `superposition/`.

### Out of scope (Phase 4+)

- **Equality** in the prover (superposition/paramodulation/demodulation) — Phase 4. Clausification itself is
  equality-agnostic, so Phase-3 wiring is validated on no-equality goals; equality goals start working once
  Phase 4 lands, with no change to the wiring. — Phase 5.
