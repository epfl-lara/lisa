# Plan: σ-maximality (and the deferred deref-aware KBO)

Status: **design, not implemented.**

## What & why

**σ-maximality** is the inference-time ordering filter: after unification, re-check that the resolved
literal is still maximal *under the unifier σ* (the precise Bachmair-Ganzinger condition), pruning
inferences that clause-level selection at activation could not rule out. Without it the loop
**over-generates but stays sound and complete** — so this is an **efficiency** filter, added when we
want tighter generation, not a correctness fix.

Evaluating the KBO under σ can be done two ways:

- **(A) Full materialization** — build `σ(clause)` as concrete terms (via `Trail.applier`), compare
  with the **existing concrete KBO**. **Chosen** for the near term: no new KBO code, and materialised
  images are hash-consed + weight-cached in our `TermBank` — i.e. the Vampire-flavoured
  materialise-and-reuse approach, which our term bank already supports.
- **(B) Lazy deref-aware KBO** — compare under the trail without materialising. **Deferred, possibly
  to Phase 4** (see the second half of this doc): it only earns its keep once superposition + term
  indexing produce huge numbers of short-circuiting ordering checks, where materialising on every
  check is wasteful.

Note we are already on Vampire's side structurally: the **two-scope / banks** trail (vs E's
rename-apart) and a **hash-consed, weight-cached** term bank. Approach A leans on exactly those.

---

## Approach A — σ-maximality via full materialization (the plan)

### When the check applies

Re-check **only the positive resolved literal**. The negative side is eligible *by selection*
(`CompleteBest`'s negative route selects one negative unconditionally); re-checking its maximality
would wrongly reject valid inferences. A *selected positive* can only have come from the maximal
route, so the positive resolved literal is exactly the one whose σ-maximality must still hold.

### Single-instantiation structure (don't do the work twice)

The naïve flow instantiates each surviving literal **twice** — once to build `σ(clause)` for the KBO
check, once to build the resolvent. Avoid it by materialising each literal's σ-image **once** into a
shared array, reused for both the check and the clause:

```scala
// after unify succeeds, σ is in the trail
val applier = trail.applier()                 // ONE applier ⇒ consistent variable renumbering
val instLits: Array[Literal] =
  clause.literals.map(l => mkLiteral(applier.apply(atomOf(l), scope), isPositive(l)))  // each σ-image built ONCE

if positiveResolved && !maximalUnder(kbo, instLits, i) then { trail.restore(saved); return None }

val out = concat(instLits without i1, otherSurvivors without i2)   // REUSE instLits — no re-instantiation
Some(mkClause(out, Justification.Resolution(...)))
```

- `maximalUnder(kbo, instLits, i)` = no `j ≠ i` with
  `kbo.compare(atomOf(instLits(j)), atomOf(instLits(i))) == Gt` — the **concrete** KBO on the
  already-materialised atoms.
- One `applier` for all literals keeps variable renumbering consistent, so the surviving subset is a
  valid clause and the check's atoms share one namespace.
- Maximality is **within a clause**, so only the positive side's clause is fully materialised; the
  partner materialises **survivors only** (its resolved negative literal need not be instantiated).
- Do the check **before** `mkClause`, so a rejected inference also skips the clause allocation / id /
  justification.
- **Early-reject**: compare `σ(i)` against `σ(j)` lazily and bail on the first dominator (materialising
  less on failure); on success the whole clause is already materialised → reused for the resolvent. So
  no literal is ever instantiated twice, and on failure we instantiate fewer.

Net cost (passing case): `|positive-clause| + |negative-survivors|` instantiations — the only "extra"
over building the resolvent alone is the single positive resolved literal used as the comparison
baseline.

### Wiring

`Inference.resolve` / `factor` gain a `KBO` parameter (the `Discount` loop owns the `KBO`, as it would
for `CompleteBest`). `Applier` and `mkClause` are unchanged; we hoist the per-literal `apply` into the
shared `instLits` array and slice it. Factoring: the factored-upon positive literal gets the same
σ-maximality check; factoring on negatives (selected) needs none.

### Status

Efficiency only; the loop is sound and complete without it, so it is not required to finish Phase 1.
Add when we want tighter generation.

---

## Approach B — deref-aware (lazy) KBO  *(deferred — possibly Phase 4)*

A KBO that compares two terms **under the trail's bindings without materialising** (E's `DerefType` /
Vampire's `AppliedTerm`).

**Why deferred:** it only pays off where there are huge numbers of short-circuiting ordering checks
under substitution — **superposition / demodulation (Phase 3)** and **term indexing (Phase 4)** —
where materialising on every check is wasteful. Until then, Approach A reuses work and leans on the
cached-weight bank, so it dominates for the σ-maximality use. The E-vs-Vampire **mechanism** choice
(below) is best made *then*, with indexing requirements in hand; given our scope/bank model we would
likely lean Vampire.

**E vs Vampire (the choice to make later):**
- **E** chases `binding` fields **in place**, no materialisation; variables are uniquely named
  (rename-apart upstream) so there is **no scope** in comparison — its balance array is `vb[-f_code]`.
- **Vampire** wraps each side in an `AppliedTerm` (`term` + `applicator` + `aboveVar`), materialising
  each touched variable's image into **shared, weight-cached** terms; one KBO serves many substitution
  backends (unifier, matcher, indexing). `aboveVar` = single-step deref, valid because its images are
  substitution-closed.
- **Our trail is triangular**, so a lazy walk must **chase to head** (≈ E's `DEREF_ALWAYS`); the
  `aboveVar` single-step optimisation does **not** apply.

**Design sketch if/when we build it:**
- **Single parameterized path** (not duplication): one set of methods over a `(term, scope)` view —
  reuse the packed `term<<32 | scope` that `Trail.deref` returns — plus a nullable `trail` and an
  `inline derefView(t, scope, trail)` that is the identity when `trail eq null`. The public
  `compare(s, t)` becomes the `trail = null` wrapper. This matches Vampire's `AppliedTerm` / E's
  `DerefType` (one path that degenerates to the no-substitution case at ~zero cost) and avoids two
  copies of the tupling algorithm drifting.
- **Two-scope variable identity** is the *sole delta from E*: `vb` keyed by `globalId = (varNum<<1) |
  scope` instead of E's `vb[-f_code]`. Everything else (dense array + watermark reset, ground fast
  path, variable-condition counts) is identical to our existing concrete KBO. We keep scopes because
  our Phase-0 trail is bank-based (Vampire-style) — switching to rename-apart to drop scope would mean
  reworking the tested `Trail`/`unify`/`resolve`, not worth it for the KBO alone.
- **Ground fast path survives**: syntactically-ground subterms are σ-invariant → cached weight in O(1)
  (matches Vampire's `kboWeight` cache; better than E, which re-traverses).
- **Occurs-under-σ**: `containsVarUnder` deref-walk (ground subterm ⇒ `false` fast).
- **Unidirectional `greaterUnder`**: maximality only ever asks "is `lⱼ ≻ lᵢ`?", so add a unidirectional
  greater (Vampire's `compareUnidirectional` / E's `KBO6Greater`) — cheaper than the full 4-valued
  compare and the natural primitive for both maximality and demodulation.
- **Testing**: differential oracle against materialisation — `compareUnder(s@0, t@1, trail)` ==
  `compare(applier(s@0), applier(t@1))` over random terms + random unifiers; plus the `trail = null`
  wrapper == the old concrete `compare`.
