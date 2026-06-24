# Plan: proof reconstruction into Lisa `SCProof`

Status: **design, not implemented.** This is the remaining Phase-1 deliverable (`Reconstruction.scala`).

## Goal & output
Turn a refutation — the empty clause `□` plus its `Justification` DAG — into a kernel `SCProof` whose
**imports are the input clause-sequents** and whose **conclusion is the empty sequent** `⊢`
(`Sequent(∅, ∅)`), then validate it with `SCProofChecker`. Clauses are sequents (negative atoms on the
left, positive on the right — the bridge's convention), so no explicit negation appears.

## Kernel API (confirmed in `lisa.kernel.proof`)
- `SCProof(steps: IndexedSeq[SCProofStep], imports: IndexedSeq[Sequent])`; imports are referenced by
  **negative** index (`-1` = `imports(0)`, `-i` → `imports(-i-1)`), steps by their non-negative index.
- `Cut(bot, t1, t2, phi)`: `t1 = Γ ⊢ Δ, φ` and `t2 = φ, Σ ⊢ Π` ⟹ `Γ, Σ ⊢ Δ, Π`. **φ on the right of
  `t1`, on the left of `t2`.**
- `InstSchema(bot, t1, subst: Map[Variable, Expression])`: free-variable instantiation of premise `t1`
  — exactly the "Instantiate of free variables".
- `Restate(bot, t1)`: OL-rewrite to an equivalent sequent (for no-op steps).
- `SCProofChecker` validates a proof; `Sorry(bot)` is the escape hatch for any unreconstructed step.

## Step mapping (DAG node → proof step)
| Justification | Reconstruction |
|---|---|
| **Input** | the user's exact sequent as an **import**, then an `InstSchema` renaming its variables to the canonical naming; `ref` = that step (skip it and reference the import directly when the clause is ground). |
| **Factoring(parent, i, j)** | `InstSchema(bot, ref(parent), σ)`, `σ = mgu(atom_i, atom_j)`; literals `i`,`j` collapse in the set-sequent. |
| **Resolution(left, i, right, j)** | `InstSchema` left by σ, `InstSchema` right by σ, then `Cut` on `φ = σ(atom)`. The **positive** side (atom on the right) is `t1`, the **negative** side `t2`. |
| **Canonicalization(parent)** | **pass-through**: sort/dedup are no-ops on set-sequents, so reuse the parent's reference (no step). |

Identity-σ fast path: when σ is the identity (propositional/ground), skip the `InstSchema` steps and
`Cut` the parents directly.

## Memoization (each clause expanded at most once)

The `Justification` graph is a **DAG, not a tree**: a clause is often a parent of several derived
clauses. Naive recursive expansion would re-expand a shared clause's entire history once per use —
exponential. Reconstruction must emit **one proof step (or import) per clause**, and every consumer
references it by its single index. This is exactly the sharing `SCProof`'s index references give us.

- Keep a memo `mutable.Map[clauseId, Int]` from a clause's identity to its **proof reference** (a
  negative import index for `Input`, a non-negative step index otherwise).
- `refOf(c)`: if `c` is memoized, return the cached index; else reconstruct it (its parents first),
  emit its step(s), cache and return the index. Inputs reconstruct as an import + a rename `InstSchema`
  and memoize to that step (or to the bare import when ground).
- **What is *not* memoized:** the per-use `InstSchema`. A clause `C` used in two resolutions is
  instantiated by **different** unifiers there, so each use emits its own `InstSchema(refOf(C), σ_k)`.
  Memoization shares `C`'s *derivation* (`refOf(C)`), which is the expensive part; the per-use
  instantiation is a single cheap step that necessarily differs by σ.
- Net size: `O(#clauses)` derivation steps + `O(#edges)` per-use `InstSchema`/`Cut` steps — linear in
  the DAG, never re-expanding a shared subproof.

## Engine 1 — recompute σ
Unifiers were deliberately not stored, so per Resolution/Factoring, re-unify the recorded literals'
atoms with the existing `Trail` (two scopes 0/1 for resolution, one for factoring) and read the
binding off the trail. Same deterministic mgu, no storage.

## Engine 2 — internal ↔ kernel translation
- **Symbols:** internal code → `Signature.info(code)` → `(name, arity, isPredicate)` → kernel
  `Constant` of the right sort; equality code 0 → `K.equality`.
- **Variables:** a per-clause bijection *internal var number ↔ kernel `Variable`*, with
  **clause-id-prefixed names** so any two clauses are automatically standardised apart (which keeps
  the σ-translation for `Cut` clash-free). **Every** clause — input and derived — uses this one
  canonical scheme; inputs reach it via their rename `InstSchema`, so there is no input/derived split.
  - **Input clauses:** the import is the user's **exact** sequent; the per-input rename `InstSchema`
    maps its original variables to the canonical ones, using the per-input var map the bridge records.
  - **Derived clauses:** the kernel sequent must be **exactly** `substitute(parentSeq, σ_kernel)` (what
    the checker recomputes), so it uses the σ-application's variable names. The fiddly bit is recovering
    which internal var of the resolvent matches each surviving `(scope, parentVar)` — the `Applier`'s
    renumbering. Recommended: have `Inference.resolve`/`factor` **record that renaming** (cheap);
    fallback: replay the `Applier`'s deterministic first-appearance numbering during reconstruction.

## Driver
1. From `□`, reconstruct via `refOf` (post-order with the memo), so parents precede children and each
   clause is expanded once.
2. `Input` clauses populate `imports` (memoized to their negative index on first encounter).
3. Each `refOf` call appends the clause's step(s) and records its index; the final `Cut` for `□`
   produces `Sequent(∅, ∅)`, the proof's conclusion.
4. Run `SCProofChecker`; return the proof (or fall back to `Sorry` per step on a gap, so partial
   reconstruction stays inspectable).

## Supporting changes
- **`Bridge`:** return the per-input-clause variable map (internal var ↔ original kernel `Variable`),
  so imports are the user's exact sequents and the rename `InstSchema` can be built. (Adopted — this is
  the small Bridge edit.)
- **`Core`:** symbol inversion is already public via `Signature.info`; no change needed.
- Optionally have `resolve`/`factor` expose the `Applier` renaming for derived clauses, else replay it.
- **New `Reconstruction.scala`:** `def reconstruct(empty: Clause, …): SCProof` (or
  `Either[String, SCProof]`), with the memo and the `refOf` recursion.

## Testing
- Reconstruct for the existing refutation tests (`{P},{¬P}`, the FO chain, the factoring case) and a
  few SYN baseline problems; assert `SCProofChecker` accepts each with conclusion `⊢`.
- Assert the proof's `imports` equal the input sequents.
- A DAG-sharing check: a problem where one clause feeds several resolvents should yield **one** step
  for that clause (memo working), not duplicates.

## Scope / risks
- **Imports are exact:** the per-input rename `InstSchema` keeps imports syntactically identical to the
  user's original sequents while everything downstream uses canonical variable names — no alpha gap at
  the import boundary.
- **Canonicalization-as-no-op holds only in Phase 1.** Once Phase-2 simplifications (subsumption,
  demodulation) are recorded via `Justification`, each needs a real reconstruction step — the framework
  (per-clause sequent + memoized ref, topological walk) extends to them.
- The variable-renumbering alignment (engine 2, derived clauses) is the one genuinely fiddly piece;
  recording the `Applier` renaming removes it.
