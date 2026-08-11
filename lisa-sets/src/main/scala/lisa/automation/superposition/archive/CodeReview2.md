# Code review — `clausification/` + `superposition/`

**Date:** 2026-08-09 · **Scope:** ~9 500 lines of main source (44 files) and ~5 000 lines of tests (32 files).
Ten reviewers covered disjoint slices; every finding below that is marked **verified** was re-checked against the
code by hand afterwards. Findings marked *reported* are a reviewer's analysis I found credible but did not
independently re-derive.

---

## 0. Verdict

The engineering is strong and the review found no live soundness bug. Three things stand out as genuinely
above-average: the package boundary is clean and one-directional (`superposition → clausification`, with the
prover arriving as a `Problem => SCProof` callback, so the clausifier stays prover-agnostic); the calculus is a
faithful port, checked rule-for-rule against Vampire and E, with side conditions in the right places; and the
retrieval indices are sound over-approximations pinned against exact brute-force oracles rather than
smoke-tested.

The weaknesses cluster in three places, and they share a shape: **a guarantee is stated in prose, holds today
by accident of call order, and is enforced nowhere.** The clausifier's polynomial bound, the active set's
removal soundness, the reconstruction replay's variable numbering, and three index preconditions are all of
this kind. Nothing is broken; several things are one plausible refactor away from breaking silently.

The single most valuable fix is the smallest: **no test anywhere asserts `usesSorry == false`**, so the suite
cannot distinguish a real refutation from a fabricated one — in a project whose headline promise is proof
reconstruction.

---

## 1. Correctness

### 1.1 ~~[H] Nothing asserts the reconstructed proof is `Sorry`-free~~ — FIXED 2026-08-09

`SCProofChecker` returns `SCValidProof(_, usesSorry = true)` for a `Sorry` step, so `.isValid` is `true`
(`SCProofChecker.scala:805`). `grep usesSorry` across both test packages returns **zero** hits.

`SCProof(IndexedSeq(Sorry(⊢)))` therefore satisfies every assertion in `ReconstructionTest.check` and
`EqualityReconstructionTest.checkReconstructs`: valid ✓, concludes `⊢` ✓, imports ⊆ clauses ✓ (empty),
imports distinct ✓. Three test files define a `sorryProver` helper, so the construct is one copy-paste from a
real path. No main source currently emits `Sorry`, so this is a missing regression guard, not a live bug.

**Fix.** `lisa.kernel.KernelProof` (in `lisa-utils`' kernel tests, since nothing about this is specific to
this prover — `lisa-sets` already depends on `withTests(utils)`) provides two named assertions, so each call
site *states* which contract it checks rather than leaving it implied by whichever prover was passed in:

- `assertCorrectProofNoSorry` — accepted **and** `Sorry`-free. Applied to all 20 real-prover sites across
  `ReconstructionTest` (both the inline helper and the 20 SYN tests), `EqualityReconstructionTest`,
  `ClausalTest`, `SuperposeTacticTest`, `CertifiedClausificationTest` (11 sites) and `PrenexRewriteTest`.
  `ProofIRTest`'s local `isValid` was tightened the same way.
- `assertCorrectProof` — accepted, `Sorry` permitted. Only the two sites that stub the prover on purpose
  (`ScreenPhaseTest`, and the one `sorryProver` case in `CertifiedClausificationTest`), each with a comment
  saying why tolerating `Sorry` is the point there.

All 484 tests still pass, so the real provers do produce `Sorry`-free proofs. A guard that never fires proves
nothing, though, so `lisa.kernel.KernelProofTest` pins that it fires: the kernel accepts a `Sorry` proof (the
fact that made the old assertions vacuous), `assertCorrectProofNoSorry` rejects one and names the cause,
accepts a genuine `Hypothesis` proof, and rejects a kernel-invalid one; `assertCorrectProof` tolerates `Sorry`
but still rejects an invalid proof.

Still open from the same finding: the 20 SYN tests remain without the imports-⊆-clauses check (§4).

### 1.2 ~~[H] Certified naming emits bidirectional definitions, defeating its own blow-up cap~~ — FIXED 2026-08-09

`FastClausify.define` emits the polarity-directional Plaisted–Greenbaum half (`d ⇒ c` at positive polarity,
`c ⇒ d` at negative). `CertifiedFastClausifier` emits `∀x̄. subst ⇔ nm(x̄)` unconditionally: `findSite`
computes the polarity and uses it in the gates, but `Site(subst, phiBody, p)` discards it.

The threshold gate bounds the clause count only in the direction the site's polarity uses; the other half of
the `⇔` is unbounded, so it can distribute into exponentially many clauses on precisely the shapes naming
exists to tame (*reported*: `¬((a₁∧b₁) ∨ … ∨ (a_k∧b_k)) ∧ T` goes from `k` clauses to `2^k`). Two
consequences: the header's "stay polynomial" claim is false for the certified path, and the twins produce
materially different clause sets even when they name identically — which narrows what
`CertifiedFastEquivalenceTest` vouches for, since it compares only `namedFormula` and never inspects the
definitions.

**Fix.** `Site` and `NamingStep` now carry the polarity `findSite` already computed, and `NamingStep` exposes
two formulas: `quantified` (the `⇔`, used by the `RightSubstIff` bridge and the final discharge — neither is
clausified, so both are unaffected) and `directional`, the half handed downstream, matching
`FastClausify.define`: `nm ⇒ subst` at positive polarity, `subst ⇒ nm` at negative, the full `⇔` at 0.

The inner proof supplies it with **one `Weakening` per definition** — the kernel's rule is `isImplyingSequent`,
an ortholattice *entailment* rather than an equivalence, and the checker takes `∀x̄.(a ⇔ b) ⊢ ∀x̄.(a ⇒ b)`
including under the binder (probed directly before relying on it). At polarity 0 the two formulas coincide and
the assumption import is cited unchanged.

Measured on `((a₁∨b₁) ∧ … ∧ (a_k∨b_k)) ∨ z`, which names the conjunction at positive polarity so the *unused*
half is the expensive one (`pos = k`, `neg = 2^k`) — clauses handed to the prover:

| k | before (`⇔`) | after (directional) |
|---|---|---|
| 5 | 38 | 6 |
| 12 | **4109** (= 2¹² + 13) | **13** |

Pinned by a new test, which was checked to *fail* on the old behaviour (that is where the 4109 comes from).
The first version of that test was vacuous and passed either way: it used `¬(⋁(aᵢ∧bᵢ))`, where the `Or` sits at
negative polarity, so the `pol >= 0` gate never fires and nothing is named at all. Choosing a shape where the
gate fires *and* the unused direction is the costly one is the whole difficulty of testing this.

Also corrected while here: this phase was dropping `problem.frozen` (§1.6), the one phase of seven that did.

### 1.3 ~~[H] `CascProver` emits ambiguous and invalid TPTP~~ — FIXED 2026-08-09

Two independent defects in the flat-CNF renderer, both invisible to the kernel because this path never builds
a kernel proof:

- `functor(c.id.name)` (lines 294, 298) drops the identifier counter, so `sk`, `sk_3`, `sk_7` all print as
  `sk`. `printDerivation` uses `sig.info(...).name`, which *is* the full `id.toString`, so the clause lines
  and the derivation lines disagree about which symbols exist.
- `NamingSupport.freshNamingAtom` returns a **`Variable`** of sort `Ind→…→Prop` (deliberately, so `InstSchema`
  can discharge it). `symbol` maps any `Variable` to `vname`, so a naming atom renders as `X0(X1)` — a
  variable in functor position, which is not valid TPTP CNF. The comment claiming this branch is "only
  reached for a genuine Ind variable" is false. Naming fires on large problems, i.e. exactly where a printed
  proof matters.

**My `CascProverTest` cannot catch either**, which is worth recording: its problems use explicit constants
(one `sk` at most) and sit far below the naming threshold, so the re-parse assertion — which is the right
assertion — never reaches the broken code.

**Fix.** One rule each, both in `Tptp.render`:

- `functorOf(id) = functor(id.toString)`, never `id.name` — the counter is part of the identity.
- Only an `Ind`-sorted `Variable` is a TPTP variable. At any other sort a `Variable` is a *symbol*:
  `freshNamingAtom` returns naming atoms as `Variable`s so `InstSchema` can discharge them, and `ScreenPhase`
  renames user predicate variables to `usr…`. `term` routes through `symbol` so the rule holds in term
  position too.

Observed before the fix, on problems the old tests never produced. Two existentials:

```
cnf(c0, plain, p(sk),  inference(clausification,…,[a1])).
cnf(c1, plain, q(sk),  inference(clausification,…,[a2])).   % really sk_1
```

`q(sk)` does not follow from `? [Y] : q(Y)` — `sk` is already `a1`'s witness. And a naming atom with a free
variable printed as `a1(X0) | X1(X0)`: a variable in functor position, not valid TPTP. After the fix these are
`q(sk_1)` and `a1(X0) | nm_1(X0)`.

**Verification, and a new offline oracle.** `tptp4X` — the checker CASC itself applies — ships in the TPTP
distribution at `$TPTP/Scripts/tptp4X`, so no download and no network. `Tptp4X` (test package) runs it,
through WSL on Windows since the binary is a Linux ELF, and cancels with a warning where it cannot run at all,
the same trade `TptpCorpus` makes. Three new tests, each checked to *fail* on the reverted code:

| test | catches |
|---|---|
| distinct Skolem constants print distinctly | `collapsed into {sk}` |
| an applied naming atom prints as a functor | `a1(X0) \| X1(X0)` |
| tptp4X accepts every emitted refutation | `tptp4X rejected …` — independently |

Note the division of labour: tptp4X catches the naming atom (a syntax error) but is **blind to the Skolem
collapse**, which is well-formed TPTP that simply does not follow from its leaves. Semantic derivation
checking is GDV's job, and GDV is online-only — deliberately kept out of the suite rather than making tests
depend on a third-party endpoint and publish proofs externally. A periodic manual audit is the right home for
it. That is why the symbol assertions exist alongside the syntax gate rather than being replaced by it.

### 1.4 ~~[H] `equalityFactoring` restricts the *partner* literal to the eligible set~~ — FIXED 2026-08-09

Both loops range over `eligible`. Bachmair–Ganzinger requires eligibility only of the factored-out literal;
the partner is any other positive equality. Vampire agrees — `getSelectedLiteralIterator()` for the factored
literal, `iterLits()` for the partner.

Concrete miss (*reported*): `f(x) ≈ a ∨ f(x) ≈ d` with `d ≻ a` selects only literal 1, so literal 0 is never
offered as partner. Two things keep this hidden: the doc frames the restriction as deliberate ("which pairs
are eligible — is the loop's concern, via `eligible`"), and every test passes `Array(0, 1)`, so both literals
are always eligible.

**Fix.** `j` ranges over all of `c`'s literals; `eligible` governs `i` only. The doc now states the asymmetry
and why, rather than presenting the restriction as the loop's business.

Pinned by a test using a *genuinely* restricted selection: `f(x) ≈ a ∨ f(x) ≈ d` with `a` interned before `d`,
so literal comparison cancels the shared `f(x)`, `d ≻ a` makes literal 1 strictly maximal, and
`maximalFlags` really is `(false, true)` — the test asserts that before proceeding, so it cannot quietly stop
exercising the case. On the old loop it fails with `got {}`: not a wrong factor, *no factor at all*.

That is the shape of the whole finding — the existing equality-factoring test passes `Array(0, 1)`, and every
other test does the same, so no test could observe the restriction. A test that supplies every literal as
eligible cannot test what eligibility excludes.

Regression check: the 44-problem list still refutes 44/44 with no bad proofs. Note the limits of that — the
list is the equality-*free* corpus, so it barely exercises equality factoring at all; the equality-bearing
corpus was not A/B'd. The change strictly adds inferences, so the risk is search cost rather than
correctness, and `Reconstruction.buildEqualityFactoring` replays a `Justification.EqualityFactoring`
regardless of whether the partner was eligible.

### 1.5 ~~[H] `DiscriminationTree` lacks the re-entrancy guard its two siblings have~~ — FIXED 2026-08-09

`Fingerprint` and `FeatureVector` each convert "callback must not re-enter the index" into a loud
`IllegalStateException` with a test (5 and 7 `guardNotDescending` sites). `DiscriminationTree` has **zero**,
only a comment — and its failure mode is worse: re-entrancy resets the shared `qLen`, so the outer descent
calls `visit` on rules whose LHS does not generalise the query. That is an unsound rewrite, not a lost
candidate.

Separately, the leaf loop calls `visit(rs(k))` for every rule at a leaf with **no `trail.save()`/`restore`
between them**, so a `visit` that binds leaves σ polluted for the next rule. Multiple rules per leaf is
ordinary (`f(x)=a`, `f(x)=b`).

Latent today: the only caller's `visit` reads the trail but never writes it.

**Fix.** Both halves, plus the `visit` contract written down on `retrieveGeneralizations`:

- The `descending` flag and `guardNotDescending`, ported from the siblings, on `insert`/`remove`/`clear`/
  `retrieveGeneralizations`. The buffer comment now says *why this one is worse* than the same hazard in the
  clause indices — there a corrupted buffer drops a candidate, here it makes the descent report rules that do
  not generalize the query.
- `save()`/`restore()` around each leaf-rule `visit`. The variable edges were already bracketed; the leaf loop
  was not, so a `visit` that bound left σ polluted for the *next* rule at that leaf — and several rules per
  leaf is ordinary (two unit equalities sharing an LHS).

While here, `clear()` was unguarded in all three indices — the one structural operation the other two also
missed. Now guarded in each.

Two tests, both checked to fail on the reverted code. The re-entrancy one names each of the four entry points
and then asserts the guard *disarms* (a `try/finally` bug there would make every later retrieval throw). The
trail one puts two demodulators on one leaf and compares the trail checkpoint at each `visit`: reverted, it
reports `1, 2` — the second rule matched under a substitution the first left behind.

Corpus unaffected: 44/44 on the 44-problem list. The bracket is on the forward-demodulation path, but `save`
is a counter read and `restore` a no-op when nothing was bound, which is the usual case.

### 1.6 [M] `certifyFastNaming` is the only phase that drops `problem.frozen` — **verified, found twice**

Two reviewers reached this independently. `Problem((namedHyps ++ defHyps).toList, None)` omits the third
argument; all six sibling phases thread it, and `Clausification` documents it as "threaded forward through
every phase". `freshNamingAtom` takes a `frozen` parameter — documented as the guard against ∀-closing an
uninterpreted Skolem constant — and this call site does not pass it. Harmless only because naming runs above
Skolemization, the only producer of frozen symbols.

### 1.7 ~~[M] `needsAssumptions` optimisation added an unstated invariant~~ — FIXED 2026-08-09

A child subproof's external imports unconditionally receive the inherited assumptions, while the kernel checks
subproof premises by *exact* match. So a parent step that `needsAssumptions` marked `false` will fail to match
the child's import. All `ClausificationSubproof` construction sites currently satisfy the invariant;
nothing states or checks it. Citing a locally-derived closed lemma as a subproof premise — a natural thing to
want — would break it.

**Fix.** Both halves of the recommendation. The restriction is now a named paragraph on
`ClausificationSubproof` ("cite only assumption-bearing steps"), stating the rule, why negative premises are
exempt (lowering routes them through the external-import view or a `Weakening`, both of which carry the
assumptions), and — the part that makes it concrete rather than abstract — that `DistributePhase` is the live
temptation: it derives every clause from *closed* steps and stays correct only by citing the `Cut` against the
axiom import, never the derivation behind it.

`lowerClausificationProof` then asserts it at the `ClausificationSubproof` case, where the `needs` relation is
in hand: every non-negative premise must satisfy `needsAssumptions(r)`. The check is skipped entirely when no
assumptions are in scope (`needsAssumptions == null`), which is exactly when nothing is rewritten and the
constraint is vacuous.

All seven construction sites pass (the review said six; `ScreenPhase` is the seventh) — 496/496 tests with the
TPTP corpus present, so the assertion is exercised by the whole certified pipeline rather than only by unit
tests. Note what this does **not** do: it fires when a bad premise is lowered, not when the subproof is built,
so it reports the offending premise index rather than the site that chose it. Constructing the `needs` relation
requires the enclosing proof, which `ClausificationSubproof` does not have, so a construction-time `require`
was not available.

### 1.8 ~~[M] Subsumption-resolution knobs are silently dead in reachable configurations~~ — FIXED 2026-08-09

`Discount:116` gates `simplifier.forward` on `forwardSubsumption || forwardUnitDeletion`, but `Simplifier`
runs SR on its own flag inside. So `SearchOptions(forwardSubsumption = false, forwardUnitDeletion = false,
forwardSubsumptionResolution = true)` does no forward SR at all, silently. Same shape backward
(`Discount:157` vs `Simplifier:228`). Three knobs documented as independent axes; one is reachable-dead.

The ablation that flipped the shipped SR default is **not** invalidated — `Evaluation`'s `subs` argument
defaults to both-on, so the gate was open.

**Fix.** The three `Discount` guards are gone — the two forward ones (at selection, and the
`forwardSimplifyAtGeneration` arm of `addPassive`) and the backward one — so the loop calls
`simplifier.forward` / `simplifier.backwardSubsume` unconditionally and `Simplifier` owns the question.

Deleting them naively would have cost something, which is why the decision moved rather than vanished:
`forwardScan`/`backwardScan` walk the whole active set per given, so with *every* flag off they would spin an
empty O(|active|) loop where the guard used to skip the call. `Simplifier` therefore gained `forwardEnabled` /
`backwardEnabled` — the disjunction over **all three** flags in each direction, not the two the loop happened
to test — and each entry point early-outs on it. The backward one is a deliberate over-approximation: which of
`backwardUnitDeletion` / `backwardSubsumptionResolution` applies depends on whether the given is a unit, decided
per call inside.

The general point is in the `forwardEnabled` doc: a gate can only stay in step with the flags it guards if it
lives beside them. The shipped configuration has every flag on, so no default behaviour changes (496/496 tests
unchanged); what changes is that the SR-only configurations now do what they say.

### 1.9 [M] Other unenforced preconditions — **all seven now documented, 2026-08-09**

Each holds today by call order and was documented nowhere. Every row now carries a one-sentence precondition
note in the owning scaladoc — stated, not asserted, since none is cheap to check at the point it matters:

| Where | Assumption | Breaks if |
|---|---|---|
| `dischargeAssumptionsLatestFirst` | the substitution fixes `rhs` pointwise | reused under a non-empty succedent |
| `Signature.intern` after `Precedence.assign` | ~~precedence stays a dense permutation~~ — **row was wrong, see below** | — |
| `FeatureVector` monotonicity | subsumption is **multiset** (injective) | relaxing `matchRec` to set-based |
| `DiscriminationTree` size prune | every symbol weight ≥ `VariableWeight` | a zero-weight constant scheme |
| `SampleTrie` | positions are pairwise distinct | a duplicate silently leaves a slot stale |
| `Clausal.Abstraction` | every free variable of an ε-term is `Ind` | a higher-sorted free variable → sort error |
| `CascProver` leaf naming | input clause ids are exactly `0…n-1` | `Bridge` pre-building any clause |

**Correction: the `Signature.intern` row does not hold as stated.** Writing the note exposed it. A fresh
`SymbolInfo` defaults to `_precedence = id`, and `id` is `infos.length` at construction — so after
`Precedence.assign` has laid down ranks `0 … n-1`, the next symbol interned takes precedence `n`, then `n+1`,
and so on. The precedences stay a dense *total* order throughout, `KBO` never reaches its "equal precedence but
distinct symbols" `Inc` branch, and no completeness is lost. (Interning also bumps `orderingVersion`, via the
`weight` write in `intern`, so `Order`'s orientation memo drops itself correctly too.)

What is true is milder and worth recording anyway, so the scaladoc says that instead: a symbol interned after
`assign` lands above every rank the scheme chose, i.e. it silently opts out of the selected
`PrecedenceScheme`. Sound, unprincipled, and invisible.

**The intern key — FIXED 2026-08-09.** It was `(name, arity)`, and it *accepted* `isPredicate` only to
discard it, so a name used at the same arity as both a predicate and a function collapsed into one symbol with
whichever occurrence interned first deciding the kind for both. Unreachable from TPTP, where the positions are
distinct; ordinary from a Lisa goal, where `Constant("p", Ind→Prop)` and `Constant("p", Ind→Ind)` are two
legal symbols. Note the shape of the mistake: the call sites in `Bridge` all *knew* the kind and the sort —
every production `intern` call is in that one translation function — and the information was dropped twice on
the way in.

The key is now the quadruple `(name, no, arity, isPredicate)`, and `SymbolInfo` stores the identifier's name
and counter index apart instead of one `name_no` string. That has a second payoff: `Reconstruction`
*reassembles* `Identifier(name, no)` rather than parsing it back out of a string, so `identOf` — and the
argument that the `toString`/parse round-trip is lossless because the TPTP parser escapes `_` — is gone.
`schematicNames`/`dischargeByName` are keyed by `K.Identifier` rather than by name. `SignatureTest` pins what
the key must and must not distinguish.

Deliberately still *not* distinguished: a `Constant` from a `Variable` used as a symbol. Closing that in the
key alone would not close the class, since `Reconstruction` decides which to rebuild by identifier membership
in its schematic set; the generated namespaces are what keep them apart today.

**Decided, not overlooked: `CascProver`'s printer does not re-separate them.** Two symbols that are now
distinct in the signature but share a name still print as the same functor. That is accepted:

- On the CASC path it cannot arise. The only input is a TPTP file, and TPTP does not permit one name as both
  a predicate and a functor, so the two symbols never coexist there.
- Where they can coexist — a Lisa goal — the output is a kernel proof, not TPTP, and the kernel keeps them
  apart by sort.
- Even if such a pair were printed, the positions disambiguate for a reader: different arities, or one in
  literal position and one nested in a term.

Slightly inelegant, unambiguous, and safe. Not worth qualifying every functor name in the output for a case
the input language cannot express.

### 1.10 [M] Error handling that loses information

- `Superpose` catches `Throwable`, converting an `InterruptedException` into an ordinary tactic failure *and*
  clearing the interrupt flag, and absorbing `OutOfMemoryError` and assertion failures into "Superpose failed".
- `BenchUtil.withTimeout` wraps the body in `Try`, which catches only `NonFatal`, so an `OutOfMemoryError`
  leaves the result box empty and is reported as `HARD_TIMEOUT`. "Times out on 12 problems" and "OOMs on 12
  problems" are very different conclusions.
- `FofHarness`'s summary omits `PROVER_CRASH` and `MISSING` from its counts while still printing `of $total` —
  and `PROVER_CRASH` is the category added specifically to surface fork-mode crashes.

### 1.11 ~~[M] `DistributePhase.isLeaf` fails open on its own motivating case~~ — FIXED 2026-08-09

The `Forall`/`Exists` extractors require an explicit `Lambda`, so an η-reduced `Application(forall, p)` — the
exact shape `etaExpandQuantifiers` exists to repair — has sort `Prop`, falls through to the catch-all, and is
accepted as a *literal*. Not unsound; the prover just receives an opaque quantified atom and the problem looks
unprovable rather than mis-clausified.

**Fix.** `isLeaf` matches the two `Application(forall, _)` / `Application(exists, _)` shapes head-on and returns `false`, so
the shape hits the `require` in `distributeClauses` instead of the sort test. The message names the cause
(β-normalisation η-reduced the body and `etaExpandQuantifiers` was not applied) rather than only printing the
offending expression, because the *symptom* — a problem that merely looks unprovable — carries no signal at all.

Worth being precise about what this buys, since it is a diagnostic and not a soundness fix: previously the
clause carried an opaque quantified literal whose head `Bridge.atomTerm` interns as an ordinary unary predicate
`forall/1` over a clause variable. That is a well-formed clause. Nothing downstream can tell it from a genuine
atom, so the failure surfaced as an unexplained non-refutation, arbitrarily far from its cause.

Only the quantifiers need the case: a partially-applied connective such as `∧(a)` is `Prop → Prop`, so the sort
test already excludes it — the quantifiers are the ones that take a single argument and land back at `Prop`.
That is now stated in the scaladoc so the case does not read as arbitrary.

`DistributePhaseTest` (new, 5 tests) pins it, and both η-reduced cases were checked to fail on the reverted
code — with "no exception was thrown", i.e. the shape really was being clausified as an atom. The other three
tests cover the ordinary CNF path, the explicit-`Lambda` quantifier the old case already caught, and the
sort-excluded partial application, so the three routes to the same verdict stay pinned together.

**The root cause was fixed separately, on 2026-08-10 — see §1.13.** The entry to every path now η-expands, so
this check is a backstop rather than the whole defence.

### 1.12 ~~[M] `PrenexPhase`'s two strategies are not interchangeable~~ — FIXED 2026-08-10

The rewrite path instantiates `schemaR := sibling` assuming the sibling is free of the lifted binder. That is
neither checked nor guaranteed. The deconstruct path is immune. `preferRewriteStrategy` chooses silently, and the
one test covering the rewrite path uses a nullary constant, so it structurally cannot catch this.

Fails loudly via a `require`, not silently — but on input the other strategy handles fine.

**Correction: the original entry blamed the wrong component.** It claimed `ScreenPhase` *creates* the collision,
citing `(∀v_0. P(v_0)) ∧ Q(y)` screening to `(∀v_0. P(v_0)) ∧ Q(v_0)`. That does not happen. Substitution is
capture-avoiding, so screening α-renames the binder and yields `(∀v_1. P(v_1)) ∧ Q(v)` — and `ScreenPhase`
already had a test pinning exactly that ("an input binder that shadows a canonical target is α-renamed"). The
entry contradicted a property the suite was checking.

Screening in fact does the opposite: on a collision already present in the input it renames the free occurrence
and leaves the bound one, so `(∀x. P(x)) ∧ Q(x)` screens to `(∀x. P(x)) ∧ Q(v)` and both strategies then succeed.
Since the entry's only proposed route to the defect was that (non-existent) one, its reachability claim went with
it. No route from the pipeline has been found; the defect is real on directly-constructed input.

**The actual defect, and the fix.** `liftOneLayer` built the lifted formula by hand as
`forall(Lambda(x, and(body)(rhs)))`, reusing the source binder. The correct lift of `(∀x. body) ⊕ s` is
`∀x'. (body[x:=x'] ⊕ s)` with `x'` fresh for `s` — reusing `x` captures a free `x` in `s`, and the result is not
an instance of the law, which holds only because `R` is a nullary `Prop` schema.

The mismatch was between the code and the kernel, not within the code: `InstSchema` substitutes
`schemaR := s` *capture-avoidingly*, so it produced the correctly renamed formula while the hand-built one
captured. The strip then yielded a matrix `extractUniversalMatrix` never predicted, and the closing `require`
fired.

The fix α-renames the binder away from the sibling's free variables and uses the renamed pair for both `rhsIff`
and `schemaP`; `lhsIff` keeps the original binder, since it must match the node as it stands in the source
formula. The two four-case matches collapsed into one that yields the sibling and the library reference, so the
substitution is written once.

**Tests.** Two, in `PrenexRewriteTest`, one conjunct apart so the contrast is the strategy and nothing else: the
same capturing shape at a size that selects deconstruct (passed before the fix) and at a size that selects
rewrite (failed before it, across all four `LiftLayer` cases). The failing one was written first and confirmed to
fail with `got Pc(w) ∧ Qc(w) ∧ Qc(y), expected Pc(w) ∧ Qc(z) ∧ Qc(y)`. Its bound variable is deliberately named
`z`, not `x`: `x` is `Clausification.schemaX`, the library statements' own binder, and naming it `x` would leave
the test open to being read as a collision with *that* — which is not the defect. Verified: the failure is
identical either way. Each test asserts what `preferRewriteStrategy` returns before proceeding, so neither can
silently stop covering its case if the heuristic changes.

### 1.13 ~~[M] η-reduced quantifiers are repaired at one producer, not at the entries~~ — FIXED 2026-08-10

§1.11's backstop made the failure loud on one path. This is the root cause, closed on all of them.

`betaNormalForm` η-reduces `λy. p(y)` to `p` (kernel `Syntax.scala:277`), so `∀y. p(y)` can present as
`∀(p)` — which `Forall`/`Exists`/`Epsilon`, all requiring an explicit `Lambda`, do not match. Every phase is
written against those extractors, so such a quantifier travels the pipeline as an opaque *atom*: NNF does not
push a negation through it, `SkolemPhase` does not Skolemize it, `PrenexPhase.hasForall` does not strip it, and
`Bridge` interns `∀` as an ordinary unary predicate. Never unsound — the clause is still a consequence — but a
valid goal quietly looks unprovable.

The repair lived at the single place that *creates* the shape (`SkolemPhase`'s `betaNormalForm`, the
Pelletier-50 fix). That is repair-at-the-producer, and it left the other source — a caller simply handing us an
η-reduced formula — uncovered on **every** path.

**Measured first, three facts that make the fix free.** `isSame` compares `betaNormalForm`s, so the two shapes
are indistinguishable to the kernel: `isSame(∀(p), ∀(λz.p(z)))` is `true`, `Restate` is valid in *both*
directions, and `InstSchema` checks via `containsEq` → `isSame`. So η-expansion needs no lemma, no schema, and —
placed inside an existing `InstSchema` — no extra proof step at all.

**Fix: normalise at each entry, then keep the pipeline closed.** Three entries, one per way a formula can arrive:

| entry | path | note |
|---|---|---|
| `ScreenPhase` | certified | folded into the existing `InstSchema`; `Restate` when there is no renaming to do |
| `FastClausify.clausalFormWithOrigins` | uncertified — CASC, every benchmark | *after* the orthologic `reducedNNFForm`, which rebuilds through the kernel's locally-nameless form |
| `Bridge.formulaToSequent` | already-clausal TPTP | expected to be a no-op; applied rather than assumed, since it is idempotent and one traversal |

`CascProver.Tptp.cnfClause` got it too — an unstripped quantifier there prints as the functor `'∀'(p)`, which is
well-formed TPTP but illegal in a `cnf` body, so the emitted proof would be rejected.

**Deliberately not changed: `Bridge.solve` itself.** It documents its input as *already clausal*, and a clause has
no quantifiers, so a quantifier arriving there is caller error however it is shaped. Worth recording that the two
shapes fail differently: `∀(p)` interns `∀` as a unary predicate and proceeds silently, whereas `∀(λz. p(z))`
makes `atomTerm` throw "not first-order" on the `Lambda` argument. Expanding inside `solve` would therefore
convert a silent caller error into a loud one — an improvement in isolation, but it belongs to a separate
question (what `solve` should assert about its input) rather than to this one, and every in-tree caller now feeds
it η-clean clauses.

Two things can reintroduce the shape downstream and both re-apply immediately: `SkolemPhase.skolemizeOne` (the
demonstrated case) and the orthologic normal form (defensive). The rule is now stated on
`etaExpandQuantifiers`: **re-apply after any `betaNormalForm` or kernel normal-form round-trip.** It is
`private[automation]` rather than `private[clausification]` because `Bridge` is one of the entries.

**On the ordering.** η-expansion runs *after* the screening renaming, so the fresh `etaZ` binders are minted
when every input name is already a `v`/`usr` and cannot collide with the caller's; and *after* the orthologic
step, so nothing it emits escapes normalisation. Neither order is observable in the output on ordinary input,
which is exactly why both are written down.

**The user's formula is not altered.** `ScreenPhase.restored` prefers the caller's own conjecture whenever
`isSameSequent` holds, and η-expansion preserves that — so a goal written `∀(p)` comes back `∀(p)`.

Seven new tests, all checked to fail on the reverted code, and the failures are the finding itself: on the
certified path they surface through §1.11's `require`; on the uncertified path the clause set prints as
`Sequent(Set(),Set(∀(p)))` — the quantifier sitting in a clause as a literal, beside a correctly-stripped `q(w)`
from an explicit-`Lambda` hypothesis in the same problem. That contrast is the whole bug in one line of output.
`ε`-terms remain deliberately excluded from the expansion: they are matched structurally by `Clausal`'s
abstraction and the reconstruction's import lookup, so normalising inside one risks the "clause absent from the
clausifier's clause set" mismatch in `Clausal.proveOutcome`.

---

## 2. Documentation

The prose is well above average in *kind* — it explains why, not what — and several headers are load-bearing
and should not be touched: `ClausificationSubproof`'s soundness restriction, the clausal-prover contract,
`ScreenPhase`'s whole header, the arena layout in `Core`, `matchTerm`'s contract, and the pipe-deadlock and
locale notes in the harnesses. All state invariants unrecoverable from the code.

The problems are volume and drift.

**Changelog-as-comment**, ~10 files. `SearchOptions` opens with eight lines about how the knobs used to be
re-declared at four layers; `BenchUtil` explains how the problem lists used to be located; `Precedence` opens
with "our default used to be…". A reader of `SearchOptions` needs to know what the knobs mean. The contrast
that makes the rule clear: `ActiveSet`'s history note *earns* its place, because there the history is the
rationale for the class existing.

**The same thing said three or four times.** `DistributePhase` states its flat-emission rationale four times
plus a fifth in `ProofIR`. The contamination anecdote appears in four files. The dated ablation numbers
(80 vs 74, 71 vs 74, 72 vs 74) appear in four files *and* in `Benchmarks.md` — four copies of a number that
changes whenever the ablation is re-run. `Subsumption`'s four conditions are listed in three places.

**Claims that are false as written** — worse than silence, because they send a reader to the wrong place:

- `ActiveSet`'s class doc argues re-derived removal is safe *because* of the `orderingVersion` stamp. The
  stamp guarantees the inverse: it makes `orient` return new answers, so removal would orphan entries. The
  real guarantee is that the ordering is fixed per saturation — which the `treeRulesOf` doc, three lines
  below, states correctly.
- My `needsAssumptions` comment says the kernel "demands the two left sides line up exactly" for
  single-premise rules. It does not — they use `subset`/`allContainedExcept`. The conclusion holds by
  `needs`-inheritance, which the preceding sentence already gives.
- `matcherIsRenaming`'s "recomputing would trade this array for more garbage" and `maximalFlags`'s "no
  boxing" both defend hot paths with guarantees the compiler does not give.
- `AdversarialInputTest`'s header says message text is not asserted; all fourteen tests assert it. Here the
  code is right and my header is wrong — the substring checks are load-bearing.
- `Reconstruction.scala` says "see `Reconstruction.md` for the design"; that document's third line reads
  *"Status: design, not implemented."* `Phase4.md` says "Not started" for shipped work. `Phase3.md` documents
  a `certifyTseitin` phase that does not exist.

**Structural.** Neither package has a README or any entry point. `PLAN.md` — a good 96-line orientation — now
sits in `archive/`, which tells a reader it is dead, and the repo-root `CLAUDE.md` link to it is broken. Four
of the seven clausification phase files have no object-level doc at all, including the two largest.
Sixteen files use "Phase 4 Step 3" vocabulary that only resolves through documents the project itself marks
historical. Two `.md` claims I made in the previous review were wrong: the docs are **not** packaged into the
jar (verified: zero `.md` in `target/…/classes`), and `.txt` needed moving for the resource-loading and
forked-child reasons, not jar bloat.

---

## 3. Structure

- **`Discount` is still ~60% generating-inference machinery.** The split gave simplification its own class
  with indexed and scanning arms; generation has the same shape and the same A/B story and did not get the
  same treatment. Extracting a `Generator` would drop `Discount` to ~150 lines and make its header true.
- **`lowerClausificationProof` is 147 lines** doing six jobs, with the same "compare, then weaken" idiom
  written four times in three subtly different spellings.
- **`SearchOptions.default` is dead** and its docstring ("the shipped configuration") contradicts
  `Strategy.balanced`, which pins SR *off*. Two things claiming to be the default, differing.
- **`FeatureVectorIndex.backwardCandidatesThenInsert` is dead** — found independently by two reviewers; the
  fusion it existed for became impossible when backward subsumption moved to `Simplifier`.
- **Naming collisions:** `Problem` means both `Clausification.Problem` and `lisa.tptp.Problem` (the tell is
  that `BenchUtil` needs a `toClausificationProblem` to disambiguate); `SuperpositionTactic.scala` contains
  `object Superpose` tested by `SuperposeTacticTest` — three names for the user-facing entry point.
- **Four spellings of "is this literal an equality"** across `Discount`, `ActiveSet`, `Demodulation`, `Order`.

---

## 4. Tests

~325 tests. Real strengths, verified: indices pinned against exact brute-force oracles; trail save/restore
asserted on both success and failure paths; randomised differential tests for KBO and the literal order;
negative controls beside positives more often than is typical; and the clausifier has a genuine soundness
guard (a satisfiable set asserted *not* refuted).

Gaps, beyond §1.1:

- **The 20 SYN reconstruction tests never check imports against the problem.** The inline helper does;
  `checkSCProof` validates *conditionally on imports*, so a refutation importing a sequent the problem never
  contained would pass — and those 20 are the only reconstruction coverage on real input.
- **The generation↔replay correspondence is asserted only where it is vacuous.** The replay code exists to
  reproduce exact fresh-variable numbering; every test that could observe it is ground.
- **Index A/B tests compare a verdict too coarse to fail.** An index dropping a large fraction of candidates
  would still reach `refuted` on every one of these builders. `loopStats` already exposes counts that would
  make the assertion sharp.
- **Clause-selection fairness is untested** — the property the completeness argument rests on. No
  `PassiveSetTest` exists.
- **`WeightScheme.Arity` and `LiteralSelection.BestLiteral` are entirely unexercised**, though `PrecedenceTest`
  pins the analogous property for every `PrecedenceScheme`.
- **Four tests titled "default selector" pin the wrong default** — the `TermBank` field default
  (`BestLiteralSelector`, the incomplete one), not the shipped `LiteralSelection.Complete`.
- **41 tests (~11%) vanish without `TPTP`**, including all reconstruction on real input and the entire
  certified-vs-fast equivalence check. The banner added earlier is the right mitigation; the residual risk is
  a CI job reporting "All tests passed" with both missing.

---

## 5. Prioritised actions

1. **`assertProved` with `usesSorry == false`** (§1.1). Smallest change, largest correctness return.
2. **Polarity-directional certified definitions** (§1.2) — restores the clausifier's stated bound.
3. **`CascProver` identifier and naming-atom rendering** (§1.3), plus the two test problems that would have
   caught them.
4. **Equality factoring partner range** (§1.4) — a silent completeness loss in a generating rule.
5. **`DiscriminationTree` re-entrancy guard and per-rule trail bracketing** (§1.5).
6. ~~**Thread `frozen` through `certifyFastNaming`** (§1.6)~~ — done under §1.2; what remains of §1.6 is the
   unused `frozen` parameter on `freshNamingAtom` (thread it into both naming paths, or delete it — open).
   ~~**Delete the SR guards in `Discount`**~~ (§1.8) — done, with the enable decision moved into `Simplifier`.
7. ~~**Write down the seven unenforced preconditions**~~ (§1.9) — done, one sentence each in the owning
   scaladoc; one row turned out to be a false finding and is corrected in place. §1.7's is stated *and*
   asserted. Still open: assert the cheap ones, and add `KBO.checkAdmissibility` (§6.2) to the table.
8. **Documentation pass:** delete the changelog paragraphs, collapse the four-times-repeated rationales,
   fix the five false claims, add a `README.md` with a file map, move `PLAN.md` out of `archive/`, and banner
   every archived document with its status.

---

## 6. Addendum — second reading (2026-08-09)

Five further observations from a full re-read of both packages, after the §1.1–§1.5 fixes landed. None is a
soundness issue and none displaces anything in §5. Two of them restate findings already recorded above; they
are kept because they were reached independently, and because each adds something the original entry does not.

### 6.1 [L] `FeatureVectorIndex.backwardCandidatesThenInsert` is unreachable — **duplicate of §3**

Confirmed from the call sites rather than by grep: `ActiveSet.add` inserts into `subsumptionIndex`, and
`Simplifier.backwardIndexed` queries it through `ActiveSet.subsumeeCandidates`. The two now happen in different
classes at different points of `activate`, so the fused "compute the feature vector once, query then insert"
method has no caller left. Worth noting that its doc carries the *collect-inside-`visit`, mutate-after* rule
that the split since made structural — deleting the method should not delete that sentence, which belongs on
`backwardCandidates`.

### 6.2 [M] Four ordering members are test oracles, and one of them names a live runtime gap — **verified**

`Order.maximalSide`, `Order.isStrictlyMaximal`, `Order.compareClause` and `Order.termMultisetCompare` have no
production caller. Each says so and is visibility-restricted accordingly, and that is a fair trade: they state
the definitions in the form the tests check against, and the engine reads `orient`/`isMaximal` directly to
avoid the allocation.

`KBO.checkAdmissibility` is different in kind, and its own doc is the source of the finding. `WeightScheme` and
`PrecedenceScheme` are user-selectable through `Strategy`, so KBO admissibility — and with it *termination of
rewriting* — is a property of a **runtime configuration** that only a test validates. A scheme added later that
violated it would not fail in `KBOTest`; it would loop, or lose completeness, somewhere inside demodulation.
This belongs in the §1.9 table of unenforced preconditions, and it is the one entry there whose failure mode is
non-termination rather than a wrong answer. The fix the doc already proposes — one call from `Bridge.solve`
behind a debug flag — is a few lines.

### 6.3 [L] The shipped portfolio is tuned against a search configuration the engine no longer defaults to — **related to §3**

`Strategy.base` pins `forwardSubsumptionResolution` and `backwardSubsumptionResolution` off, deliberately, so
that "full simplification" stays a real axis for #6 `unary-redundancy` and #7 `subsumption-light`. The
consequence is that **six of the eight** strategies — including #1 `balanced`, which is `CascProver`'s default
and the completeness backstop — run with SR off, while the engine default flipped SR *on* in the 2026-08-08
re-ablation on the strength of 80-vs-74 refutations.

§3 records this as a documentation conflict ("two things claiming to be the default, differing"). The part
worth adding is that it is not only that: each of #2–#8 was chosen to differ from `balanced` in exactly two
knobs, so the portfolio's whole delta structure is defined relative to a baseline that is no longer the
default. Re-deriving it against SR-on is a benchmarking task, not an edit, and until it happens the ablation
that justified the default has never been run on the configuration that actually competes.

### 6.4 [L] `scanGenerate` re-derives `fromSides` once per active clause — **verified**

`Discount.scanGenerate` precomputes the given clause's from-sides once per activation — correctly, and the
comment explains why — then calls `Superposition.fromSides(bank, bank.order, a, aSel)` for **every** active
clause `a` inside the scan, allocating a `List` with a tuple per usable side, per active clause, per given.

Cost is confined to the `fingerprintIndexing = false` fallback, so nothing shipped pays it. It is worth
recording anyway, because that fallback is what the index A/B comparisons and the harnesses' `noindex` mode run
through: the allocation is incidental to linear scanning (the sides could be cached on the `Clause` exactly as
`selected` is), so `noindex` timings overstate the cost of the scan itself and flatter the index by that much.

### 6.5 [L] `ActiveSet.add` and `detach` guard the demodulator upkeep asymmetrically — **verified**

`add` inserts demodulators under `if forwardDemodulationOn && Demodulation.isPositiveUnitEquality(…)`; `detach`
removes them under `if Demodulation.isPositiveUnitEquality(…)` alone. With forward demodulation off both sinks
(`demodTree`, `activeDemodulators`) are empty, so the removal is a no-op — nothing is wrong today.

But `detach` is documented as "the exact inverse of the shadow half of `add`", and this is the one line where
that is not literally true: every other pair (`updateSuperpositionEntries`, `updateResolutionEntries`,
`updateDemodSubterms`, the subsumption index and unit sublist) is guarded by the identical flag on both sides.
Adding the missing `forwardDemodulationOn &&` costs nothing and makes the stated inverse relation hold by
inspection rather than by an argument about which collections happen to be empty.
