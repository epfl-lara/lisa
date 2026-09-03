# Clausification

This package converts a first-order problem stated in Lisa's kernel syntax into a set of clauses, and produces
a kernel proof that connects those clauses back to the original problem. It is the front end of the
[superposition prover](../superposition/), which consumes the clauses and attempts to refute them.

The text below first states the design and therory, then the implementation 

## Part 1: Theory

### 1.1 Goal and direction of work

The caller has a goal sequent and wants a kernel proof of it. We only work with kernel proofs and statements. A saturation prover does not prove goals
directly; it refutes clause sets.
To establish a conjecture, we assume its negation, convert the resulting set of formulas into clauses, and derive a contradiction. A contradiction is a proof of the empty sequent.

The package takes a problem consisting of hypotheses and one optional conjecture, and hands a clause
set to a clausal prover supplied by the caller. The prover is expected to return a kernel proof whose imports are the
clause sequents and whose conclusion is the empty sequent. That expectation is the contract between the two
packages, and Section 2.2 explains where it comes from.

### 1.2 Clauses as sequents

A literal is an atom or a negated atom. A clause is a finite disjunction of literals. Clauses are represented
as kernel sequents under the usual reading, in which a sequent asserts that the conjunction of its left side
implies the disjunction of its right side. The sequent

```
  a₁, …, aₘ ⊢ b₁, …, bₙ
```

therefore represents the clause `¬a₁ ∨ … ∨ ¬aₘ ∨ b₁ ∨ … ∨ bₙ`. A negative literal is carried as its atom on the
left, a positive literal on the right, and no formula on the right is a negation. Both sides are sets, so
duplicate literals collapse and the order of literals carries no meaning. The empty sequent represents the
empty clause, that is, falsity.

This is the representation the prover works in, and it is also the representation in which a refutation is
reconstructed, since the imports of the reconstructed proof are the clause sequents themselves. Emitting it
directly means the clause set, the prover's working form and the proof's imports are one representation rather
than three. Both clausifiers build it at the leaves of their distribution step, `UncertifiedClausifier.toClauses`
and `DistributePhase.clausesOf`.

Clauses contain no quantifiers. Their free individual variables are read as universally quantified. Producing
that shape from an arbitrary formula is the work of the pipeline.

### 1.3 The four transformations

Converting a formula to clauses requires four transformations. Some are simple to certify, others not.

**Negation normal form.** Implications and biconditionals are eliminated and negations are pushed inward until
they apply only to atoms. This is a propositional equivalence. The kernel's `Restate` step accepts it, so one step justifies the whole conversion of a formula.

**Skolemization.** Existential quantifiers are removed. The textbook method replaces the witness of `∃x. φ(x)`
by a fresh function symbol applied to the enclosing universal variables. That method is unavailable to a
certified procedure: introducing a symbol extends the signature, and the kernel can't directly certify equisatifiability.
The kernel does, however, provide the Hilbert epsilon operator and the theorem

```
  (∃x. P(x)) ⇔ P(ε(λx. P(x)))
```

The term `ε(λx. φ)` is therefore a witness that behaves like a fresh function symbol, and no new symbol is required. Section
1.4 describes the one complication this introduces.

**Quantifier stripping.** After Skolemization there ae no existential quantifiers, but there are universal ones. Since a clause
carries no quantifiers and reads its free variables as universal, each `∀x. ψ` is replaced by `ψ` with `x`
instantiated at a fresh variable. The kernel's `LeftForall` rule performs exactly this instantiation. But universal quantifiers can exist deep in the formula, underneath conjunctions and disjunctions. They are stripped where they
stand, by walking the formula's tree and mirroring each connective, which costs a proof linear in the size of
the formula.

**Distribution.** At this stage, the formula is a tree of conjunctions and disjunctions over literals, without quantifiers, and
distributing disjunction over conjunction yields the clauses. Two facts are important.

The first is that only one direction of the distributive law is needed. Clausification requires that the
clauses follow from the formula, that is, `φ ⊢ CNF(φ)`. The instance that this reduces to,
`a ∨ (b ∧ c) ⊢ (a ∨ b) ∧ (a ∨ c)`, is valid in OL. Only the converse requires genuine
distributivity. Consequently each clause is easy to certify in the kernel.

The second fact is that the number of clauses can grow exponentially in the size of the formula. Distribution
multiplies the clause counts of the two operands of a disjunction, so a formula built from nested
disjunctions of conjunctions produces a clause set exponentially larger the initial formula. This is the reason for the transformation described next.

### 1.4 Definitional naming (Tseitin encoding)

To keep the clause set polynomial in the input, a subformula can be replaced by a fresh
predicate, and the meaning of that symbol is recorded as an additional formula. Writing `x̄` for the
free individual variables of a subformula `ψ`, the replacement introduces a fresh predicate `d` together with
the definition

```
  ∀x̄. d(x̄) ⇔ ψ
```

Occurrences of `ψ` become `d(x̄)`. The definition is clausified alongside everything else, and the original is now smaller by the size of `d`. This is the classical Tseitin construction.

Two refinements matter here.

The first is that naming is applied selectively rather than everywhere. Naming every subformula produces a
clause set that is linear in size but created many new symbols, which slows the prover down. Hence there is a tradeoff between the number of symbols introduces and the formula size. The
implementation estimates the clause count of each subformula and names one only when the estimate exceeds a
threshold. This follows the practice of E and Vampire.

The second is that only one direction of the definition is required, and using both is harmful. If `ψ` occurs
only positively, then `d(x̄) ⇒ ψ` suffices; if only negatively, then `ψ ⇒ d(x̄)` suffices.

Skolemization raises the same size question in a different form. The term `ε(λx. φ)` contains the whole
subformula `φ`. A second Skolemization step inside that term would nest one epsilon term inside the next and
square the size, so a chain of existential quantifiers would produce a term of exponential size. The solution is the same as definitional naming: each epsilon term is replaced by a fresh function symbol, and the meaning of that symbol is recorded by the defining equality

```
  ∀x̄. ε(λx. φ) = F(x̄)
```

The rest of the proof only sees the small term `F(x̄)`.

### 1.5 Assumptions and their discharge

Both naming devices introduce a symbol that the caller's problem does not contain, and record its meaning in an
auxiliary formula. Those auxiliary formulas are not consequences of the caller's hypotheses, so they cannot
simply be added to the proof as facts. They are carried as assumptions, meaning they appear on the left side of
the sequents of the part of the proof that uses them, and are removed before the proof is complete.

Removing one is a two-step argument, and it is the same argument in both cases. The introduced symbol is a
kernel schema variable, so the kernel's `InstSchema` rule can substitute a value for it. Substituting the value
the symbol was intended to abbreviate turns the auxiliary formula into a triviality: the definition becomes
`∀x̄. ψ ⇔ ψ`, and the defining equality becomes `∀x̄. t = t`. Each is provable outright, in a single restate step. A `Cut` against that proof removes the assumption.

Assumptions are discharged in reverse order of introduction.

One restriction follows from this design:`InstSchema` may not instantiate a
variable that occurs free in an assumption still in scope. Every phase after the conjecture is negated runs
inside the scope of the assumption `¬φ`, and deeper phases run inside the scope of the definitions as well. Any
variable that the pipeline or prover needs to instantiate cannot be free in these assumptions, otherwise that occurence would be instantiated as well. Section 2.4 describes how the package removes this possibility.

### 1.6 Certified and uncertified conversion

The package provides certified (proof-producing) clausification for the kernel, and non-certified for pure speed.

| | guarantee | cost | used for |
|---|---|---|---|
| certified | a kernel proof that the clauses entail the goal | proof construction | the `Superpose` tactic, and any result the kernel must check |
| uncertified | none explicit, but a proof exists (unless there is a bug)| clause computation only | competition mode, benchmarking |

The uncertified conversion is free to introduce fresh function symbols without going through the proofs for naming, because
equisatisfiability is all it claims. It is a single pass and produces no proof.

Having both is useful beyond speed. The uncertified conversion is a reference implementation of the same
transformations, so the two can be compared stage by stage, and the difference in their running times measures
the cost of proof construction rather than of clausification.

## Part 2: Implementation

### 2.1 Entry points

| entry point | file | result |
|---|---|---|
| `CertifiedClausifier.certifyClausal(problem, prover)` | [CertifiedClausifier.scala](CertifiedClausifier.scala) | a kernel `SCProof` of the goal |
| `UncertifiedClausifier.clausalForm(problem)` | [UncertifiedClausifier.scala](UncertifiedClausifier.scala) | the clause set alone |
| `UncertifiedClausifier.clausalProblemWithOrigins(problem)` | [UncertifiedClausifier.scala](UncertifiedClausifier.scala) | the same, each clause paired with the index of the formula it came from |

The input type is `Problem`, defined in [../Problem.scala](../Problem.scala) and shared with the prover: a sequence
of hypotheses, an optional conjecture, and a set of `frozen` variables. Each hypothesis and the conjecture must
be a sequent with an empty left side and exactly one formula on the right. The `frozen` set holds variables that
downstream phases must treat as uninterpreted constants rather than universally quantify; Skolem function
symbols are added to it as they are created.

The `prover` argument is a continuation rather than a return value. `certifyClausal` calls it partway through
its own descent, receives a kernel proof of the empty sequent from the clauses, and splices that proof into the
one it is building. This is why the contract stated in Section 1.1 requires the prover's conclusion to be
exactly the empty sequent.

### 2.2 The certified pipeline

Each phase has the shape `(Problem, ClausificationProver) => ClausificationProof`. It transforms the problem,
calls its continuation on the transformed problem, and wraps the result in the steps that bridge the two. The order below is the order of the transformations from Section 1.3.

| order | phase | file | transformation |
|---|---|---|---|
| 1 | screening | [ScreenPhase.scala](ScreenPhase.scala) | rename every free input variable; expand every quantifier to explicit lambda form |
| 2 | negation | [NegatedPhase.scala](NegatedPhase.scala) | move the conjecture `φ` to the hypotheses as `¬φ`, freezing its free individual variables |
| 3 | naming | [NamingPhase.scala](NamingPhase.scala) | replace subformulas above the threshold by `nm(x̄)`, adding their definitions |
| 4 | negation normal form | [NnfPhase.scala](NnfPhase.scala) | eliminate `⇒` and `⇔`, push negation to the atoms |
| 5 | Skolemization | [SkolemPhase.scala](SkolemPhase.scala) | remove `∃` using epsilon terms, then abbreviate each as `esk(x̄)` |
| 6 | quantifier stripping | [PrenexPhase.scala](PrenexPhase.scala) | remove every `∀`, instantiating at a fresh variable `w` |
| 7 | distribution | [DistributePhase.scala](DistributePhase.scala) | distribute `∨` over `∧` to obtain the clauses |

Below phase 2 the conjecture is always absent (it's the empty sequent), and every later phase requires this of its input.

Phase 2 also adds the conjecture's free individual variables to `frozen`. A goal `φ(x̄)` asserts `∀x̄. φ(x̄)`, so
`x̄` must not be instantiable: left as clause variables they would refute only `∃x̄. φ`, a weaker statement that
does not yield the intended conclusion. Freezing them makes the prover treat them as symbols, which is what
closing them universally and Skolemizing the resulting `∃x̄. ¬φ` would achieve, without introducing an `∃` and
therefore without a Skolem definition or a step to recover the original goal.

### 2.3 Representation of proofs under construction

A phase does not emit a kernel `SCProof` directly, because Section 1.5 requires a part of the proof to carry
assumptions on the left side of its sequents while the phase that introduced them is still assembling their
discharge. [ProofIR.scala](ProofIR.scala) supplies the intermediate representation.

| type | role |
|---|---|
| `ClausificationProof` | a list of steps together with an import list, mirroring `SCProof` |
| `ClausificationProofStep` | either a kernel `SCProofStep` or a `ClausificationSubproof` |
| `ClausificationSubproof` | a nested `ClausificationProof`, some of whose imports are declared as assumptions, by index |

`clausificationProofToSCProof` converts this representation into a kernel `SCProof`. For each assumption it adds
the assumed formula to the left side of the steps that need it, and inserts one `RestateTrue` step, proving the
tautology `assumptions ⊢ φ`, to account for the corresponding import. Only the steps whose premises reach an import can be affected by an
assumption, so the others are left unchanged, which keeps the conversion proportional to the number of steps that
genuinely depend on the assumption.

A kernel `SCSubproof` is converted exactly like a `ClausificationSubproof` that declares no assumption of its
own, so the two follow the same rule at every depth.

One restriction applies to both and is checked rather than assumed. The imports of a converted subproof receive
the assumptions handed to it, and the kernel matches each of those imports against the parent step that
discharges it, so such a step must be one that also received them, that is, one whose premises reach an import.
The phases respect this: every step `DistributePhase` cites, for instance, is a `Weakening` of an axiom import.

### 2.4 Names

Every fresh name the package generates is declared in `Clausification.GeneratedNames`, in
[Clausification.scala](Clausification.scala).

| prefix | sort or role | introduced by |
|---|---|---|
| `v` | individual variables of the input (`Ind`) | screening |
| `P` | predicate symbols of the input (`Ind → … → Ind → Prop`) | screening |
| `F` | function symbols of the input (`Ind → … → Ind → Ind`) | screening |
| `nm` | definitional naming predicate | naming, in both conversions |
| `esk` | Skolem function symbol abbreviating an epsilon term | Skolemization |
| `u` | bound variable inside a Skolem term | Skolemization |
| `w` | clause variable replacing a stripped `∀` | quantifier stripping, in both conversions |
| `HOLE` | placeholder marking a rewrite position in a proof | proof construction |

Two conventions are worth stating because other code depends on them. Each prefix is short and purely
alphabetic, and the numeric part of a generated name always lives in the counter field of the kernel
identifier rather than in its text.

Screening exists to enforce Section 1.5's restriction. It renames every free variable of the input into the
three namespaces above, choosing between them by the sort the symbol ultimately returns, which is `Prop` for a
predicate of any arity and `Ind` for a function or an individual. It runs at the very top of the pipeline,
above negation, because at that point every sequent still has an empty left side and a renaming by `InstSchema`
is therefore legal at every sort. Renaming is applied to all input variables rather than only to those that
collide, so that afterwards the absence of input names outside `v`, `P` and `F` holds by construction.

The predicate namespace shares its prefix with `schemaP`, the placeholder `P` of the library theorem, so the
two are kept apart by the counter: screening numbers from 1, making `P_1` the first screened predicate and
leaving the bare `P` to the schema. Without that, the first screened predicate of every problem would be the
very symbol the Skolem bridge instantiates, which is the fault screening exists to remove.

Screening has a second task. The kernel's beta normal form contracts `λy. p(y)` to `p`, so `∀y. p(y)` can be
presented as an application of `∀` to `p` with no lambda in it. The extractors that the phases match on require
an explicit lambda, so such a quantifier would be treated as an atom, travel through the pipeline unchanged,
and reach a clause as an opaque literal. Screening expands every quantifier into explicit lambda form, which
establishes the shape that the phases below rely on. The expansion is invisible to the kernel, which compares
formulas up to beta-eta normal form, so it costs no proof step.

### 2.5 Library theorems

The pipeline uses one theorem of the Lisa library, `(∃x. P(x)) ⇔ P(ε(λx. P(x)))`, the witness adequacy
statement of Section 1.3. It is listed as `Clausification.libImports`, supplied by the caller of the tactic,
and appears at the end of the import list of every proof the package produces.

Four prenex equivalences, `(∀x. P(x)) ∧ R ⇔ ∀x. (P(x) ∧ R)` and its three variants, used to sit beside it.
They served a second quantifier-stripping strategy, which lifted each quantifier to the root before stripping
it there, giving a proof proportional to the number of quantifiers times the depth rather than to the size of
the formula. Measured over the 944 equality-free FOF theorems, that strategy roughly doubled both proof size
and time and failed 19 problems the present one handles, so it and the four theorems were removed.

### 2.6 The uncertified conversion

[UncertifiedClausifier.scala](UncertifiedClausifier.scala) implements the whole uncertified pipeline: selective
naming, negation normal form, one Skolemization pass directly using with fresh function symbols instead of epsilon terms, and
distribution.
It freezes the conjecture's free individual variables as phase 2 does, and performs the same quantifier
expansion as screening, both at its own entry point.

### 2.7 Shared support

| file | contents |
|---|---|
| [Clausification.scala](Clausification.scala) | the `Problem` type, the generated names, the library theorems, assumption discharge, size estimation, and the shared helpers |
| [NamingSupport.scala](NamingSupport.scala) | creation of a naming predicate over a subformula's free variables, and the small proofs that discharge a definition |
| [ProofIR.scala](ProofIR.scala) | the intermediate proof representation and its conversion to `SCProof`, described in Section 2.3 |

`Clausification.checkInterrupted` is called at every point in the pipeline where work can grow without bound.
It observes thread interruption and available heap, so that a caller with a time budget can stop a conversion
that has begun to blow up. The benchmark harnesses depend on this.

### 2.8 Reading order

The sections above are arranged by topic. To read the source itself, the order below works better: it follows
the package's dependencies, so with one deliberate exception nothing refers forward to something not yet read.
Where the dependencies leave a choice, the order follows the pipeline of Section 2.2.

| order | file | why it sits here |
|---|---|---|
| 1 | [ProofIR.scala](ProofIR.scala) | the proof representation every phase produces, and the conversion that turns it into a kernel proof. It uses nothing from the package, so nothing precedes it |
| 2 | [Clausification.scala](Clausification.scala) | the vocabulary: `Problem`, the generated names, the library theorems, and the `ClausificationProver` type, which is a function from a problem to a `ClausificationProof` and so needs ProofIR first |
| 3 | [UncertifiedClausifier.scala](UncertifiedClausifier.scala) | every transformation of Section 1.3 in one pass and without a proof. Read early as the overview: it is the shortest complete account of what clausification does here, and the certified pipeline below is the same work carried out so that each step can be justified |
| 4 | [NamingSupport.scala](NamingSupport.scala) | how a naming predicate is created and how its definition is discharged, used by the naming phase and by Skolemization |
| 5 | [ScreenPhase.scala](ScreenPhase.scala) | the first phase, and the one that establishes the name and shape invariants the rest assume |
| 6 | [NegatedPhase.scala](NegatedPhase.scala) | where the conjecture goes, and where the prover contract comes from |
| 7 | [NamingPhase.scala](NamingPhase.scala) | the phase that introduces a symbol and must discharge it, and the one whose decisions the two conversions must agree on |
| 8 | [NnfPhase.scala](NnfPhase.scala) | the smallest phase, and the one whose certification is a single step |
| 9 | [SkolemPhase.scala](SkolemPhase.scala) | the same discharge machinery as naming, over ε-terms |
| 10 | [PrenexPhase.scala](PrenexPhase.scala) | one derivation per axiom, mirroring the formula's own tree |
| 11 | [DistributePhase.scala](DistributePhase.scala) | the last phase, where the clauses are finally built |
| 12 | [CertifiedClausifier.scala](CertifiedClausifier.scala) | the composition root, read last because it is the only file that mentions all the others |

Three points are worth knowing before starting.

Position 3 is the exception to the dependency order. `UncertifiedClausifier` reuses `NamingSupport` and
`NnfPhase.toNNF`, both of which come later, so two of its calls point forward. Reading it there is still worth
the cost, because it shows the whole conversion at a size that fits in one sitting, and everything after it is
then a matter of how each step is justified rather than what it does.

Phases 5 to 11 do not depend on each other at all. Each depends on `Clausification` and `ProofIR`, and
`NamingPhase` and `SkolemPhase` on `NamingSupport` as well, but none of them names another. They are connected
at run time by the continuation each is passed, not by any reference between them. Their order in the table is
therefore the pipeline order rather than a constraint, and any one of them can be read on its own.

`CertifiedClausifier.scala` is read last because it is the composition and nothing else. Its dependency on
`UncertifiedClausifier` is narrow: the default naming threshold, and the oracles that let
`ClausifierEquivalenceTest` compare the two conversions stage by stage.

### 2.9 Tests

Tests are in [`../../../../../test/scala/lisa/automation/clausification/`](../../../../../test/scala/lisa/automation/clausification/).

| suite | subject |
|---|---|
| `CertifiedClausificationTest` | the pipeline end to end, including a satisfiable problem asserted not to be refuted |
| `CertifiedFastEquivalenceTest` | the certified and uncertified conversions compared stage by stage |
| `AdversarialInputTest` | each precondition of the pipeline, paired with the input that violates it |
| `ProofIRTest` | the conversion, which steps receive the assumptions, and the restriction on subproof premises |
| `PrenexPhaseTest` | quantifier stripping where the quantifier's sibling mentions its binder free |
| `ScreenPhaseTest`, `DistributePhaseTest`, `NamingSupportTest` | the individual phases named |
