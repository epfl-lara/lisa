# Superposition

This package semi-decides whether a set of clauses is contradictory, and when it does, produces a
kernel proof of the empty sequent from the clause sequents. That engine is the back end of the
[clausification package](../clausification/), which converts a first-order problem into clauses and expects
exactly such a proof in return. On the other side of it sits the front end, which takes an unclausified
problem and drives the whole path: preprocessing, clausification, search, and the justification the caller
asked for. Section 2.1 is the way in.

The text below first states the theory, then the implementation.

## Part 1: Theory

### 1.1 Goal and direction of work

The caller has a goal and wants a kernel proof of it. As explained in the clausification package, the goal is
not proved directly. Its negation is added to the hypotheses, the result is converted to clauses, and the
prover attempts to derive a contradiction from them. Deriving a contradiction means deriving the empty clause,
which represents falsity. The search itself assumes the problem is already in clausal form.

The prover does this by *saturation*. It repeatedly applies inference rules to the clauses it has, adding the
conclusions to the set, until one of three things happens.

| outcome | meaning |
|---|---|
| refutation | the empty clause was derived, so the clause set is contradictory and the goal holds |
| saturation | no rule application produces anything new, so the clause set is satisfiable and the goal does not follow |
| exhaustion | a budget on time or on the number of steps ran out, so nothing is known |

Saturation is not a failure: It means (unless bug) that the problem is not first-order valid. A rule set is *refutation-complete* when every contradictory clause set has a derivation of
the empty clause. Every rule and every restriction described below preserves refutation completeness, and the
places where the package deliberately gives it up are marked.

First-order logic is only semi-decidable, so on a satisfiable set the search may run forever rather than report
saturation. This is why the third outcome exists.

### 1.2 Clauses

The representation is the one the clausification package produces. A literal is an atom or a negated atom, a
clause is a finite disjunction of literals, and a clause is carried as a kernel sequent under the usual
reading, so that

```
  a₁, …, aₘ ⊢ b₁, …, bₙ
```

represents `¬a₁ ∨ … ∨ ¬aₘ ∨ b₁ ∨ … ∨ bₙ`. The empty sequent represents the empty clause. A clause contains no
quantifiers, and its free individual variables may be instantiated freely.
statement follows from it.

A clause with no variables is *ground*. A *substitution*  `σ` maps variables to terms. A *unifier* of two terms is a substitution making them equal. A *matcher* from `s` to `t` is a substitution with
`sσ = t` which binds only the variables of `s`, leaving `t` fixed. The distinction between unification and
matching decides, throughout, whether a rule generates a new clause or simplifies an existing one.

### 1.3 Restricted resolution

The basic rule on clauses is binary resolution. From `C ∨ A` and `D ∨ ¬B`, where `σ` is a most general unifier
of the atoms `A` and `B`, it derives `(C ∨ D)σ`. It is completed by factoring, which from `C ∨ A ∨ B` derives
`(C ∨ A)σ` when `σ` unifies `A` and `B`. Together they are refutation-complete.

However, such deductions quickly explode in size. The rest of the section explain how to mitigate this, with two strategies.

The first is to *restrict* which inferences are performed. If enough inferences can be forbidden while
retaining refutation completeness, the search space shrinks without any answer being lost. Sections 1.4 to 1.6
describe the restrictions used here.

The second is to *delete* clauses that cannot contribute to a refutation. Section 1.7 describes those.

### 1.4 The term ordering

The restrictions rest on an ordering `≻` on terms with four properties: it is a strict partial order, it is
stable under substitution (if `s ≻ t` then `sσ ≻ tσ`), it is monotone with respect to context (replacing a
subterm by a smaller one makes the whole term smaller), and it contains the subterm relation. An ordering with
these properties is a *simplification ordering*. It is also required to be total on ground terms, so that any
two variable-free terms are comparable.

The solver uses the Knuth-Bendix ordering. It gives each symbol two independent parameters: a *weight* (a
non-negative integer) and a *precedence* (a position in a total order on the symbols). The weight of a term is
the sum of the weights of its symbols, counting variables as a fixed weight. Two terms are compared by weight
first; on equal weight, by the precedence of their head symbols; on equal head symbols, by comparing their
arguments left to right. Additionally, the verdict is discarded, and the terms declared incomparable, unless the larger term contains each variable at least as often as the smaller one. That last condition is what makes the ordering
stable under substitution.

On non-ground terms the ordering is partial, and incomparability is common: `f(x)` and `f(y)` are unrelated,
and so are `x` and `a`. Every use of the ordering below must treat incomparability conservatively,
by permitting the inference rather than forbidding it.

The choice of weights and precedences is free, but changes how the search behaves. The usual default is that
symbols occurring frequently in the problem receive small precedences, so that terms are rewritten toward the
common vocabulary and rare symbols are eliminated first.

The ordering on terms is extended to literals and then to clauses by multiset comparison. A literal is
*maximal* in a clause when no other literal of that clause is strictly greater.

### 1.5 Equality

Equality can be treated as an ordinary predicate together with axioms for reflexivity, symmetry, transitivity
and congruence. This is complete but less efficient.

Instead, equality is built into the calculus with the rules below.

| rule | from | derives | condition |
|---|---|---|---|
| superposition | `C ∨ l ≈ r` and `D[u]` | `(C ∨ D[r])σ` | `σ` unifies `l` and `u`, `u` is not a variable, and `lσ ⋡ rσ` |
| equality resolution | `C ∨ s ≉ t` | `Cσ` | `σ` unifies `s` and `t` |
| equality factoring | `C ∨ s ≈ t ∨ s' ≈ t'` | `(C ∨ t ≉ t' ∨ s' ≈ t')σ` | `σ` unifies `s` and `s'`, with ordering conditions on the sides |

Superposition is the central rule. It rewrites an occurrence of `l` inside another clause by `r`, having first
unified. The condition `lσ ⋡ rσ` means the equation is used only in the direction that makes terms smaller, so
an equation between incomparable sides may be used in both directions and one between comparable sides only in
one.

Two further restrictions apply to all inference rules: an inference may only involve a
literal that is *eligible* in its clause, and superposition may only rewrite into a maximal side of a maximal
literal. Eligibility is the subject of the next section.

### 1.6 Literal selection

The rules above are restricted further by choosing, in each clause, a subset of its literals that alone may
take part in inferences. Such a choice is a *selection function*, and the Bachmair-Ganzinger completeness
result states the conditions under which one preserves refutation completeness: either a negative literal is
selected, in which case that clause may be used only through it, or no negative literal is selected and all
maximal literals are selected.

This still leaves a lot of freedom. Selecting a single negative literal in a clause with many of them
removes every inference on the others, which is a large reduction. Which negative literal is selected a heuristic choice.


### 1.7 Redundancy

A clause is *redundant* in a set when it follows from clauses of that set that are strictly smaller in the
clause ordering. Redundant clauses may be deleted without affecting refutation completeness, because anything
derivable through them is derivable without them. The forms used here are the
following.

| simplification | effect |
|---|---|
| tautology deletion | a clause containing a literal and its complement is discarded |
| subsumption | if some instance of `C` is contained in `D`, then `D` is discarded |
| subsumption resolution | if some instance of `C` is contained in `D` except for one literal, whose complement it matches, that literal is removed from `D` |
| condensation | a clause is replaced by a shorter instance of itself when that instance still entails it |
| demodulation | a clause is rewritten by an equation `l ≈ r` where some subterm matches `l` and `r` is smaller |

Two properties of this list matter later.

The first concerns matching. Subsumption and demodulation use matching rather than unification, so the clause
being simplified is not instantiated. This is what makes them simplifications: the result entails the original,
so the original may be deleted.

All the simplification rules are special cases of the above inference rules and for matters of proofs are justified the same way. The deletion itself requires no proof.

### 1.8 The saturation loop

The clauses are divided into two sets: the *active*
set, in which every pair has already been considered, and the *passive* set, which is waiting. One iteration
picks a clause from the passive set, called the given clause, performs every inference between it and the
active clauses, moves it into the active set, and places the conclusions in the passive set.

Simplification is applied in both directions. *Forward* simplification uses the active set to delete or shorten
the given clause, and *backward* simplification uses the given clause to delete or shorten active clauses.

Which clause is chosen from the passive set is a heuristic decision. Choosing small
clauses finds short proofs quickly, but completeness requires that every clause is eventually chosen. The two are combined by
alternating between them in a fixed ratio, which is fair as long as the age share is non-zero.

### 1.9 Retrieval

Each iteration must find, among the active clauses, the partners for every rule. Scanning the whole active set at each iteration is slow, and the active set grows throughout the run.

The standard remedy is an *index*: a data structure that, given a query term, returns a small superset of the
terms that could match or unify with it according to the inference and simplification rules. The candidates it returns are then checked exactly.

### 1.10 Proof reconstruction

A derivation of the empty clause is a directed acyclic graph. Its leaves are the input clauses, its internal
nodes are the conclusions of rules, and each node records which rule produced it and from which premises. The search may explore any number of dead ends, but only the
subgraph reaching the empty clause is turned into a proof.

Each rule of Sections 1.3 and 1.5 is easily represented in the kernel. Instantiation of a clause by a substitution
is a schema instantiation, resolution is instantiation of both premises followed by a cut on the resolved atom,
and the equality rules are simulated by the kernel's substitution rules for equality. The resulting proof has the clause
sequents as its imports and the empty sequent as its conclusion, which is the contract the clausification
package requires.

## Part 2: Implementation

### 2.1 Entry points

The three entry points in [Prover.scala](Prover.scala) all take the same thing, an unclausified `Problem`
([../Problem.scala](../Problem.scala)) with every other parameter in one `SearchOptions`, and differ only in the
justification asked for. That difference is what picks the clausifier.

| entry point | result | clausifier |
|---|---|---|
| `Prover.solve(problem, opts)` | the verdict alone, no proof built | uncertified |
| `Prover.proveKernel(problem, opts)` | a kernel `SCProof` of the goal | certified |
| `Prover.proveTstp(problem, opts)` | a TSTP derivation, which needs no kernel justification | uncertified |

Both proving entry points return a proof of the problem's goal — its conjecture, or `⊢` when it has none —
whose imports are the hypotheses, pointwise and in order, followed by the clausifier's library imports.

Preprocessing runs before clausification, as a phase with a continuation. SInE axiom selection only ever
removes hypotheses, so nothing justifies it: the kernel version widens the finished proof's import list back to
the caller's. Orthologic normalisation rewrites each formula to an OL-equal one, so its kernel version is one
`Restate` per hypothesis plus one for the goal.

`Superpose` ([Superpose.scala](Superpose.scala)) is the tactic a Lisa proof uses: it accepts a sequent of any
shape, with either side possibly empty, and cited facts are folded in as hypotheses. Since the clausifier takes
a single formula, the goal `Γ ⊢ Δ` is passed as `⋀Γ ⇒ ⋁Δ`. `CascProver` ([CascProver.scala](CascProver.scala))
is the command line over one TPTP file.

The three outcomes of Section 1.1 are the cases of `Clausal.Outcome`: `Success`, which carries everything needed
to reconstruct the proof, `Saturated`, and `Timeout`. A budget is enforced cooperatively, checked once per
iteration of the loop, so a run that exceeds it stops in a defined state rather than being abandoned.

### 2.2 Terms, literals and clauses

[Core.scala](Core.scala) holds a low-level representation of terms and clauses.

Terms live in a single flat array owned by a `TermBank`, and a term is the offset of its record in that array.
The type `Term` is therefore an (opaque) integer. A `Literal` packs a term together with a sign into a single machine word. A `Symbol` is an index
assigned by a `Signature`, which also stores each symbol's arity, weight and precedence.

A variable is not a separate kind of record. It is written directly in the head field of a term as a negative
number, so a term is a variable exactly when that field is negative.

Every term caches the set of variables occurring in it, as a bit mask of sixty three bits, with the top bit
meaning that some variable numbered too high to represent occurs. A term is ground exactly when its mask is
zero, which is the test that lets the ordering and the indices take fast paths on ground terms.

Terms are *hash consed*: constructing a term that already exists returns the existing one. Equality of terms is
therefore comparison of two integers, and sharing is automatic.

A `Clause` holds an array of literals, a unique identifier, its weight, its age, the record of the rule that
produced it, and several cached quantities computed once when the clause is first used. `Justification` is the
record described in Section 1.10, with one case per rule.

### 2.3 Substitution

Unification, matching and the application of substitutions are the work of `Trail`, also in
[Core.scala](Core.scala). Bindings are stored in arrays indexed by variable number, and every binding is
recorded on a stack to enable backtracking.

Section 1.2 requires the variables of two clauses to be kept apart. Rather than renaming one of them, the trail
tags each operand with a *scope*, either 0 or 1, and treats the same variable number in different scopes as
different variables. Rules that combine two clauses use both scopes, rules that work within one clause use one.

Building a conclusion from a trail state
is the job of an `Applier`, which applies the current bindings and renumbers the surviving variables so that
the new clause starts from zero again.

### 2.4 The ordering

| file | contents |
|---|---|
| [ordering/KBO.scala](ordering/KBO.scala) | the Knuth-Bendix ordering on terms, returning `Gt`, `Lt`, `Eq` or `Inc` |
| [ordering/Order.scala](ordering/Order.scala) | orientation of equations, the literal ordering, maximality, and the clause ordering |
| [ordering/Precedence.scala](ordering/Precedence.scala) | generation of the symbol precedences from the input |
| [ordering/Selectors.scala](ordering/Selectors.scala) | the selection functions of Section 1.6 |

`KBO` implements the linear algorithm of Löchner rather than the definition of Section 1.4 read literally. The
two terms are traversed once together, accumulating the weight difference and, per variable, the difference in
number of occurrences. The variable condition then reduces to a counter reaching zero, and the comparison is
linear in the size of the terms rather than quadratic. The accumulators are reused between calls, so an
instance is not safe to share between threads. The whole search is single-threaded.

`Order` lifts this to literals and clauses. An equality literal is compared as the multiset of its sides, `{s, t}`
when positive and `{s, s, t, t}` when negative, which makes a negative equation larger than the positive one on
the same terms. Equality literals rank below every non-equality literal. `Order` also memoises the orientation
of each equation, keyed on the term, since orientation is asked for repeatedly and does not change during a run.

`Precedence` assigns the precedences to symbol once, before the search starts, from the symbol counts of the input
clauses. Four schemes are available; the default makes frequent symbols small, as Section 1.4 describes.

`Selectors` provides three selection functions. `Complete` is the one satisfying the conditions of Section 1.6,
and is the default: it selects a negative literal when one exists, choosing the one of highest quality by a
fixed measure, and otherwise selects every maximal literal. `FirstNegative` and `BestLiteral` are
incomplete heuristics, used only as members of the portfolio of Section 2.10.

### 2.5 Generating inferences

[Inference.scala](Inference.scala) holds resolution and factoring, and
[Superposition.scala](Superposition.scala) the three equality rules of Section 1.5. All follow one shape: save
the trail position, unify, check the ordering conditions on the result, build the conclusion through an
`Applier`, record the `Justification`, and restore the trail. The caller's trail state is unchanged whether or
not the rule applied.

Superposition departs from this shape in one respect. The position at which to rewrite is found by the caller,
through the index of Section 2.8, and the caller has already unified when it calls in.
`Superposition.superpose` therefore receives a trail that already carries the unifier, checks the conditions
and builds the conclusion, and leaves the surrounding save, unify and restore to the caller.

Eligibility is likewise the caller's responsibility. The rules therefore check only the ordering
conditions on terms, which are independent of selection, and the loop passes only eligible literal positions.

`Inference.canonicalize` puts a new clause into a normal form before it is stored: the literals are sorted into
a fixed syntactic order, duplicates are removed, and a clause containing complementary literals is reported as
a tautology and discarded.

### 2.6 Simplification

| file | contents |
|---|---|
| [Subsumption.scala](Subsumption.scala) | the subsumption test, subsumption resolution and condensation |
| [Demodulation.scala](Demodulation.scala) | rewriting by positive unit equations |
| [Simplifier.scala](Simplifier.scala) | every simplification of Section 1.7, in both directions |

`Subsumption.subsumes` decides whether some instance of one clause is contained in another. It must find a witness: one substitution under which every literal of the first clause becomes a literal of the
second, and injectively. It builds that assignment literal by literal, backtracking when a choice
cannot be completed, and takes the most constrained literal first so that a hopeless branch is abandoned early.
It is preceded by a test on cached quantities alone, comparing sizes, the counts of positive and negative
literals, weights, and a bit mask of the head symbols present. Each of these is implied by subsumption, so the
test never rejects a genuine case, and it rejects the large majority of pairs before any substitution work.

`Demodulation` performs the rewriting of Section 1.7. A rewrite replaces a subterm by a smaller instance, so
repeated rewriting terminates, and each step records its own `Justification`. Rewriting a clause with an
equation does not always make the clause redundant, and where it does not, the rewrite is skipped and the
inference is left to superposition, which handles it correctly.

`Simplifier` owns the decisions about when each of these runs. Every retrieval goes through an index. Since
Section 1.9 makes an index a filter over the same exact test that would decide a candidate found by any other
means, the set of simplifications performed is the calculus's and not the index's; redundancy that a different
retrieval order would have caught earlier is caught when the clause is later selected. Each direction had a
second, linear-scan implementation beside the indexed one for a time, so that the two could be compared while
the indices were being brought up; those are gone, and the tests pin the verdict of the surviving path instead
of comparing two.

### 2.7 The loop and the clause sets

| file | contents |
|---|---|
| [Discount.scala](Discount.scala) | the given-clause loop of Section 1.8 |
| [Generator.scala](Generator.scala) | every generating inference performed on a given clause |
| [ActiveSet.scala](ActiveSet.scala) | the active clauses and every index over them |
| [PassiveSet.scala](PassiveSet.scala) | the passive clauses and the choice of the next given clause |

`Discount` is the loop itself. One iteration takes a clause from the passive set, rewrites it to normal form
against the active equations, forward simplifies it, and discards it if it was subsumed. Otherwise it moves it
into the active set, generates every resolvent, factor and superposition against the active clauses, and places
the survivors in the passive set. It stops on the empty clause, on an empty passive set, or on a budget.

The two halves of the work each have their own file, so that what is left in `Discount` is the iteration, the
two clause sets, and the single decision about where a new clause goes. `Generator` performs the inferences of
Sections 1.3 and 1.5 on the given clause, taking its partners from the indices, and `Simplifier` the deletions
and shrinkings of Section 1.7. Both hand their conclusions back through a callback, since the passive set is the
loop's to own.

`PassiveSet` holds two views of the same clauses, one ordered by age and one by weight, and alternates between
them in the ratio of Section 1.8. A clause taken through one view remains in the other as a stale entry and is
skipped when reached, which avoids the cost of deleting from both.

`ActiveSet` holds the clauses and, alongside them, the derived structures that hold the same clauses
keyed differently, so that each query of Section 1.9 is answered quickly. `add` and `remove` are the only entry points, and each touches every structure, so the obligation is discharged in one place rather than at every call site in the loop.

### 2.8 Indexing

Three indices implement Section 1.9, one per query type.

| file | query | method | used by |
|---|---|---|---|
| [index/Fingerprint.scala](index/Fingerprint.scala) | terms that may unify with a query term | a fixed vector of sampled positions | superposition, on both sides of the overlap; ordinary resolution; backward demodulation |
| [index/FeatureVector.scala](index/FeatureVector.scala) | clauses that may subsume, or be subsumed by, a query clause | a trie over counting features | subsumption and subsumption resolution, both directions; unit deletion |
| [index/DiscriminationTree.scala](index/DiscriminationTree.scala) | equations whose left side matches a query subterm | a tree over the symbols of the left sides | forward demodulation |

A *fingerprint* samples a fixed set of positions in a term and records at each what is found there: a concrete
symbol, a variable, a position below a variable, or a position that cannot exist even in an instance. Two terms can unify only if their fingerprints are compatible at every sampled position, so
comparing fingerprints rejects most pairs at the cost of a few integer comparisons. Terms that genuinely unify
always have compatible fingerprints.

A *feature vector* counts quantities that cannot decrease under subsumption, such as the number of literals,
the numbers of positive and negative literals, and the number of occurrences of each of a chosen set of
symbols. If `C` subsumes `D`, then `C`'s vector is componentwise at most `D`'s. Storing the clauses in a trie
keyed by these vectors turns the search for candidate subsumers into a descent through the part of the trie
below the query's vector. The features are chosen once from the initial clause set, with the most discriminating
placed at the shallow levels.

The *discrimination tree* stores the left sides of the unit equations in flattened form and retrieves by descending
with the query subterm. It is *perfect*, meaning that reaching a leaf establishes the match outright, because
the descent binds the equation's variables on the trail as it goes and checks consistency. No separate
verification step is needed. Each node also records the smallest left side beneath it, and since matching can
only make a term larger, a subtree whose smallest entry is heavier than the query is skipped.

### 2.9 Reconstruction

| file | contents |
|---|---|
| [Reconstruction.scala](Reconstruction.scala) | the derivation graph turned into a kernel proof |
| [Clausal.scala](Clausal.scala) | conversion between kernel sequents and the internal representation, and the abstraction of non-first-order subterms |

`Clausal` converts a list of clause sequents into internal clauses, interning each symbol in the signature and
numbering each clause's variables from zero, and records what is needed to invert the conversion. It also
disables the equality rules when the input contains no equality at all, where they could never apply.

`Reconstruction` walks the justification from the empty clause. Each clause becomes one step
or one import, and the result is memoised by clause identifier, so a clause used several times is proven once.
Every clause is stated with variables in a canonical naming. The substitution used by an inference is not stored during the
search; it is recomputed by repeating the unification of the recorded literals, which is cheaper than keeping
every substitution for a search that mostly produces clauses no proof will mention.

It also replaces each non-first-order subterm by a fresh function
symbol applied to its free variables, using the same symbol for identical subterms so that the replacement is a
genuine function, and records the value of each symbol. The search runs on the abstracted problem.

The proof is not built on it. What the search returns is a record of which inferences fired on which clauses,
not a kernel proof, so reconstruction builds the proof itself and writes the original subterms in as it goes:
each import is declared with the values substituted back, and every term it rebuilds substitutes a symbol that
has a recorded value.

### 2.10 Search configuration

| file | contents |
|---|---|
| [SearchOptions.scala](SearchOptions.scala) | every parameter of the search, in one record passed unchanged through each layer that can configure one: clause selection, the ordering and selection function, and which simplifications run |
| [Strategy.scala](Strategy.scala) | a named point in that space, and the eight of them a competition run executes in parallel, taking the first refutation |
| [Sine.scala](Sine.scala) | axiom selection: keep only the hypotheses reachable from the conjecture through a relation on symbols, applied before clausification on problems with very many of them. Sound but incomplete, so `shouldFilter` decides per problem whether it is worth applying |
| [CascProver.scala](CascProver.scala) | the command line: read one problem, search under a wall clock budget, write a status line and, on a refutation, the derivation |
| [Tstp.scala](Tstp.scala) | that derivation, printed from the internal proof DAG rather than from a kernel proof |

These are the configuration surface for any caller, not only for competition. `Superpose` takes the defaults
and wires up none of the rest, including the two preprocessing phases, which are off by default. Only the eight
named strategies and the command line prover are specific to competition use.

### 2.11 Benchmarks

[bench/](bench/) holds the measurement harnesses. They are not tests; each has a `main`, and each requires the
`TPTP` environment variable to point at a problem library.

| file | subject |
|---|---|
| [bench/Harness.scala](bench/Harness.scala) | clausify, refute and kernel-check a dataset; settings are `key=value` arguments |
| [bench/Evaluation.scala](bench/Evaluation.scala), [bench/FofEvaluation.scala](bench/FofEvaluation.scala), [bench/EqFofEvaluation.scala](bench/EqFofEvaluation.scala) | that harness over the clausal, the equality-free FOF and the equality-bearing FOF datasets |
| [bench/BaselineBench.scala](bench/BaselineBench.scala) | throughput with no proof built, for comparison with other provers |
| [bench/StrategyEvaluation.scala](bench/StrategyEvaluation.scala) | the strategies of Section 2.10 against each other |
| [bench/BenchUtil.scala](bench/BenchUtil.scala) | the shared parts, including the problem lists and the seeded sampling |

One point about the results is recorded in `BenchUtil` and repeated here because it invalidates whole runs. A
problem is solved on its own thread under a time limit, and a thread that does not stop when asked cannot be
stopped on the Java virtual machine. It continues to consume processor time and memory for the remainder of the
run, so every problem measured after it is measured on a loaded machine. The harnesses count such threads and
report the run as contaminated. Running problems on a forked JVM bypass this problem, but has a longr startup time.

### 2.12 Reading order

The sections above are arranged by topic. To read the source, the order below works better, since it follows
the dependencies between the files: with the one exception noted after the table, nothing refers forward.

| order | file | why it sits here |
|---|---|---|
| 1 | [Core.scala](Core.scala) | terms, literals, clauses and the trail. Everything else is written in terms of these, and the representation cannot be inferred from its uses |
| 2 | [ordering/KBO.scala](ordering/KBO.scala) | the ordering on terms, which uses only the representation |
| 3 | [ordering/Order.scala](ordering/Order.scala) | the ordering on literals and clauses, built on `KBO` |
| 4 | [ordering/Precedence.scala](ordering/Precedence.scala) | where the precedences that `KBO` reads come from |
| 5 | [ordering/Selectors.scala](ordering/Selectors.scala) | the selection functions, which need the literal ordering |
| 6 | [Inference.scala](Inference.scala) | resolution and factoring, the smallest complete example of how a rule is written |
| 7 | [Superposition.scala](Superposition.scala) | the equality rules, in the same shape, with the ordering conditions of Section 1.5 |
| 8 | [Subsumption.scala](Subsumption.scala) | the subsumption test, used by simplification and by the clause index |
| 9 | [Demodulation.scala](Demodulation.scala) | rewriting, and the condition under which it may replace its premise |
| 10 | [SearchOptions.scala](SearchOptions.scala) | the parameters, read as a list of what the following files can vary |
| 11 | [index/Fingerprint.scala](index/Fingerprint.scala) | the first index, and the clearest statement of the filter and verify pattern |
| 12 | [index/FeatureVector.scala](index/FeatureVector.scala) | the clause index, whose candidates `Subsumption` then verifies |
| 13 | [index/DiscriminationTree.scala](index/DiscriminationTree.scala) | the equation index, generic in its payload, which demodulation instantiates at its rules |
| 14 | [PassiveSet.scala](PassiveSet.scala) | the smaller of the two clause stores, and the clause selection heuristic |
| 15 | [ActiveSet.scala](ActiveSet.scala) | the larger, and the place where the indices are kept in agreement |
| 16 | [Simplifier.scala](Simplifier.scala) | simplification in both directions, over the active set |
| 17 | [Discount.scala](Discount.scala) | the loop, which is short once everything it calls has been read |
| 18 | [Reconstruction.scala](Reconstruction.scala) | the derivation graph turned into a kernel proof |
| 19 | [Clausal.scala](Clausal.scala) | the kernel interface: clause sequents in and out, and the abstraction of non-first-order subterms |
| 20 | [Prover.scala](Prover.scala) | the front end, which composes preprocessing, clausification and the search into the three entry points |
| 21 | [Superpose.scala](Superpose.scala) | the tactic, read last because it is the composition of everything above |

`Core.scala` is the exception. `TermBank` holds the selection function of position 5 and the ordering of
position 3, and `Clause` calls into position 7 to compute its own eligible equation sides. These are the only
forward references in the file and can be passed over on a first reading.

[Strategy.scala](Strategy.scala), [Sine.scala](Sine.scala), [CascProver.scala](CascProver.scala) and
[Tstp.scala](Tstp.scala) sit above the whole package and can be read at any point after position 19. See
Section 2.10.

### 2.13 Tests

Tests are in [`../../../../../test/scala/lisa/automation/superposition/`](../../../../../test/scala/lisa/automation/superposition/).

| suite | subject |
|---|---|
| `KBOTest`, `OrderTest`, `PrecedenceTest` | the ordering, including randomised checks that it is total and transitive on ground terms, and that the literal comparison agrees with a direct implementation of the multiset definition |
| `MatchTest` | unification and matching, and that a failed attempt leaves no binding behind |
| `InferenceTest`, `SuperpositionTest`, `DemodulationTest` | the rules of Sections 1.3 and 1.5 |
| `SubsumptionTest` | the subsumption test and the simplifications built on it |
| `FingerprintTest`, `FeatureVectorTest`, `DiscriminationTreeTest` | each index against an exact enumeration of the candidates it should return |
| `DiscountTest`, `EqualitySaturationTest` | the loop, with the verdict pinned on one clause set per shape of inference and of redundancy |
| `ReconstructionTest`, `EqualityReconstructionTest` | reconstructed proofs, checked by the kernel |
| `ProverTest`, `BridgeTest`, `ClausalTest`, `SuperposeTacticTest` | the entry points of Section 2.1, including the proof contract they promise |
| `SineTest`, `SinePolicyTest` | axiom selection and the decision to apply it |
| `CascProverTest`, `SynBaselineTest` | the command line prover, and a sample of small problems that must continue to be refuted |

`SynBaselineTest` and the tests that read a problem library require the `TPTP` environment variable. Without it
they are cancelled rather than failed, so the suite runs anywhere.
