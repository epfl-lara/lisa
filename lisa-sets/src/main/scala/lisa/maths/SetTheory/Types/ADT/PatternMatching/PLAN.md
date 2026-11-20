# Unifying pattern validation and proof generation

Status: steps 1–4 implemented, 2026-11-16.

Use one resolved representation for constructor patterns and one retained decision tree for each collection of cases. Plain patterns are constructor nodes whose children are binders. Validation, coverage, branch selection, induction, and recursion must consume that same resolved structure. Functions continue to use the unified construction introduced in the preceding refactor.

The public `Case`, `fun`, `recFun`, and `Induction` syntax stays unchanged. Preserve the current typing and computation theorems, exhaustive and disjoint matching, specialization, and lookup modulo binder renaming. This work does not add case priority, arbitrary expression patterns, or semantic reasoning about whether arbitrary types are empty. CI wiring remains a separate change.

## Data and proof contracts

### Resolved patterns

Change [PatternValidation.scala](PatternValidation.scala) from checking and returning `Unit` to constructing a resolved pattern. Use sealed traits and case classes, with these two node forms:

```scala
sealed trait PatternNode
final case class Bind(variable: Variable[Ind], typ: Expr[Ind]) extends PatternNode
final case class Construct(
    constructor: Constructor[?],
    typeArguments: Seq[Expr[Ind]],
    arguments: List[PatternNode]
) extends PatternNode
```

Construction is internal to the validator. It checks constructor ownership, explicit type arguments, exact arities, expected child types, and binder linearity. A case has a `Construct` root. Constructor identities and type arguments remain available after validation; constructor names are only used in diagnostics. Types remain ordinary `Expr[Ind]`, including opaque parameters and function types at binder leaves.

Derive the expression denoted by a pattern, its ordered user binders, and its typing signature from this tree. A constructor node's result type comes from its constructor and type arguments. Do not maintain independently supplied copies of terms, guards, binder lists, or types that can disagree with the tree. Resolve constructor applications once at the input boundary; proof generation must not scan the ADT registry to rediscover them.

Keep clause payloads separate from pattern structure: `Clause[A](pattern, payload)`, with a function body or an induction proof as `A`. The compiled collection retains the ordered clauses and their decision tree. Clause indices refer to this fixed order; mapping payloads preserves the pattern objects and the tree. This removes the dummy function bodies currently used for induction.

### Decision tree

The typed tree in [DecisionTree.scala](semantics/DecisionTree.scala) replaces the old string-based trie:

- `Split`: an occurrence path, the specialized datatype at that path, and one edge per actual constructor.
- `Leaf`: the unique matching clause index and an ordered mapping from that clause's user binders to occurrence paths.

An occurrence path is a sequence of constructor-field indices, starting at the input. It identifies a value within a branch; it is not a generated proof variable. A binder can refer to a whole subtree when other clauses inspect that position more deeply.

Use the existing deterministic matrix-compilation approach: split the outer constructor first, then the leftmost remaining column containing constructor patterns. Specialize matching rows, discard different constructors, and propagate unconstrained columns for binder rows. Generated unconstrained columns need no invented user binder such as the string `_`.

A terminal state with no matching row reports a missing case; multiple matching rows report overlap. Return diagnostics through `Either`, with the occurrence path and relevant clauses/constructors. Only successful trees reach proof generation. Handle a datatype with no constructors by a zero-edge `Split`, whose proof is its empty elimination theorem, before applying the missing-row rule. This ordering accepts `Void` with no cases. Do not extend this into general emptiness analysis of field types.

### Proof-facing branch layout

Derive and retain a branch view from each resolved pattern. Preserve the existing order: outer constructor arguments first, then nested leaf binders. A nested argument gets a fresh outer binder and an equality guard relating that binder to the nested constructor term.

For example, `succ(succ(k))` has the user binder `k`, but its proof view still has an outer argument `a`, the inner binder `k`, and the guard `a = succ(k)`. Consumers currently rely on the outer argument count to separate these groups. Keep this layout while replacing their implementations.

The view supplies the current input term, typing assumptions, guard equalities, and existential witness order. It is derived once, with fresh names, and reused by the induction callback and final assembly. Generated proof eigenvariables and `proof.Fact` values remain local to each proof traversal. Freshening must account for ambient assumptions, the goal, clause binders, type arguments, and any function self-reference.

Induction hypotheses continue to follow the constructor signature's immediate `SelfRef` fields. Nested recursive agreement points additionally carry their field paths; each descent must be justified through the applicable `SelfRef` fields. A payload whose instantiated type happens to equal the domain does not acquire an induction hypothesis or height bound from that equality alone.

## Implementation sequence

### 1. Return and retain resolved patterns

Implemented in [PatternNode.scala](PatternNode.scala), the resolver, and the unified [Pattern.scala](semantics/Pattern.scala). Both function and induction compilation retain the resolved patterns; proof generation no longer reparses pattern expressions.

1. Add the two node forms and derived operations, preferably alongside the existing [Pattern.scala](semantics/Pattern.scala), keeping the file layout small.
2. Replace `validateCase` with a resolver returning the constructor-rooted tree. Reuse the existing strict application decoder and diagnostics.
3. Make [CaseAccumulator.scala](syntax/CaseAccumulator.scala) retain resolved cases once the domain is known. For functions, resolve the collected raw cases during compilation.
4. In [Case.subproof](syntax/Case.scala), resolve the case before executing its callback and store that same resolved pattern with the resulting proof. Final induction compilation must not parse the case again.
5. Derive the current plain/nested branch views from these nodes as temporary adapters. Replace the `Pat` and `RPat` parsers and migrate expression rendering, typed-binder collection, constructor typing, and case lookup to the resolved nodes.

Per-case validation must precede an induction callback. Whole-collection coverage and overlap checks still occur after collection under the existing DSL; do not claim to validate future cases before their callbacks are supplied.

Completion check: no parser inside proof generation; constructor specialization and arbitrary binder types survive resolution. Existing lookup tests still distinguish type arguments and preserve a bijection of value binders. Existing invalid-case tests still reject malformed input before its induction callback runs.

### 2. Compile and retain one typed decision tree

Implemented in [DecisionTree.scala](semantics/DecisionTree.scala). The accumulator compiles plain and nested clauses through the same coverage/overlap analysis and stores its tree on `PatternSystem`. The old trie and duplicate collection-validation checks are removed.

1. Replace `NestedTrie.compile/buildTree` with a compiler consuming the resolved clauses and specialized domain. Keep compiler and tree declarations together, for example in `semantics/DecisionTree.scala`.
2. Carry actual constructor references, specialized column types, occurrence paths, and binder assignments through compilation. Never compare constructors or binders through their printed names.
3. Run coverage and overlap analysis once. Store the successful tree on the compiled collection; render diagnostics from the same analysis.
4. Compile plain and nested cases through this path. Remove the separate top-level missing/duplicate-case algorithms once equivalent diagnostics come from the common compiler.
5. Preserve the original clause order and payload attachment even when the tree groups cases by constructor.

Completion check: one retained tree describes every accepted collection, including `Void` with no cases. Tests cover gaps, overlap, splits in multiple argument positions, and constructor identity across different datatypes. No definitions or proof generation are needed to decide these checks.

### 3. Reconstruct coverage and branch selection from the tree

Implemented in [PatternProofs.scala](semantics/PatternProofs.scala), used by the unified pattern system. Coverage traverses the retained root; branch selection traverses the known constructor's subtree using the original clause indices. Leaves use recorded binder paths, including whole-subtree binders. Split witnesses are fresh against the proof context and pattern variables, and empty splits use the datatype's elimination theorem. The independent proof matrix and split-selection logic are removed.

The new whole-subtree regression also exposed a disjointness bug: clauses guarding different fields were compared by guard-list index. Guards are now aligned by their argument position before looking for different constructors.

1. Replace the independent `RowP`/`ColP`, `switchIdx`, and matrix-specialization logic in [PatternProofs.scala](semantics/PatternProofs.scala) with recursion over the retained `Split` and `Leaf` nodes.
2. At each split, instantiate the recorded datatype's elimination theorem, introduce fresh typed field witnesses, and extend the local occurrence-to-expression environment and path equalities.
3. At each leaf, use the recorded binder assignments and the derived branch view to prove the selected clause's existing coverage disjunct. Supply outer synthetic binders and inner witnesses in their established order.
4. Prove whole-domain coverage from the root. Prove `branchSelectionFor` using the subtree of the known outer constructor, starting with its arguments and input equality already available. Do not compile a second matrix for branch selection.
5. Keep zero-constructor elimination explicit and keep all intermediate facts within their current proof scopes. Use Lisa's frontend tactics; the generated proofs remain kernel checked.

Completion check: coverage and branch-selection statements retain their current shape, with equality guards and existential typing assumptions intact. The proof generator contains no choice of split column or reconstruction of clause rows. The recursion witness construction continues to consume these theorems unchanged.

### 4. Unify branch semantics and migrate consumers

Implemented with one body-independent `Pattern`, `Clause[A]` for the attached payload, and `PatternSystem[A]` for the compiled collection. Induction retains its proof payload directly; function bodies are instantiated through `PatternSystem.map`, which shares the same patterns, decision tree, and theorem caches. The constructor/nested adapters, their downcasts, and the separate induction-branch representation are removed. Proof helpers now live in [PatternProofs.scala](semantics/PatternProofs.scala).

Nested recursive binders carry field paths derived only through `SelfRef` fields. Height descent follows these paths; specializing a payload to an ADT does not turn it into a recursive argument. Freshening uses payload/context expressions during construction without retaining those expressions in the body-independent pattern.

1. Replace `ConstructorPattern`, `NestedConstructorPattern`, and their two pattern systems with one branch implementation and one compiled collection. Keep the existing `Pattern`-facing methods as derived operations while migrating consumers.
2. Move constructor typing, injectivity, incompatibility, and case matching onto the resolved tree. Use constructor injectivity along common paths and disjointness at a differing constructor. These operations need no separate pattern AST or decision-tree compilation.
3. Update [CaseAccumulator.scala](syntax/CaseAccumulator.scala) and [Induction.scala](../induction/Induction.scala) to attach proof payloads to resolved branches directly. Remove dummy `∅` bodies, rediscovery of interface constructors, and duplicate coverage checks.
4. Replace recursive guard reparsing with traversal of recorded field paths. Update [PointwiseAgreementStep.scala](../recursion/helpers/PointwiseAgreementStep.scala), which serves stabilization and uniqueness, and preserve the immediate/inner binder distinction used by [Witness.targetInhabited](../recursion/Witness.scala).
5. Update function specifications, graph-witness proofs, and the public function wrapper to consume the unified clauses. Keep body-independent coverage/selection data shared when substituting the recursive self-reference into bodies.
6. Remove temporary adapters, `ConstructorHeadPattern` downcasts, the plain/nested dispatch in the accumulator, and unused guard representations. Fold the surviving proof routines into a common `semantics/PatternProofs.scala` or an equivalently small arrangement.

Completion check: all functions and induction cases use one pattern implementation. No independently stored pattern terms or guards are reparsed to recover structure. Preserve the public DSL and theorem contracts; introduce no new distinction between ordinary and recursive functions.

## Validation and completion

Use the existing [ADTRegressionSuite.scala](../../../../../../../../test/scala/lisa/maths/SetTheory/Types/ADTRegressionSuite.scala), currently 68 tests, the six compiler/contract tests in [DecisionTreeSuite.scala](../../../../../../../../test/scala/lisa/maths/SetTheory/Types/ADT/PatternMatching/DecisionTreeSuite.scala), and the existing ADT examples. Preserve coverage of specialization, independent function parameters, opaque/function payloads, nested recursion, ambient induction assumptions, invalid declarations, and binder-renamed equation lookup.

Step 2's tests cover empty splits, source clause indices and binder order, whole-subtree binder paths, nested specialization, missing cases, overlap in both declaration orders, and distinct datatypes with matching short constructor names. Compilation is also checked to leave definition and ADT registration unchanged.

Validated after step 2: all 4 compiler tests, all 63 ADT regression tests, all 16 examples, and both proof initializers executed successfully. `git diff --check` passed.

Step 3 adds computation and induction regressions for whole-subtree bindings, reordered cases, and ambient variables named like the old proof placeholders. All 4 compiler tests, all 65 ADT regressions, all 16 examples, and both proof initializers executed successfully; `git diff --check` passed.

Step 4 adds tests for shared pattern/tree/theorem identities after payload mapping, recursive field-path filtering, two nested recursive binders, and absence of induction hypotheses for specialized payloads. All 6 compiler/contract tests, all 67 ADT regressions, all 16 examples, and both proof initializers executed successfully; `git diff --check` passed.

Focused regressions cover the following boundaries:

- Nested cases split two different fields of one constructor; execute computations and induction assembly.
- Several nested recursive binders exercise height descent, existence, and uniqueness.
- A payload specialized to an ADT type receives no recursive hypothesis solely because of that type. Check the branch assumptions as well as successful nonrecursive use.
- User or ambient variables named like `scrutX`, `fv0`, `bsf0`, and generated constructor arguments do not get captured.
- Constructor identities remain distinct across datatypes with matching short constructor names; rigid type arguments survive binder-renamed lookup.
- Clause reordering preserves the intended equation lookup and payload association. Mapping bodies preserves the compiled pattern structure and coverage proof.
- Empty-ADT coverage succeeds through the common compiler; nested gaps and overlaps fail before definition registration. Existing invalid-induction tests still prove that the offending callback is never entered.

For each migration stage, execute the relevant regression proofs. Before considering the refactor complete, run these commands sequentially:

```text
sbt "lisa-sets/testOnly lisa.maths.SetTheory.Types.ADT.PatternMatching.DecisionTreeSuite"
sbt "lisa-sets/testOnly lisa.maths.SetTheory.Types.ADTRegressionSuite"
sbt "lisa-examples/runMain ADTExamples.RunAll"
```

Compilation alone is insufficient. The latter command executes all 16 examples and both proof initializers. Check generated theorems for admitted proofs as in the existing tests, and finish with `git diff --check`.

The implementation has one resolver, one decision-tree compiler, and proof routines consuming their output. The string pattern AST, `RPat`, duplicate parsers, the second splitting algorithm, and separate plain/nested implementations are removed. Theorem caches belong to the compiled collection and are shared when its payloads are mapped; proof facts remain scoped to their proofs.

## Follow-up: direct functionality and lazy disjointness

Constructor disjointness is cached on demand. Each unordered pair has one proof from the encoding; the reverse orientation follows by symmetry. The public ADT and semantic callers share these proofs, and only requested public theorem wrappers are registered.

[WitnessFunctionProofs.scala](proofs/WitnessFunctionProofs.scala) proves functionality directly over the existing clause graph. Two fresh witness tuples are reused under independent branch quantifiers, and small branch-decomposition facts are shared across comparisons. Identical instantiated bodies agree immediately. Otherwise, equal inputs from the same clause yield equal binders by pattern injectivity, then equal outputs by explicit simultaneous substitution, including lambda-valued outputs. Different clauses use cached pattern incompatibility. Both witness tuples are closed existentially, and the resulting pair statements are combined against the existing graph-membership disjunction.

Only unordered clause pairs generate agreement lemmas. Reverse pairs use output-swapped theorem instances without registering extra wrappers. The older conversion between named and canonical graph branches, separate body-equality theorem map, and nested existential proof scaffolding are removed. This remains quadratic in clause count; the decision tree continues to drive coverage and branch selection.

The expanded subtree-relation approach was removed after measurement: despite reducing emitted lemmas, transporting entire subtree formulas made the eight-clause example slower (1.99 s versus 1.09 s for the older direct proof, medians of three local samples). The implementation now has one graph-functionality proof, with no second relation or graph-to-tree bridge. A generic split-lemma prototype would need to demonstrate better construction time and kernel-proof size before replacing it.

Validated by executing 68 ADT regressions, 6 compiler/contract tests, 3 disjointness tests, all 16 examples, and both proof initializers. These include reordered eight-clause computations, lambda-valued bodies, whole-subtree binders, empty domains, and theorem-cache identity. The independent cross-constructor binder-capture failure recorded in `AGENTS_adt.md` was subsequently fixed.

### Direct-proof measurements, 2026-11-16

The simplified functionality implementation is 359 lines, compared with 685 in the old direct implementation; the extra subtree-relation and bridge files are removed. Canonical closed branch formulas are defined once by `Clause.caseMembership` and reused by graph construction and proof statements.

The following are medians of three warmed function-construction samples, using the same lazy disjointness cache and a 3 GB JVM heap in both implementations. Nested cases inspect all Boolean combinations; payload cases return an unconstrained pattern-bound value, so their same-clause proofs require injectivity and substitution. Wide cases use flat enumerations. Kernel steps sum the checked theorem certificates registered during construction, including nested subproof containers but excluding imported proofs already counted elsewhere. Temporary counters were removed after measurement.

| Function | Old time | Simplified time | Old kernel steps | Simplified kernel steps |
|---|---:|---:|---:|---:|
| Nested, 2 clauses | 0.094 s | 0.070 s | 3,873 | 3,646 |
| Nested, 4 clauses | 0.304 s | 0.281 s | 9,945 | 8,863 |
| Nested, 8 clauses | 0.940 s | 0.888 s | 27,121 | 22,710 |
| Nested, 16 clauses | 4.591 s | 4.625 s | 85,812 | 66,199 |
| Payload, 4 clauses | 0.331 s | 0.324 s | 10,647 | 11,332 |
| Payload, 8 clauses | 1.203 s | 1.076 s | 30,727 | 31,227 |
| Wide, 2 constructors | 0.112 s | 0.080 s | 3,829 | 3,714 |
| Wide, 4 constructors | 0.130 s | 0.106 s | 6,209 | 5,874 |
| Wide, 8 constructors | 0.215 s | 0.195 s | 12,135 | 10,958 |

These small samples show roughly preserved or improved runtime, not a universal speedup. Kernel-proof size decreases for constant-result cases but increases slightly for the payload cases. Pairwise comparison remains quadratic. The temporary harness is `target/ADTScalingBenchmark.scala`; raw results are in `target/adt-scaling-{matrix,selected}.log`.

### Follow-up: reuse theorem instances, 2026-11-16

Height adapters now instantiate shared theorems with `.of` inside the consuming proof. The three constructor height lemmas are cached generic schemas. Empty or identity substitutions return the original theorem; other substitution lists retain their simultaneous, last-assignment-wins semantics. Type-substitution validation is unchanged. The unused `UniqueCharacterizedSymbol` layer is removed; `UniqueDefinedSymbol.fromParts` retains the existence and uniqueness construction without generating the unused characterization theorem.

Executed 82 tests, all 16 examples, and both proof initializers. The five new `TheoremInstancesSuite` tests check identity reuse, substitution semantics, separate proof contexts, shared constructor schemas, and invalid substitutions. Repeated specialization registers no new theorems once the schemas exist.

The same warmed construction harness gives the following medians of three samples. The baseline is the preceding `selected` run, not an alternating before/after measurement. Counts include all kernel theorem registrations during each construction.

| Function | Previous theorems | Current theorems | Previous time | Current time |
|---|---:|---:|---:|---:|
| Nested, 2 clauses | 99 | 61 | 0.070 s | 0.100 s |
| Nested, 4 clauses | 139 | 111 | 0.281 s | 0.245 s |
| Nested, 8 clauses | 269 | 241 | 0.888 s | 0.907 s |
| Nested, 16 clauses | 673 | 645 | 4.625 s | 4.921 s |
| Payload, 4 clauses | 155 | 127 | 0.324 s | 0.341 s |
| Payload, 8 clauses | 329 | 301 | 1.076 s | 1.190 s |
| Wide, 2 constructors | 99 | 61 | 0.080 s | 0.074 s |
| Wide, 4 constructors | 161 | 103 | 0.106 s | 0.162 s |
| Wide, 8 constructors | 303 | 205 | 0.195 s | 0.192 s |

Registration counts decrease in every case; runtime does not consistently improve. Kernel steps also depend on where instantiations are performed: wide-eight decreases from 10,958 to 9,604, while payload-eight increases from 31,227 to 32,365. Raw results are in `target/adt-scaling-instances.log`. Temporary counters were removed, and the five instance tests were executed again with the restored kernel source.

### Follow-up: shared helpers and constructor lookup

`HeightStageSet` and `HeightTerms` share one finite-union implementation and one lazy subset schema. Component-inclusion proofs start at the requested component, preserve ambient assumptions, and reject absent components. Seven unused specialization helpers and their stale imports are removed. The old coverage and nullary-pattern machinery was already removed by the pattern refactor.

The ADT registry indexes constructor identifiers by owner and position. Pattern resolution uses this index and initializes only the requested owner's constructor wrappers, stored in a vector. Arity, specialization, and ownership checks remain unchanged. The new tests cover finite-union edge cases, theorem reuse, lookup misses, distinct constructor identities, and lazy initialization of unrelated wrappers.

Validated by executing all 86 tests, all 16 examples, and both proof initializers. `git diff --check` passed. Runtime effects were not benchmarked for this cleanup.

The follow-up freshness fixes share generated variables across each function declaration, keep canonical constructor tuples fresh against parameters and case bodies, and instantiate type and value substitutions simultaneously. Constructor predicates are capture-avoiding formula templates; induction also freshens its property binder and constructor witnesses against the ambient context. Pattern input typing reuses the constructor's application theorem.

Recursive body equality now abstracts the exact recursive-call occurrences and applies one simultaneous equality substitution through the whole body. This handles nested lambdas without separate cases for binder depth. `RobustnessSuite` adds 37 executed regressions covering the reported captures, specialized domains, nested recursion, and two or three nested lambdas. All 123 ADT tests, all 16 examples, and both proof initializers pass. `git diff --check` is clean.
