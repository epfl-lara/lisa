# SC-proof backport ledger

Base: upstream `a234fb842ef8ab875647b7c83099b9dd47a716ba`.
Source: `lcf-hol-ex` at `c8fc28f`, plus its accepted working-tree changes.
Status: selected ports implemented, committed, and validated; ready for donor
coverage/diff review. No automatic rebases or merge of the previous backport.

Run `bash bin/check-backport-boundary.sh` after every batch. Keep the SC proof
kernel, basic steps, and old tactic API. Translate proof recipes, never LCF
carriers. Preserve upstream tests, normalization fixes, and build configuration.

## Batches

| Donor | Scope | Result |
| --- | --- | --- |
| — | Architectural guard | Added; SC proof kernel and basic steps unchanged |
| `6aadc2f`, `7c61b25` | SC serialization and tests | Cherry-picked as `856ca31`, `d8c6157` |
| `7f41a5c`, `fbe1e93`, `df32fb0` | HOL extractor scaffold | Cherry-picked; retain upstream build and toolchain |
| `1341c60`, `81f2800` | Writer and sorted-set repairs | Cherry-picked as `dce92d4`, `28267fd` |
| `e51725d`, `6556eab` | Typing contexts | Cherry-picked as `780e809`, `e3569f1` |
| `697e77e`, `9a6619f` | Discharge and concrete universe proofs | Cherry-picked as `c4eb7aa`, `195c51b` |
| Cache identity repairs | Full names, expected statement, retained SC proof | Adapted as `192e70d`; no proof-recomputing accessors |
| `c775d7d` and accepted reader/parser worktree | Sparse traces, buffered reading, FastParse | Adapted as `ae82c02`; 17 reader/parser regressions |
| `1e5e236` old-API scaffold; later HOL proof recipes | HOL basics, propext, subset type definitions | Adapted as `602db9a`; no LCF frontend |
| `792e952`, `1a69311`, `ff679d1` and accepted hashing worktree | Capture avoidance, sort-sensitive equality, hashconsing, stored OL hashes | Adapted as `0c8fa7e`; preserve upstream normalization |
| `d8a49d6`, `c8fc28f` and accepted typing worktree | Recursive memo, equivalent types, explicit cuts | Adapted as `e317320`; retain the old inference API |
| Port validation | Binder shadowing and function-arrow capture | Fixed as `191f777`; 18 typing regressions pass |
| Port validation | Substitution under ambient assumptions | Fixed as `2ad04a2`; isolate internal restatements without changing the API |
| `fcd1dca` | Explicit discharge pivots and unchanged-cut elimination | Adapted as `97f04fd`; three checked SC regressions |
| `b726afa`, `4d00487`, `3355daa`, `fcd1dca` and accepted importer worktree | Paired type definitions, typed names, primitive proof recipes, shared steps | Adapted as `906826c` using independently checked SC proofs |

## Validation

- Pristine upstream: utils 25 passed; sets 482 passed, 42 canceled.
  Log: `/tmp/lisa-backport-baseline-full.log`.
- Serialization/cache batch: utils 100 passed before expression changes.
  Three cache regressions cover cold/warm reuse, colliding short names,
  stale statements, and rejection before wrong-name registration.
- Final suites in `/tmp/lisa-backport-validation-34.log`: utils 113 passed;
  sets 501 passed, 42 canceled; HOL/parser/extractor 30 passed (644 total).
  The upstream tests remain present; no new test exclusions were added.
- The sets run includes 18 typing regressions, one substitution-context
  regression, and all 58 original HOL tests. Typing covers negative contexts
  and types, repeated subterms, dependent covariance, and binder shadowing.
- The HOL run includes 13 regressions covering checked primitive proofs, type
  identities, annotation-sensitive caches, uncached local typing fallback,
  subset theorems, sparse shared steps, rejected statements, and debug gating.
  Checked fixture theorems also assert a false transitive `withSorry` flag.
- Expression/hash suite: all 10 tests passed independently under bounded,
  IDs-only, hybrid, and disabled hashing. Cached modes used an eight-entry cap
  to exercise rotations. Default capacity remains 1,048,576 per generation.
- Debug import: first 50 names passed, including 7,683 distinct trace steps and
  their exported statements (`/tmp/lisa-backport-validation-31.log`).
- Final debug import: first 200 names passed, including 57,721 distinct trace
  steps (`/tmp/lisa-backport-validation-34.log`, 177.536s). Intermediate exported
  statements were checked throughout. The complete validation command exited 0.
- Full-prefix import: 300 names and 101,189 distinct HOL trace steps passed with
  a 6 GB heap (`/tmp/lisa-backport-validation-34.log`). This crosses the historical
  failures at 110, 158, 174, 228/229, and the shadowing failure found at 300.
  The import reported 270.577s; this is validation, not a controlled comparison.
- `lisa.maths.SetTheory.Ordinals.TransfiniteRecursion` completed under
  the SC backend, including a later sbt run in `/tmp/lisa-backport-validation-33.log`.
  The earlier 28.80s wall time (`/tmp/lisa-backport-transfinite-current.log`)
  was measured during other work; it is not a comparative benchmark.
- Cold/warm full-library serialization parity remains pending. Do not infer
  binary compatibility with the LCF reader from round trips.

## Adaptation details

- Each shared imported step is an independently SC-checked theorem registered
  through the existing `THM.fromSCProof` API. Retain its actual derived sequent:
  weakening it to the exported HOL context can introduce non-emptiness premises
  which later rules cannot eliminate. Named theorems check their exported goals.
  No local proof index crosses proof owners. The old builder's required owner is
  one genuinely proved tautology, not an admitted theorem; it is never imported.
  Intermediate proof output is discarded, but the SC proof is checked and retained.
- Recursive typing memoizes only SC fragments whose external imports are
  reusable library justifications. Fragments depending on local facts are not
  cached. No path-dependent judgement casts or LCF carriers are introduced.
- HOL typing also registers the cleaned, actually inferred sequent through
  `THM.fromSCProof`. Canonical cache entries depend only on term annotations;
  retries with ambient assumptions are checked independently and never cached.
  Select typing assignments with the membership extractor, not an erased test
  against the opaque `TypeAssign` type. A regression checks a constructor whose
  typing is valid even for an empty type parameter.
- Scala 2 case-class constructors retain their original signatures. Explicit
  `copy` methods route through the expression factories, preventing copied
  expressions from bypassing identity allocation. Bounded/no-cache modes use
  stored structural hashes; hybrid/IDs modes use canonical IDs. Equality keeps
  its structural fallback. OL caches remain `Option`-based.
- Upstream beta/eta normalization, locally nameless OL forms, Scala versions,
  sbt version, automation API, and all pre-existing tests remain in place.
- Concrete port repairs: handle empty type-definition contexts without an
  empty hypothesis; instantiate `Exists.P`, not the unrelated `TypeDefs.p`;
  retain the witness before proving correctness; align covariance binders in
  the correct direction; replace brittle proof-search sites with explicit
  existential rules, substitutions, or cuts.
- Import validation exposed further old-API issues: clean non-emptiness after
  discharging polymorphic constructors; freshen typing binders against the
  context and domain; keep function-arrow codomains capture-free; isolate
  substitution's exact internal restatements from ambient weakening.
  Binder capture and the erased type test are candidates for a separate review
  on the LCF side; this task leaves the dirty source checkout unchanged.

## Remaining comparison limits

- Intermediate exported statements are checked only in debug mode; all SC proofs
  and all named statements are always checked. Stored proof size, import resolution,
  and theorem registration still differ from the LCF implementation.
- Upstream uses Scala 2.13.16 for the kernel and 3.8.4 for the frontend; the
  source comparison uses a different compiler and normalization implementation.
- The inferred-type monadic payload is not copied. The old inference API still
  extracts its single typing conclusion; the recursive proof-search reductions
  and memoization are ported independently of that API redesign.
- The standalone Horn tactic and temporary optimization/benchmark overlays are
  not part of these HOL/typechecking batches. They require a separate old-API port.

## Review the diff

Run from this checkout:

```sh
bash bin/check-backport-boundary.sh
git log --reverse --oneline a234fb8..HEAD
git diff --stat a234fb8..HEAD
git diff a234fb8..HEAD -- lisa-kernel/src/main/scala/lisa/kernel/fol
git diff a234fb8..HEAD -- lisa-utils/src/main/scala/lisa/utils/prooflib
git diff a234fb8..HEAD -- lisa-sets/src/main/scala/lisa/maths/SetTheory/Types
git diff a234fb8..HEAD -- lisa-sets/src/main/scala/lisa/hol lisa-hol
```

The only kernel edits are expression representation/hashconsing and stored OL
hashes in `fol/`. The entire `proof/` directory is byte-identical to the base.
Core frontend API files are unchanged; `WithTheorems` changes only cache identity
and retained proof handling. `SimpleDeducedSteps` changes only old-API Discharge.
Substitution changes only internal assumption isolation. No examples changed.
The small parser-demo `lisa-hol/.../Main.scala` was replaced by the bounded
import runner and parser tests; recover the old demo from `906826c^` if needed.

Reproduce checks (replace `PREFIX` with the export prefix):

```sh
sbt --client 'lisa-utils/testOnly *; lisa-sets/testOnly *; lisa-hol/testOnly *'
sbt --client 'set holImport / Compile / run / javaOptions := Seq("-Xmx6G"); lisa-hol/runMain lisa.hol.ImportBenchmark PREFIX 300'
sbt --client 'lisa-hol/runMain lisa.hol.importMain PREFIX --debug 50 false /tmp/unused false'
```

Each import command forks a fresh JVM. `ImportBenchmark` accepts an optional
zero-based start index for debugging later names while constructing their actual
dependencies. Normal imports still check every SC derivation and named goal;
debug mode additionally compares every ordinary intermediate exported statement.
Session heap settings do not change the build and can be cleared with `reload`.
The 4 GB full-prefix run was stopped after theorem 228 because its remaining
heap fell to tens of MB and progress deteriorated; do not use it as a timing
baseline. SC proof retention needs more heap than the LCF theorem store.

## Deferred decisions

- Complete full-library cold/warm cache checks and cross-reader binary checks
  before using these branches for a direct checker benchmark.
- Do not include experimental A/B/C/E caching proposals from the performance
  study in the accepted baseline.
- Do not import the proof-recomputing accessors of `c6567fa` without a separate
  lifecycle/cache review.
