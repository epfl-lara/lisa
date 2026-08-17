# Code review — `superposition/` (2026-08-16)

Scope: all 31 source files of `lisa-sets/src/main/scala/lisa/automation/superposition/` (~6,900 lines),
including `index/`, `ordering/` and `bench/`, plus [README.md](README.md). Cross-checked against
[archive/CodeReview.md](archive/CodeReview.md) and [archive/CodeReview2.md](archive/CodeReview2.md) so that
closed findings are not re-litigated; where a prior finding is still open it is marked as such.

Focus: code quality and conciseness — how easy the package is to read and maintain. Every recommendation is
neutral or favourable on performance; where a change could cost anything, that is stated.

No correctness findings.

**Reading this document.** Findings marked *done* keep the text they were written with, including its
`file:line` references, because the argument for a change is worth keeping next to the record of it. Those line
numbers describe the code as it stood when the finding was made, and the fixes have moved much of it — follow
the symbol name, not the number. Findings still open name their symbol instead, for the same reason.

---

## 0. Verdict

This is unusually good code. The layering is real (encoding → ordering → rules → simplification → loop →
reconstruction → adapters), the invariants that matter are written down where a reader hits them, and the
README is the best package document in the repository.

What holds it back from being *easy* to maintain is not the algorithms — those are clear — but roughly 600
lines of mechanical repetition spread thinly across every file, so that no single place looks bad enough to
fix. The three largest sources are parameter threading (§1.1), the `Option[Clause]` short-circuit idiom
(§1.2), and the scan/indexed twins (§1.6).

---

## 1. Repetition worth removing

### 1.1 `(bank, trail, order)` threaded through every signature — **partly done 2026-08-16**

*Status: the `order` parameter is gone (the "smaller version" below). The class-ification was **not** done, for
a reason found while doing it: `Superposition`'s pure-term helpers (`subtermAt`, `replaceAt`,
`foreachSubterm`, `fromSides`) are called from contexts that hold a **different** `Trail` (`Reconstruction`
builds its own) or no trail at all (`Core.Clause.fromSides` calls back into `Superposition`, so an instance
field would be a cycle). Class-ifying therefore splits each object into a static half and an instance half,
which is less uniform than the present all-static style, not more. The remaining `(bank, trail)` pair stays.*

[Inference](Inference.scala), [Superposition](Superposition.scala), [Demodulation](Demodulation.scala) and
[Subsumption](Subsumption.scala) are stateless objects whose every method — public and private — carries two
or three context parameters. The worst case is
[Demodulation.scala:172](Demodulation.scala#L172), with seven parameters of which three are context.

Two facts make this removable:

- `trail.bank` already *is* the bank ([Core.scala:555](Core.scala#L555) declares `val bank`), so `bank` and
  `trail` are never independent.
- `order` is **provably always** `bank.order`. `new Order(` occurs exactly once, at
  [Core.scala:194](Core.scala#L194), and all 10 test references go through `bank.order` via the fixture at
  `TermFixture.scala:26`. The parameter models a configurability that does not exist.

Turning these four objects into one-per-search classes (`new Inference(bank, trail)`,
`new Superposition(bank, trail, order)`, …), held as fields on `Discount` next to `simplifier` and `active`,
removes three parameters from about 25 signatures and from every call site. Field reads replace stack
arguments; the JIT treats these identically, and it removes the `lazy val order` access that currently
happens on some paths.

Smaller version of the same change: drop only `order`, and read `bank.order` into a local at each method's
top. One line per method, no structural risk.

### 1.2 The `Option[Clause]` short-circuit idiom — 33 occurrences — **done 2026-08-16**

*Status: implemented as written. `Discount` gained a `refutation` field and a `found` helper; `addPassive`,
`activate`, `addAll`, `scanGenerate`, `superposeUsing`, `superposeAtPositions`, `superposeIndexed`,
`superposeVerified`, `resolveIndexed` and `Simplifier`'s `backwardSubsume`, `backwardIndexed`,
`backwardScan`, `emitAll`, `backwardDemodulate`, `backwardDemodulateIndexed` all return `Boolean`. The three
`var refut: Option[Clause]` accumulators inside retrieval callbacks became `var stop: Boolean`. 19 of the 33
sites are gone; the 14 that remain are the unrelated "the rule did not fire" matches on `Inference.resolve` /
`canonicalize` / `subsumptionResolutionResolvent`, which are a genuine two-outcome result.*

```scala
addPassive(r) match
  case Some(empty) => return Some(empty)
  case None => ()
```

23 in [Discount.scala](Discount.scala), 8 in [Simplifier.scala](Simplifier.scala), 2 in
[Subsumption.scala](Subsumption.scala). At three lines each that is ~100 lines whose only content is
"propagate the refutation upward", and it buries the actual control flow of
[activate](Discount.scala#L148) under scaffolding.

The refutation is a once-per-run event, so it does not need to be in the return type of a hot function.
Store it:

```scala
private var refutation: Clause = null          // set the moment □ is derived
private def addPassive(c: Clause): Boolean     // true ⇒ □ found, `refutation` holds it
```

Every site becomes `if addPassive(r) then return true`. This also removes
[addAll](Discount.scala#L216) and [emitAll](Simplifier.scala#L285), which exist only to walk a collection
with this idiom, and it removes the `Some` allocation on the one path that has it. `Simplifier`'s
`emit: Clause => Option[Clause]` callback becomes `Clause => Boolean`, and the explanation at
[Simplifier.scala:33-37](Simplifier.scala#L33-L37) of why the callback exists stays exactly as true.

Estimated saving: 70–90 lines, and `activate` becomes readable top to bottom.

### 1.3 Derived flags computed in three places — **done 2026-08-16**

*Status: implemented as written, plus `indexedResolution` and `indexedSubsumption`, which were in the same
position. All seven are now `val`s in the [SearchOptions](SearchOptions.scala) body (`val`, not `def`: some
are read inside the generating loops, and a field read is what the private copies cost). `ActiveSet` lost its
six private copies and its public `indexedSubsumption`; `Simplifier` and `Discount` lost theirs. No call site
changed, since all three classes already do `import opts.*`.*

[ActiveSet.scala:29-34](ActiveSet.scala#L29-L34) and [Simplifier.scala:44-45](Simplifier.scala#L44-L45) both
compute `equality && backwardDemodulation` and `… && demodulationIndexing`;
[Discount.scala:39](Discount.scala#L39) computes the superposition twin. Three classes independently deriving
the same conjunction of the same options is exactly the setup where two of them drift.

These are derivations of `SearchOptions` and belong on it:

```scala
def forwardDemodulationOn: Boolean  = equality && forwardDemodulation
def indexedForwardDemod: Boolean    = forwardDemodulationOn && demodulationIndexing
def superpositionOn: Boolean        = equality && superposition
```

Every consumer already does `import opts.*`, so the call sites do not change at all. Removes ~10 lines and
one class of latent inconsistency.

### 1.4 Six spellings of "is this atom an equality" — **done 2026-08-16**

*Status: implemented as written. [Core.scala](Core.scala) gained `TermBank.isEqualityAtom` (on a `Term`),
`isEquality` (on a `Literal`) and `isNegativeEquality`, all `inline`. `Order.isEqualityAtom` and the top-level
`Selectors.isNegativeEquality` are deleted; the seven open-coded spellings in `ActiveSet`, `Bridge`,
`CascProver`, `Demodulation`, `Discount`, `Inference` and `Superposition` (two) now call them, as does
`Order.compareLit`. `Discount`'s private `isEquality` is gone.*

*Both guards that made the spellings look different are dropped, and the reason is now stated once on
`isEqualityAtom`: a variable's functor field is negative and `EqualitySymbol` is `0`, so `!isVar` is
unreachable as a distinguisher; and `=` is interned with arity 2 while `mkApp` requires the arity to agree, so
`arity == 2` is implied. The only remaining mentions of `EqualitySymbol` outside `Core` are two **constructor**
uses (`mkApp`/`applySymbol` building an equality), which are not this predicate.*

The canonical predicate is [Order.isEqualityAtom](ordering/Order.scala#L22). It is bypassed by inline
`bank.headSymbol(bank.atomOf(lit)) == EqualitySymbol` at [ActiveSet.scala:218](ActiveSet.scala#L218),
[Demodulation.scala:40](Demodulation.scala#L40), [Discount.scala:366](Discount.scala#L366),
[Inference.scala:55](Inference.scala#L55), [Superposition.scala:227](Superposition.scala#L227) and
[Bridge.scala:114](Bridge.scala#L114), plus a seventh variant with an extra arity check at
[Selectors.scala:62](ordering/Selectors.scala#L62).

The prior review raised this ("four spellings"); it is now six or seven. The reason it keeps regressing is
that the canonical one lives on `Order`, which most of these callers do not hold. Put it on `TermBank`
instead, where every caller already has one:

```scala
inline def isEqualityAtom(t: Term): Boolean = functor(t) == EqualitySymbol
inline def isEquality(l: Literal): Boolean  = isEqualityAtom(atomOf(l))
```

`inline` means these compile to the same instruction sequence the inline spellings produce today.
`Order.isEqualityAtom` then delegates. Cheapest fix in the review, and it makes the seventh
(arity-checking) variant's difference visible instead of hidden.

### 1.5 The applier replay order duplicated across files — **done 2026-08-16**

*Status: done, but in a different shape from the one proposed below, because the proposed one would have cost
time. The three generating rules interleave their `Applier` calls with the ordering gates — `superpose`
applies `l` and `r`, **then** gates on `lσ ⋠ rσ`, and only then applies the into-atom — so a shared prefix
function hoisting all three would instantiate the into-atom for every **rejected** overlap, on the hottest
path in the prover.*

*What landed instead: [Superposition.replayApplier](Superposition.scala),
[Superposition.replayFactoringApplier](Superposition.scala) and
[Demodulation.replayApplier](Demodulation.scala), each a verbatim statement of its rule's applier order,
living a few lines from the rule it mirrors, called by `Reconstruction`. The order is still written twice, but
the two copies are now **adjacent in one file** instead of split across two, so editing a rule's applier order
puts the thing that must match on the same screen — and `Reconstruction` no longer encodes knowledge of the
generating rules' internals. Zero runtime cost; the replay runs once per reconstructed step.*

*This stays a convention — the replay redoes what generation did, in the same order — and a per-step assertion
was considered and declined as more machinery than the rule is worth (2026-08-17). The prior review's "asserted
only where it is vacuous" was verified and was true: swapping the two survivor passes in `replayApplier` passed
all 392 tests. `EqualityReconstructionTest`'s "both parents contribute a surviving variable" now fails on it,
which is the coverage the convention rests on.*

Reconstruction must call `Applier.apply` in exactly the order the generating rule did, or the conclusion's
fresh variables are numbered differently and the rebuilt proof does not match. Today that order is written
twice, in two files, held together only by a comment:

| generating side | reconstruction replay |
|---|---|
| [Superposition.scala:100-125](Superposition.scala#L100-L125) | [Reconstruction.scala:150-157](Reconstruction.scala#L150-L157) |
| [Demodulation.scala:174-191](Demodulation.scala#L174-L191) | [Reconstruction.scala:165-170](Reconstruction.scala#L165-L170) |
| [Superposition.scala:196-205](Superposition.scala#L196-L205) | [Reconstruction.scala:242-244](Reconstruction.scala#L242-L244) |

Reordering two `ap.apply` calls in `superpose` is a natural-looking edit that silently breaks reconstruction,
and the prior review already noted that the tests which could observe this are all ground, so they would not
catch it.

The fixable part is the *prefix* — the applies that register variables before the surviving literals are
copied. Extract it once, on the generating side, and call it from both:

```scala
// in Superposition
private[superposition] def registerVars(ap: Trail#Applier, l: Term, r: Term, intoAtom: Term): Unit =
  ap.apply(l, 0); ap.apply(r, 0); ap.apply(intoAtom, 1)
```

The generating side continues into `copyLitsExcept`; the reconstruction side continues into
`replaySurvivors`. The ordering then has one definition. Zero runtime cost (same calls, same order).

### 1.6 The scan/indexed twins — ~250 lines maintained in lockstep — **done 2026-08-17**

*Status: the scan arms are deleted and retrieval is unconditionally indexed. Gone: `Discount.scanGenerate`,
`superposeUsing`, `superposeAtPositions`; `Simplifier.forwardScan`, `backwardScan`, the `useIndex` parameter of
`forwardSubsumptionResolveChar2`, and the scanning arm of `backwardDemodulate`; `Demodulation.backwardDemodulate`
(the wrapper that scanned a clause collection, whose only remaining caller was that arm);
`ActiveSet.activeDemodulators` with the list half of `removeDemodulatorsOf`, plus `clauses`, `apply` and
`removeAt`, which existed for the scans; and the three `SearchOptions` flags `fingerprintIndexing`,
`subsumptionIndexing`, `demodulationIndexing` with the five derived flags that selected on them. The `index|noindex`
CLI argument and its threading through `bench/FofHarness` went too.*

*Two things did **not** simply disappear, and are worth knowing:*

- *`Demodulation.normalForm`/`rewriteOnce` (scan a rule array) are **not** an A/B arm of
  `normalFormIndexed`/`rewriteOnceIndexed` (descend the tree): backward demodulation genuinely needs
  "normal-form this clause against exactly these rules", the rules of the one new unit equality. Both survive.
  What was duplication there — two identical fixpoint loops — is merged into `fixpoint`, as proposed below.*
- *`indexedSubsumption` did not become "always true": it decided whether `ActiveSet` **maintains** the
  feature-vector index, and it read `subsumptionIndexing && (forwardSubsumption || backwardSubsumption)`. Unit
  deletion and subsumption resolution query that index too, so a configuration with only `forwardUnitDeletion`
  on would have queried an index nobody built. The linear-scan arm masked it: with `indexedSubsumption` false,
  `forward` dispatched to the scan, which needed no index. It is now
  [SearchOptions.subsumptionEnabled](SearchOptions.scala), the disjunction of **all six** simplification flags.*

*The one indexed-vs-scan A/B the engine still has is real and stays: `forwardUnitDeletionIndexThreshold` picks
per call between scanning the (small) active-unit sublist and querying the `{¬K}` cones, and both paths are
live. Its test is unchanged.*

Five pairs, all shipping with the indexed arm on by default:

| scan | indexed | lines |
|---|---|---|
| [forwardScan](Simplifier.scala#L142) | [forwardIndexed](Simplifier.scala#L88) | ~55 |
| [backwardScan](Simplifier.scala#L260) | [backwardIndexed](Simplifier.scala#L212) | ~70 |
| [scanGenerate](Discount.scala#L229) + helpers | [resolveIndexed](Discount.scala#L348) + [superposeIndexed](Discount.scala#L303) | ~95 |
| [normalForm](Demodulation.scala#L80) | [normalFormIndexed](Demodulation.scala#L93) | ~20 |
| [rewriteOnce](Demodulation.scala#L123) | [rewriteOnceIndexed](Demodulation.scala#L143) | ~30 |

The justification given everywhere is A/B comparison, and that was clearly the right call while the indices
were being brought up. It is now a standing tax: every change to a simplification must be made twice and
argued equal, and the tests that check the equality are, per the prior review, too coarse to detect a
partially broken index.

Separate the two cases:

**Merge the ones that differ only in candidate enumeration.** `normalForm`/`normalFormIndexed` are the same
fixpoint loop over different `step` functions:

```scala
private def fixpoint(c: Clause)(step: Clause => Option[Clause]): Clause =
  var cur = c
  var next = step(cur)
  while next.isDefined do { cur = next.get; next = step(cur) }
  cur
```

One closure per `normalForm` call, not per rewrite step. Saves ~10 lines outright and both arms then provably
terminate the same way. `rewriteOnce`/`rewriteOnceIndexed` merge the same way, with the rule enumeration as
the parameter.

**Retire the ones that are whole parallel algorithms.** `scanGenerate` and the `forwardScan`/`backwardScan`
arms are not variants, they are second implementations. If the indexed paths have been the default long
enough to trust, deleting them removes ~180 lines and three flags (`fingerprintIndexing`,
`subsumptionIndexing`, `demodulationIndexing` become unconditional). If the A/B ability is worth keeping, the
honest form is a git tag or a branch, not a permanently maintained shadow implementation. This is a judgement
call; the point here is only that the cost is larger than it looks from any single file.

### 1.7 The lazy-null buffer and flip-literal idioms in `Simplifier` — **done 2026-08-17**

*Status: implemented as written. Six `var buf: ArrayBuffer = null` locals became six named `private val` fields
(`unitCands`, `srCands`, `bwVictims`, `bwCands`, `shrunk`, `demodCands`) plus a shared `seenIds`, each cleared at
the point of use. Zero `if buf == null then buf = …` remain. The three flipped-clause query shapes went through
one `foreachFlipped(c, singleton)` helper, which is also where the "a stored clause SR-resolves on `Lᵢ` exactly
when it subsumes `c` with `Lᵢ` flipped" characterisation is now stated once instead of in three long comments.*

*The reuse needs one argument, which is written down next to the fields: `emit` re-enters this class —
`Discount.addPassive` calls `condense`, and calls `forward` too when `forwardSimplifyAtGeneration` is on — so
the two buffers iterated **across** `emit` calls (`shrunk`, `demodCands`) must be untouched by any forward
path, and every other buffer must be finished with before the first `emit`. Both hold.*

Two idioms, six and three sites:

```scala
var cands: mutable.ArrayBuffer[Clause] = null
...
if cands == null then cands = mutable.ArrayBuffer.empty
cands += c
```

at [Simplifier.scala:108](Simplifier.scala#L108), [175](Simplifier.scala#L175), [214](Simplifier.scala#L214),
[230](Simplifier.scala#L230), [233](Simplifier.scala#L233), [263](Simplifier.scala#L263).

Replace each with a `private val` reusable buffer cleared on entry. Shorter (one `.clear()`, no null checks,
no `if cands != null then` wrapper around the consumer) *and* strictly faster — the buffer is never
reallocated. The one thing to check is nesting: `forwardIndexed` finishes with its buffer before calling
`forwardSubsumptionResolveChar2`, so two named fields (`unitCands`, `srCands`) suffice; note the constraint
in a comment next to the fields.

The second idiom — clone the literals, negate one, `mkQueryClause`, query the index — appears at
[111](Simplifier.scala#L111), [182](Simplifier.scala#L182) and [236](Simplifier.scala#L236) in three slightly
different spellings. One private helper `foreachFlipped(c)((query, i) => …)` covers all three and makes the
E-style "subsumes with literal *i* flipped" characterisation appear once instead of in three long comments.

### 1.8 `fromSides` returns a 4-tuple — **done 2026-08-17**

*Status: implemented, and renamed. `fromSides` named the mechanism (which of an equation's two sides the
superposition "from" index is keyed on) rather than the thing, so it is now
[Superposition.rewriteSources](Superposition.scala) / [Clause.rewriteSources](Core.scala), returning
`Array[RewriteSource]` where*

```scala
final class RewriteSource(val lit: Int, val side: Int, val lhs: Term, val head: Symbol)
```

*`lhs` deliberately matches [Demodulation.Rule](Demodulation.scala)'s `lhs`: a rewrite source and a demodulator
rule are the same idea at different strengths, unification against matching, and now read alike. The three call
sites lost their positional destructuring (`fs.head` → `src.lhs`, `src.lit`, `src.side`) and their
`while xs.nonEmpty … xs = xs.tail` walks became indexed loops over the array, matching the style everywhere
else. `Tuple4` boxed all four `Int`-shaped fields; the final class boxes none.*

[Superposition.fromSides](Superposition.scala#L219) returns `List[(Int, Int, Term, Symbol)]`, destructured at
three call sites ([Discount.scala:265](Discount.scala#L265), [Discount.scala:308](Discount.scala#L308),
[ActiveSet.scala:205](ActiveSet.scala#L205)), one of which discards the fourth component. The type appears
verbatim in four signatures.

A named class is better on both axes:

```scala
final class FromSide(val lit: Int, val side: Int, val lhs: Term, val head: Symbol)
```

Readability: `fs.head.lhs` instead of positional destructuring, and the signatures shrink to
`Array[FromSide]`. Efficiency: `Tuple4` is generic, so all four `Int`-shaped fields are boxed today; a final
class with `Int` fields boxes none. The list is cached per clause so this is not hot, but it is free.
Returning `Array[FromSide]` rather than `List` also lets the three `while xs.nonEmpty do … xs = xs.tail`
walks become indexed loops, matching the style everywhere else in the package.

### 1.9 The "which sides may this equation rewrite from" rule, written twice — **done 2026-08-17**

*Status: implemented as written. `Superposition.usesSide(ori, side)` is now the one statement of the rule, read
by `rewriteSources` and by `equalityFactoring`; `usableSides` and its per-call `List[Int]` are gone, and the
factoring loop iterates the two sides directly with `order.orient` still hoisted out of the partner loop as
before.*

[Superposition.scala:231-235](Superposition.scala#L231-L235) (inside `fromSides`) and
[Superposition.scala:244-249](Superposition.scala#L244-L249) (`usableSides`) encode the identical rule —
`Gt` ⇒ side 0, `Lt` ⇒ side 1, `Inc` ⇒ both, `Eq` ⇒ none — in two different shapes, one as a boolean and one
as an allocated `List[Int]`. Extract `private inline def usesSide(ori: Cmp, side: Int): Boolean` and have
both read it. Also removes the per-call `List` allocation in `equalityFactoring`.

---

## 2. Structure

### 2.1 `Discount` is still mostly generation — **done 2026-08-17**

*Status: implemented. [Generator.scala](Generator.scala) is new and holds `generate` plus `resolveGiven`,
`superposeGiven`, `superposeVerified`, `factorGiven`, `equalityInferences`, `emitAll` and `keptMaximal`.
`Discount` is **168 lines, from 377** at the start of the review, and what is left is the iteration, the two
clause sets, and the one decision about where a new clause goes.*

*`Generator` takes its `emit` sink at **construction** rather than per call, unlike `Simplifier`: every method
here needs it and there is exactly one caller, so threading it through six signatures would be noise. The
difference is noted in both headers.*

*Two things moved inward rather than across. `gcSelNonEq` was computed in `activate` and passed down, but
`resolveGiven` is its only consumer, so it is now local to it — one fewer parameter and one fewer line in the
part of the loop a reader is trying to follow. And the naming lost its now-meaningless distinction: with no scan
arms left, `resolveIndexed`/`superposeIndexed` said nothing, so they are `resolveGiven`/`superposeGiven`,
consistent with `factorGiven` and unambiguous against `Superposition.superpose`.*

[Discount.scala](Discount.scala) is 377 lines of which 226–377 (plus the factoring block inside `activate`)
are generating-inference machinery. Its own header describes a loop, and the loop is about 80 lines.

`Simplifier` is the model: it took the redundancy machinery out and left `Discount` saying
`simplifier.forward(gc)`. The same move for generation — a `Generator(bank, trail, active, opts)` exposing
`generate(gc, addPassive)` — would leave `Discount` at roughly 150 lines that read as the loop the README
describes. Combined with §1.2, `activate` becomes:

```scala
private def activate(gc: Clause): Boolean =
  if simplifier.backwardSubsume(gc)(addPassive) then return true
  if simplifier.backwardDemodulate(gc)(addPassive) then return true
  active.add(gc)
  generator.generate(gc)(addPassive)
```

### 2.2 `activate` currently does five things in one 67-line method — **done 2026-08-17**

*Status: done as part of §2.1. The factoring block became `Generator.factorGiven` and the equality block
`Generator.equalityInferences`, both named and documented in their own right, and `activate` is now five
statements: compute the selection, backward-subsume, backward-demodulate, `active.add`, `generator.generate`.
Its doc says why that order and no other. From 67 lines to 7.*

Even without the `Generator` extraction, the factoring block at
[Discount.scala:188-204](Discount.scala#L188-L204) is a self-contained 17-line nested loop that wants to be
`factorGiven(gc, gSel)`, and the equality block at [206-213](Discount.scala#L206-L213) wants to be
`equalityInferences(gc, gSel)`. Ten-minute edit, no risk.

### 2.3 `Core.scala` at 794 lines

The header's argument — opaque types must be transparent to their implementation — is correct and should not
be fought for `TermBank` or `Trail` (the latter genuinely needs `Array[Term]` transparency for its `-1`
sentinels). But `Justification` and `Clause` do not use that transparency at all: `Clause` only holds
`Array[Literal]` and reads `.length`. Moving them to `Clause.scala` (~120 lines, with the constructor going
from `private[Core]` to `private[superposition]`) leaves `Core.scala` as exactly the encoding, which is what
its header claims to be.

Related: `Core.compareStructural` and `compareLiterals` take `bank` as their first parameter but sit outside the
class. As [TermBank](Core.scala) methods they would read `bank.compareStructural(s, t)` at the call sites, which
is one fewer thing to thread. Same for `subtermAt` and `replaceAt` in [Superposition](Superposition.scala),
which are pure term operations sitting in the inference-rule file.

### 2.4 `CascProver` is a CLI plus two independent term printers

[CascProver.scala](CascProver.scala) holds argument parsing, SZS status mapping, cone computation, the
derivation printer (with its own nested `term`/`literal`/`clauseStr` over internal `Term`s) and `object Tptp`
(a second renderer over kernel `Expression`s). The two printers necessarily differ, but they share `functor`
and both need the same identifier-reassembly discipline, which is why the same warning appears twice
([CascProver.scala:234-237](CascProver.scala#L234-L237) and
[CascProver.scala:283-287](CascProver.scala#L283-L287)). Splitting the printing into `TptpOutput.scala` would
leave `CascProver` at ~120 lines of CLI, and give the shared naming rule one home.

Also: [parseCli](CascProver.scala#L31) calls `sys.exit(2)` from inside a parser. Returning an error and
exiting in `main` keeps the function testable.

### 2.5 File and object names — **done 2026-08-17**

*Status: all three, with `git mv` so the history follows the files.*

- *`SuperpositionTactic.scala` → [Superpose.scala](Superpose.scala), which is what the object in it is called.
  The test stays `SuperposeTacticTest`: it shares the `Superpose` stem, so a search still finds all of it, and
  "TacticTest" says what it covers. Three names for the entry point, down to two that agree.*
- *`Strategies.scala` → [Strategy.scala](Strategy.scala), matching the `case class`/`object` pair inside and
  removing the package's only plural filename.*
- *The `Clausal`/`Bridge` split now says which is which, from both sides: [Bridge](Bridge.scala) calls itself
  the **encoding** half of the kernel boundary and names `Clausal` as the other, and [Clausal](Clausal.scala)
  names `Bridge` as the half below it. The sentence a reader actually needs is which one to enter through — a
  first-order problem goes to `Clausal`, clause sequents to `Bridge` — and that is now written down. No rename:
  both names are defensible, and what was missing was that sentence, not better words.*

### 2.6 Two class-level docs for `Discount` — **done 2026-08-17**

*Status: the object's doc now describes what the object holds. `Result` gained the sentence that matters about
it — that the three cases are the only three outcomes a saturation has, and that `Bridge.Outcome` is the same
three at the kernel boundary — and the loop's description, including the `SearchOptions` note that had been
stranded on the class, is in one place on the class.*

[Discount.scala:8-16](Discount.scala#L8-L16) documents the loop on `object Discount`, and
[Discount.scala:28-32](Discount.scala#L28-L32) documents it again on `class Discount`. The object holds only
`Result` and `LoopStats`; its doc should describe those.

---

## 3. Specific small items

*The first four were applied on 2026-08-17; the rest are open.*

**~~`removeUnit` is unguarded, unlike its counterpart in `add`.~~ — done.** `add` appended to `units` only
`if c.size == 1` while `detach` called `removeUnit(c)` for every removed clause, scanning the whole list to
find nothing, which contradicted `detach`'s own claim that "every line below is guarded by the identical flag
as its counterpart". [ActiveSet.detach](ActiveSet.scala) now carries the same `c.size == 1` guard, so the
inverse relation holds by inspection, and `removeUnit`'s doc no longer advertises a non-unit call as ordinary.
(Near-relative of prior review §6.5, which was about the demodulator upkeep.)

**~~`if i < j then i else i - 1` has an unreachable branch.~~ — done, by asserting.** `gSel` is ascending —
every selector returns either a singleton or the maximal literals in clause order — and the pair loop starts at
`a + 1`, so `i < j` always and the `i - 1` branch was dead, hence untested. It is now
`assert(i < j, …)` followed by `keptMaximal(f, i)` in [Generator.factorGiven](Generator.scala), with the
derivation of the invariant written out. The dead branch was the thing that would have silently produced a
wrong index if a selector ever returned its indices in another order; the assertion turns that into a failure.

**~~Seven delegating counters.~~ — done.** `Discount` forwarded all seven `SimplificationStats` fields
individually for `DiscountTest`'s benefit, so an eighth counter needed an eighth accessor before anything could
read it. One `def stats: SimplificationStats = simplifier.stats` replaces them, and the 20 test assertions read
`d.stats.forwardSubsumed`.

**~~Hand-written `reset()`.~~ — done.** `SimplificationStats.reset` zeroed seven fields by hand: a list that
had to be kept in step with the fields, and silently wrong if it ever wasn't. It is deleted;
[Simplifier.reset](Simplifier.scala) replaces the record with a fresh instance instead, one allocation per
saturation, and `Discount.saturate` says `simplifier.reset()` alongside `passive.clear()` and
`active.reset(initial)`, which reads better than reaching through to `simplifier.stats.reset()` did.

*Also fixed in passing, since editing these files surfaced it: `bench/FofHarness.verifyOne` used
`getOrElse(return)`, a non-local return that Scala 3 no longer supports and warned about. It is now the
`if … then return` early-out the other entry points in that file already use, and the package compiles warning-free.*

*The entries below name their symbol rather than a line number. Nine applied items moved most of this code, and
line-pinned references to it went stale within a day — which is the same failure the prior review recorded as
"claims that are false as written", just aimed at the reader of this document.*

**~~`kbo` is a `def`, re-resolving a lazy val per literal.~~ — done, twice over.** It became a `val` alongside
§1.2, and §2.1 then moved it out of `Discount` entirely: it is `private val kbo` in
[Generator](Generator.scala), next to the `keptMaximal` that is its only reader. Nothing to do; the entry was
left standing here after the fix, which is why it could not be found in the code.

**~~Counting in comments.~~ — done in passing.** `ActiveSet`'s header said "seven structures", `Discount`'s
field comment "the demodulators and the five term/clause indices", and the README "up to seven derived
structures", while the class held ten. §1.6 deleted two of those structures and the rewritten comments name
them instead of counting: [ActiveSet](ActiveSet.scala) lists "five fingerprint indices, the demodulator tree,
the feature-vector index, and the unit sublist", `Discount` says "the demodulators and the indices", the README
"the derived structures".

**`Generator.resolveGiven`'s `nonEq` array may not pay for itself** — *the parameter half is done; the
measurement is open.* §2.1 moved it inward, so it is a local of its only consumer rather than a value threaded
through two signatures. What remains is the original question: it is an `Array[Boolean]` allocated per
activation to cache a predicate that is two array reads, over a `gSel.length` of 1–3. Worth measuring before
keeping. No performance claim without a benchmark.

**`Core.TermBank.buildClause`'s `pack(age, goal)` Long trick.** The design intent (one match, so age and
goal-ness cannot drift apart) is right, but the reader then has to decode `(packed >> 1).toInt` and
`(packed & 1L) != 0` in the constructor call. Two `var`s assigned inside the same match are equally
allocation-free and read directly.

**~~`Bridge.solve` documents its parameters as inline comments.~~ — done.** The eight `//` comments interleaved
in the parameter list are now `@param` entries on the scaladoc, as [SearchOptions](SearchOptions.scala) already
did it, so IDE hover shows them and the signature is eight lines instead of twenty. `sequents`, `maxGiven` and
`maxMillis` gained the one-line descriptions they never had.

**~~`Clausal.proveOutcome` nests 25 lines of proof composition inside a `case` arm.~~ — done.** Extracted as
`private def composeProof(base: K.SCProof, orig: IndexedSeq[K.Sequent]): K.SCProof` in
[Clausal](Clausal.scala), with a header saying what it does — present a proof over the working-form clauses as
one over the clausifier's originals, bridging the two with a `Restate` each. `proveOutcome`'s match is now two
lines. The `work0` intermediate went away with it: the slot map calls `toWorkingSequent` as it fills, rather
than mapping the whole clause list first.

**~~`Bridge.headAndArgs` builds with `as :+ arg`.~~ — done.** Now peels the spine into an accumulator: the
outermost application comes off first, so prepending each argument puts them back in source order with no copy,
O(n) instead of O(n²). Arities are small, but this runs over every term of every input clause.

---

## 4. Test-only surface in production files — **done 2026-08-17**

*Status: moved, not labelled. The six `Order` members and the two index conveniences are now
[Oracles.scala](../../../../../../test/scala/lisa/automation/superposition/Oracles.scala) in the test sources,
as extension methods, so the call sites read as they did (`order.compareClause(c1, c2)`,
`perm.vectorOf(bank, c)`) and only an `import Oracles.*` was added to three test files. `Fingerprint.compute`
became `Oracles.fingerprintOf`. Each moved definition uses **only public API** of what it tests, so nothing was
widened or weakened to let it out of the production file. `Order` is **169 lines, from 238**.*

*The two items §4 treats separately went the other way, both as recommended below:*

- *`KBO.checkAdmissibility` is now **asserted** once per problem in [Bridge.solve](Bridge.scala), right after
  `Precedence.assign`. That is the only point where it can be checked — the weight and precedence schemes are
  per-strategy and nothing downstream knows which ran — and it needs checking because an inadmissible ordering
  does not fail loudly, it loops inside demodulation or quietly costs completeness. It cost nothing to run:
  392 tests pass with it live, including ~40 real TPTP problems.*
- *`Fingerprint.unifiable` stays, because it is the specification, and [descendUnif](index/Fingerprint.scala)
  now says so: it enumerates exactly the stored features for which `unifiable(qf, sf)` holds, the two have to
  agree, and `FingerprintTest` cross-checks both against a brute-force enumeration. An omitted branch there is
  a silently dropped candidate that no verdict would report, which is why the relationship is worth stating at
  the implementation rather than only at the specification.*

---

The finding as originally written:

The prior review found this and it was resolved by *labelling* rather than moving. The labels are honest and
well written, but the code is still there:

- [Order.maximalSide](ordering/Order.scala#L63), [isStrictlyMaximal](ordering/Order.scala#L173),
  [compareClause](ordering/Order.scala#L193), [multisetCompare](ordering/Order.scala#L205),
  [termMultisetCompare](ordering/Order.scala#L233), [literalMultisetCompare](ordering/Order.scala#L237) —
  about 65 of `Order`'s 238 lines, none reachable from the engine. `literalMultisetCompare` exists only for
  `compareClause`, which exists only for `OrderTest`.
- [Permutation.vectorOf](index/FeatureVector.scala#L74), [Fingerprint.compute](index/Fingerprint.scala#L48) —
  same.

Moving these to an `OrderOracles` / `IndexOracles` object in the test sources keeps the tests' oracles and
leaves a reader of `Order.scala` seeing only what the calculus uses. If they are kept (there is a reasonable
argument that the generic definition belongs next to the specialised one it justifies), group them under one
`// --- test oracles ---` banner at the bottom rather than interleaved with live code as they are now.

Two deserve separate treatment:

**[KBO.checkAdmissibility](ordering/KBO.scala#L235)** is different in kind, and its own docstring says why:
weights and precedences are selectable per strategy, so admissibility is a property of a runtime
configuration, and nothing checks it at runtime. Currently it is in the worst position — a runtime check that
never runs. Either call it once from [Bridge.solve](Bridge.scala#L105) after `Precedence.assign` (one call
per search, negligible), or move it to tests and drop the claim. Calling it is the better option:
`assert(kbo.checkAdmissibility().isEmpty, …)` costs one signature walk per problem and closes a stated gap.

**[Fingerprint.unifiable](index/Fingerprint.scala#L59)** is the *specification* of the compatibility
relation, and [descendUnif](index/Fingerprint.scala#L260-L282) reimplements it as a branch structure without
calling it. The two must agree or the index silently drops candidates. The reimplementation is necessary (the
descent enumerates branches, it does not test pairs), but the relationship should be stated in `descendUnif`'s
doc — "this enumerates exactly the `sf` for which `unifiable(qf, sf)` holds; `FingerprintTest` cross-checks" —
rather than only in `unifiable`'s.

---

## 5. Comments

Roughly 30% of the package is comment lines (2,057 of 6,904), which for code of this density is defensible.
The quality is high and mostly explains *why*. Several headers are load-bearing and should not be touched:
the arena layout in [Core.scala:153-166](Core.scala#L153-L166), [matchTerm](Core.scala#L654-L661)'s contract,
the re-entrancy notes on all three indices, [ActiveSet](ActiveSet.scala#L10-L24)'s
removal-by-re-derivation argument, and the pipe-deadlock and locale notes in the harnesses.

The prior review's documentation pass clearly landed — only five "changelog-as-comment" instances survive,
down from ~10:

- [Clausal.scala:132-135](Clausal.scala#L132-L135) — two sentences about the `indexOf` this replaced and its
  complexity.
- [Discount.scala:107-109](Discount.scala#L107-L109) — "Gating here on a subset of the flags is what made
  `forwardSubsumptionResolution` dead when it was the only one asked for."
- [SearchOptions.scala:36-39](SearchOptions.scala#L36-L39) — "which is why it was originally off."
- [Fingerprint.scala:138](index/Fingerprint.scala#L138) — "Two other representations benchmarked the same."
- [FofHarness.scala:161](bench/FofHarness.scala#L161) — "(see the code review, §4.5)", a cross-reference into
  an archived document.

Of these the `SearchOptions` and `Fingerprint` ones are worth keeping — they answer "why not the obvious
alternative", which is the useful kind. The other three describe code that no longer exists, and the
`FofHarness` one points at a document the project marks historical.

One more class worth naming: comments that restate the line below, e.g.
[ActiveSet.scala:100](ActiveSet.scala#L100) (`slot.put(c.id, buffer.length) // record its slot before appending`).
There are not many, and they are harmless individually.

---

## 6. Suggested order of work

Ordered by (lines removed + risk reduced) ÷ risk. §1.1 (contained form), §1.2, §1.3, §1.4 and §1.5 (adapted
form) were applied on 2026-08-16; the rest are open.

1. ~~**§1.3** — derived flags onto `SearchOptions`.~~ done
2. ~~**§1.2** — the `Option[Clause]` → `Boolean` + field change.~~ done
3. ~~**§1.1** — kill the `order` parameter.~~ done (class-ification deliberately not; see §1.1)
4. ~~**§1.4** — `isEqualityAtom`/`isEquality` on `TermBank`.~~ done
5. ~~**§1.5** — state each rule's applier order beside the rule.~~ done (adapted; see §1.5)
6. ~~**§1.6** — delete the scan arms.~~ done
7. ~~**§1.7** — `Simplifier` buffers and the flipped-query helper.~~ done
8. ~~**§1.8** — `RewriteSource` instead of the 4-tuple.~~ done (renamed; see §1.8)
9. ~~**§1.9** — `usesSide` instead of the rule written twice.~~ done
10. ~~**§2.1 / §2.2** — extract `Generator`, split `activate`.~~ done
11. ~~**§2.5 / §2.6** — the naming and duplicated-doc items.~~ done
12. ~~**§3, first four** — `removeUnit` guard, `keptMaximal` assert, `stats` accessor, `reset` by
    reallocation.~~ done (`kbo` became a `val` alongside §1.2)
13. **§3, what is left** — unroll `pack`, and *measure* `resolveGiven`'s `nonEq` array. (Everything else in §3
    is now applied; `kbo` and the counting comments turned out to have been fixed in passing.)
14. ~~**§4** — move the oracles to tests; wire `checkAdmissibility` into `Bridge.solve`.~~ done. §1.5's residual
    assertion was **declined**: the applier order stays a convention, covered by one test rather than a check.
15. **§2.3 / §2.4** — the remaining file-boundary items: split `Clause` out of `Core`, split `CascProver`'s two
    printers out of its CLI.

### What the thirteen applied items actually changed

Counts first, since they are the point. The refutation-channel idiom is at **0 sites, from 33**; `order`
appears in **no** signature; **no** flag is derived twice; the equality test has **one** definition instead of
seven, and the rewrite-side rule **one** instead of two; each rule's applier order sits beside the rule instead
of in another file; every simplification and generating rule has **one** implementation instead of two;
`Simplifier` has **no** lazily-allocated null buffers, from six; and no signature carries an anonymous tuple.

`SearchOptions` is down to 17 knobs from 20, and the three that went were the ones whose value was always the
same and whose alternative was a second implementation of everything.

The file that was doing too much is the clearest measure: **`Discount` is 168 lines, from 377.** The loop now
reads as a loop, with `Generator` (174) and `Simplifier` (274) on either side of it — the two halves of the work
each named, each documented, each with one entry point.

Line totals, main sources: the package is **6,884** lines, from 6,904, with `Generator.scala` new. Per file,
`Discount` 377 → 168, `Simplifier` 338 → 274, `ActiveSet` 259 → 228, `Demodulation` 236 → 243,
`SearchOptions` 105 → 131, `Superposition` 249 → 314, `Core` 794 → 828, `Order` 238 → 238,
`Selectors` 164 → 157, `Bridge` 239 → 234. The files that grew grew in prose, not code: the derived `val`s and
their rationale, the three replay functions and why they are mirrored rather than shared, the paragraphs on
which `isEqualityAtom` guards are unreachable and on why the complete selector is now the bank's default, the
buffer-reuse argument, and `RewriteSource`'s and `usesSide`'s docs. The total barely moves because this was
never a volume problem: it was the same few ideas written several times each, and prose replacing repetition
costs about what the repetition did.

Behaviour: unchanged by construction for §1.1–§1.5 and §1.7 (control-flow-equivalent rewrites, code moved
without changing what it computes, and the §1.4 guards dropped are the ones shown above to be unreachable).
§1.6 removes configurations rather than changing any: every deleted arm was reachable only by setting a flag
away from its default, and the shipped defaults took the surviving path already. No clause is built in a
different order, so ids and the search trajectory are identical. All **392** tests across `superposition` and
`clausification` pass with `TPTP` set, nothing cancelled — 392 rather than 393 because two A/B tests merged
into one.

Allocation is neutral-or-better throughout: strictly fewer `Some` allocations; the same number of `bank.order`
reads; `kbo` promoted from `def` to `val`; the equality test is `inline`, so it compiles to what the
open-coded spellings did; and the reused buffers stop reallocating after the first given clause. Not
benchmarked — nothing here can cost time, and a sampled TPTP timing run is too noisy to prove a null result.

### What the A/B tests became

Deleting the scan arms cost six tests that compared them. Rather than dropping the clause sets with them, each
became a **pinned-verdict** table over the same inputs: `DiscountTest` now has "indexed resolution reaches the
expected verdict on each shape of resolution problem", "indexed simplification …", and one merged "general
subsumption resolution … in both directions"; `EqualitySaturationTest` has the superposition and demodulation
equivalents. Same clause sets, same coverage of the surviving path, and a sharper assertion: an A/B says two
paths agree, a pinned verdict says what the answer is.

Pinning them surfaced something the A/B had been hiding, which led to a further fix.

The set `{P(x) ∨ P(y), ¬P(a) ∨ ¬P(b)}` is unsatisfiable (take `x = y = a`) but **saturated**, and both A/B arms
had been saturating on it in agreement, so the test passed while showing nothing. The cause was not the
indexing: `TermBank.selector`'s field default was the *incomplete* `BestLiteralSelector`, which selects one
literal per clause, and factoring pairs two *selected* literals, so the factor `{P(y)}` the refutation needs
was never derived.

That field default is now the refutation-complete [CompleteBestLiteralSelector](Core.scala), matching what
`SearchOptions.selection` ships. It is resolved on first read, so a bank whose clauses are never activated
still builds no `Order`. Production behaviour cannot change: there are exactly two `new TermBank` sites, and
`Bridge.solve` assigns the selector from the options immediately, so the default was only ever what a caller
building a bank itself received — and what it received was a selection that silently could not reach some
proofs. With it fixed, that clause set refutes and the verdict is pinned as `refuted`; the redundant
`bank.selector = new CompleteBestLiteralSelector(...)` lines in `EqualitySaturationTest`'s and
`PrecedenceTest`'s fixtures are gone.

This also closes the prior review's finding that "four tests titled 'default selector' pin the wrong default":
all four still pass, and their titles are now accurate rather than describing the incomplete strategy. Tests
whose subject *is* a particular selector keep assigning it explicitly, so they go on testing what they claim
if the default ever moves again.
