# Phase 0 — Core datastructures & utilities

CORE: datastructures for terms, literals, clauses, substitutions, unification, KBO.
We follow Vampire and E closely, translated to the JVM.

## Status

Done:
- `Signature` — symbol interning + per-symbol KBO data (in [Core.scala](Core.scala)).
- `TermBank` — the flat hash-consed term arena, term/literal/clause construction and accessors (in [Core.scala](Core.scala)).
- `Trail` — non-eager unification with a backtrackable trail, two variable scopes, and an applier (in [Core.scala](Core.scala)).
- `KBO` — the Knuth-Bendix ordering on concrete terms (in [KBO.scala](KBO.scala)); see the KBO section below.

Still to do in Phase 0:
- A small term-builder DSL for the test mirror (KBO is currently tested by building terms directly
  through the bank, in `KBOTest.scala`).

Deferred to later phases (decided): duplicate-literal deletion, tautology deletion, canonical
literal ordering (Phase 1 simplification rules); term indexing and the unidirectional KBO fast
path (Phase 4); the entire Lisa translation/reconstruction boundary (Phase 1).

## Scope decision: standalone core

Phase 0 has **no dependency on Lisa** (`Expression`/`SCProof`). It is a self-contained engine,
to be tested via an internal term-builder DSL. The Lisa boundary (goal → clauses, proof
reconstruction) is Phase 1, where it is actually exercised. The arena design stays
translation-friendly: symbol interning and clause shape map cleanly onto Lisa `Constant`s and
literal sets.

## Representation decisions

The big choices (and why), settled while building `Core.scala`:

### Integer handles, not objects
A `Term` is an `Int`, not a heap object. On the JVM, an object-per-term graph means a ~16-byte
header per node and GC tracing of millions of long-lived shared terms — usually the dominant
cost in a saturating prover. Vampire/E use C structs + pointers because in C++ that *is* the
low-level efficient choice; the faithful translation of that intent to the JVM is an arena of
primitive arrays with integer handles. An `Int` handle *is* our pointer.

### Single flat `Array[Long]` arena, AoS records
All terms live back-to-back in one growable `mem: Array[Long]` (doubled on overflow); a `Term`
is the offset of its record. This is the array-of-structs layout Vampire's `Term` and E's
`TermCell` use (header fields followed by inline children), but with every term concatenated
into one array and offsets used in place of machine pointers. Chosen over struct-of-arrays
(parallel column arrays) because our hot paths — unification and KBO — read several fields of
*one* term at a time, which AoS keeps in one cache line; SoA would scatter them across columns.

Record layout for a term at offset `p` (`n == arity`):
```
mem(p + 0) = (functor & 0xFFFFFFFF) | (arity << 32)   // functor in low 32, arity in high 32
mem(p + 1) = free-variable mask
mem(p + 2) = total KBO weight (low 32 bits)
mem(p + 3 .. p + 2 + n) = the n child offsets (inline)
```
Packing functor+arity in one word lets `equalRecords` compare both with a single `Long` compare
before touching children. (Children are referenced by offset, never inlined by value — sharing
requires references, exactly as in Vampire/E.)

### Variables encoded in the functor field
A variable is `functor < 0` (variable number `v` encoded as `-(v+1)`); a symbol is `functor >= 0`.
No separate cell type (the E/LADR trick). Variables are shared/hash-consed like any term.

### Free-variable mask (63 bits + overflow)
Every term caches a `Long` mask: bit `v` set means variable `v` occurs, exact for `v in 0..62`,
OR-ed up from children. Bit 63 is an overflow marker ("some variable `>= 63` occurs"). A term is
**ground iff mask == 0**. `containsVar`/`firstVar` answer in O(1) from the mask; only the rare
`>= 63` case falls back to a traversal, and that traversal is *mask-pruned* (it skips any subtree
whose mask shows it can't contain the variable / is ground).

### Hash-consing: write-first interning + fastutil custom-strategy map
Structurally equal terms get the same offset, so term equality is `Int` equality. The interner
is a fastutil `Int2IntOpenCustomHashMap` (offset → canonical offset) with an `IntHash.Strategy`
whose `hashCode`/`equals` **read the record at an offset** — so no key object is ever
materialised (the key is the arena slice itself). A standard `Map` can't express "key stored
externally, compared by callback"; this is the same pattern as Vampire's `Set<Term*>` /
E's splay tree. A *map* (not a set) is used because we must retrieve the *canonical* stored
offset, which a `Set` API won't return.

Interning is **write-first**: `mkVar`/`mkApp` append the candidate record at the bump pointer,
then `get` hashes/compares it by offset like any stored entry; on a hit the bump pointer is
rewound (candidate discarded) and the stored offset returned, on a miss the offset is kept and
inserted mapping to itself.

### Hashing
`hashOf` uses `scala.util.hashing.MurmurHash3`'s incremental `mix`/`finalizeHash` (the
`productHash` protocol, `productSeed`), folding the identifying words straight out of the arena
with no allocation. Correctness requirement for the interner: `equalRecords(a,b) ⇒ hashOf(a) ==
hashOf(b)` — it holds because `hashOf` reads only the fields `equalRecords` constrains (header +
children). (A weaker hash would only cost probe time; an *inconsistent* one would let duplicates
in, breaking term identity — hence the care.)

### Signature
Symbols are interned to dense non-negative `Int` codes. Per-symbol data lives in one
`SymbolInfo` object (immutable `id`/`name`/`arity`/`isPredicate`; mutable `weight`/`precedence`
for KBO), held in a single `ArrayBuffer[SymbolInfo]` indexed by code, plus one `(name,arity) →
code` map. `Symbol` stays an `Int` (what terms store as their head); `info(f)` returns the record
(grab it once into a val when several fields are needed).

### Literals and clauses
- `Literal` is an opaque `Long`, packed `(atom << 1) | sign` (`Long` for headroom, since an atom
  is an arena offset). Predicates are interned exactly like functions; a literal is an atom term
  plus a polarity bit.
- `Clause` is an array of literals + cached weight + a fresh id. `mkClause` is a **dumb
  constructor** (as in E/Vampire): it takes ownership of the array and does *not* dedup, sort, or
  drop tautologies — those are normalisation/simplification steps for the Phase-1 loop. The empty
  array is the empty clause (falsity, `□`).

## Unification + trail (`Trail`)

Non-eager unification with dereferencing (no eager substitution). Bindings live in a separate
array indexed by variable, never mutating shared term records (E's in-cell binding is
incompatible with a shared arena). A single fixed, never-reallocated **trail** array records
bound variables; `save(): Int` / `restore(n: Int)` undo to a checkpoint. Two variable scopes
(query vs. partner clause), Vampire-style, keep two clauses' variables apart without renaming.
After a successful unify the trail drives an *applier* that instantiates a literal into a fresh
shared term (and later feeds proof reconstruction).

## KBO (not LPO) — `KBO`

The Löchner "Things to Know when Implementing KBO" tupling algorithm (a port of E's recursive
`kbo6cmp`/`kbo6cmplex`, "CTKBO4-6"): one simultaneous traversal accumulating the weight balance
`w(s)-w(t)` and the per-variable balance `#(x,s)-#(x,t)`, with incrementally-maintained counts of
variables that are net-positive / net-negative. Resolved by weight, then top-symbol precedence
(from `Signature`), then lexicographically on arguments, with the variable condition downgrading
any verdict to incomparable. Result `{Gt, Lt, Eq, Inc}`.

The lex descent stops recursing at the first differing argument (sweeping the rest into the
balances only), which keeps the comparison linear rather than quadratic. Three representation wins
are exploited without affecting the result: the **cached per-term weight** gives a ground/ground
fast path and a no-descent sweep of ground subterms; **hash-consing** makes term identity (and
hence equal-argument skipping) an O(1) pointer test. The accumulator state is reused and reset per
call, so a `KBO` instance is single-threaded. `checkAdmissibility()` validates the signature's
weights/precedence (positive variable weight; constants no lighter than a variable; a weight-0
unary symbol must be precedence-maximal).

Chosen **recursive** (over an explicit-stack iteration): with `Term` an `Int`, recursion needs no
boxed worklist and is the faithful rendering of the paper. Deep-term stack overflow is the same R1
caveat as `occurs`/`apply` (see [PossibleOptimizations.md](PossibleOptimizations.md)). Comparison
under a substitution without materialising it (E's `DerefType` / Vampire's `AppliedTerm`) and the
unidirectional "is-greater" fast path are deferred to a later phase.

## Build / environment notes

- Dependency: `it.unimi.dsi:fastutil-core` (added to the `lisa-sets` project in `build.sbt`) for
  the custom-strategy hash map.
- The build requires **JDK 17+** (the wider project uses `String.indent`); sbt 1.x is fine.

## Files
- [Core.scala](Core.scala) — `Signature`, `SymbolInfo`, `TermBank`, `Clause`, `Trail`, opaque `Term`/`Literal`.
- [KBO.scala](KBO.scala) — `Cmp` and the `KBO` comparator.
