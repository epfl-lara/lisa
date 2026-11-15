# Add ADTv2: algebraic data types, pattern matching, and recursion over set theory

## Summary

This PR adds **ADTv2**, a from-scratch reimplementation of LISA's algebraic-data-type support. It provides a declarative DSL for defining (polymorphic) ADTs, total and recursive functions defined by pattern matching, an induction tactic, and a small prebuilt datatype library — all encoded into LISA set theory with machine-checked injectivity, induction, existence and uniqueness theorems.

Everything is **`Sorry`-free** (no admitted proofs), covered by a 17-file worked-example suite.

## What's included

- **Declarative ADT DSL** — `adt(name, typeVars, constructors)` producing a typed `ADT[N]` with its constructors
- **Functions** — function `fun` on ADTs
- **Recursion** — recursive functions `recFun` are constructed as the limit of approximants over a transfinite "height" stage construction, with existence + uniqueness proved by well-founded induction.
- **Induction tactic** — structural induction over any declared ADT.
- **Pattern matching** — `Case` syntax, simple, nested, and multi-layer nested patterns. Used to define functions and prove theorems by induction.
- **Prebuilt library** — `Nat`, `List`, `Bool`, `Option`, `Product`, `Union`, `Box`, `Unit`, `Void`.

A datatype and a recursive function over it are declared directly in the DSL:

```scala
val nat = adt(
  name = "nat",
  constructors = Seq(
    ("zero", Seq.empty),
    ("succ", Seq(("k", SelfRef)))
  )
)
val zero = nat.constructors(0)
val succ = nat.constructors(1)

val pred = fun(nat, nat) {
  Case(zero):
    zero
  Case(succ, n):
    n
}
```

The builder discharges the injectivity, induction, existence, and uniqueness obligations, exposing them as ordinary LISA theorems (`nat.injectivity`, `nat.induction`, `pred.intro`, `pred.elim`, …).


## Project structure

The package is organized into 12 folders forming a clean layered architecture, from the surface syntax down to the set-theoretic encoding and back up to the user-facing API:

| Folder             | Role |
|--------------------|----------------------------|
| [syntax/](syntax/)          | Surface AST (`ConstructorArg`, `TypeArg`, `SelfRef`, `TypeExpr`). |
| [support/](support/)         | ADTv2-specific foundation: proof utilities, remaining lemmas, symbol-definition builders, dev tooling. |
| [encoding/](encoding/)        | Syntactic → semantic encoding of an ADT into set theory (carrier set, constructors, injectivity, induction). |
| [height/](height/)          | Transfinite "height" stage construction justifying recursion well-foundedness. |
| [PatternMatching/](PatternMatching/) | Pattern engine: `Case` syntax, `Pattern`/nested/trie semantics, induction translation, proofs. |
| [FunctionCore/](FunctionCore/)    | Shared semantic core unifying recursive and non-recursive functions. |
| [functions/](functions/)       | Non-recursive (total) function specialization on top of `FunctionCore`. |
| [recursion/](recursion/)       | Recursive-function semantics: approximants, limit construction, existence/uniqueness. |
| [interface/](interface/)       | Typed user wrappers: `ADT`, `Constructor`, `ADTFunction`, `RecFunction`. |
| [tactics/](tactics/)         | The `Induction` proof tactic. |
| [API/](API/)             | DSL entry points: `adt`, `fun`, `recFun`, builder overloads. |
| [library/](library/)         | Prebuilt datatypes (`Nat`, `List`, `Bool`, `Option`, …). |

The single public entry point is the `ADTv2` package object, which re-exports `adt`, `fun`, `recFun`, `Case`, `Pattern`, and `Induction`.


## Changes outside the ADTv2 folder

This PR is intentionally not confined to the new package:

- **General theory upstreamed into core LISA** (reusable beyond ADTs): `Ordinals/Integer.scala`, `Ordinals/OmegaFacts`, `Ordinals/TransfiniteRecursion`, `Functions/UnionRange.scala`, `Functions/Operations/Restriction.scala`, `Base/Union`, `Base/Subset`, plus additions to `Functions/BasicTheorems` and `Types/TypingTheorems`.
- **`lisa-utils`** gains a small `debug/Time` profiler and `prooflib` helpers (`QuantifierTactics`, `TacticErrors`, `Exports`).

## Testing

17 example files under `lisa-examples/ADTv2Examples` (builder / functions / proofs / end-to-end / overview) with a [RunAll.scala](../../../../../../../../../lisa-examples/src/main/scala/ADTv2Examples/RunAll.scala) driver, doubling as integration coverage.