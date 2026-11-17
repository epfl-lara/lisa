# ADTv2: algebraic data types over set theory

ADTv2 provides declarations of polymorphic algebraic data types, functions defined by pattern matching, and structural induction. Its encoding and generated proofs are checked by LISA's kernel without admitted proofs.

## Declaring a datatype and a function

Import the public DSL and declare pattern variables explicitly. This example defines natural numbers and a nonrecursive predecessor function:

```scala
import lisa.maths.SetTheory.Types.ADTv2.*

object Example extends lisa.Main {
  val nat = adt(
    name = "nat",
    constructors = Seq(
      ("zero", Seq.empty),
      ("succ", Seq(("k", SelfRef)))
    )
  )
  val zero = nat.constructors(0)
  val succ = nat.constructors(1)
  val previous = variable[Ind]

  val pred = fun(nat, nat) {
    Case(zero):
      zero
    Case(succ, previous):
      previous
  }
}
```

The generated theorems are available through the corresponding objects: `succ.injectivity`, `nat.induction`, `nat.elim`, `pred.intro`, and `pred.elim(succ)`. Distinct constructors have a disjointness theorem, obtained with `nat.disjointness(zero, succ)`.

`fun` and `recFun` share the same construction using height-indexed approximants. `recFun` additionally supplies a self-reference to the case-building function. Both support nested patterns; cases must be exhaustive and nonoverlapping. The [examples](../../../../../../../../../lisa-examples/src/main/scala/ADTv2Examples/) demonstrate recursion, specialization, computation, and induction.

## Parameters and declaration limits

`adt(name, "A", constructors)` declares one type parameter; overloads accept tuples of up to five names. The Scala parameter of `ADT[S]` is the LISA sort of the symbol: `ADT[Ind]` for a monomorphic datatype and `ADT[Ind >>: Ind]` for one type parameter. Use `adt.specialize(typeArgs*)` when defining a function on a particular specialization. Functions can also declare their own parameters, independently of the domain's parameters, through `fun(parameters)(specializedDomain, returnType)` and `recFun(parameters)(specializedDomain, returnType)`.

Constructor fields currently have one of two forms:

- `SelfRef` refers directly to the datatype being declared.
- `TypeArg("A")` refers to a declared type parameter. Import it from `lisa.maths.SetTheory.Types.ADTv2.syntax.AST` when using this explicit form.

A string naming the datatype is shorthand for `SelfRef`; a string naming a parameter is shorthand for `TypeArg`. Arbitrary type expressions and nested recursive occurrences are not supported in constructor declarations. Constructor declaration argument names `n`, `m`, and `h` are reserved by the encoding proofs. Constructor arguments and pattern binders must have distinct names within their respective declarations or cases.

## Package structure

| Folder | Role |
|---|---|
| [API/](API/) | `adt`, `fun`, and `recFun` builders. |
| [syntax/](syntax/) | Constructor field syntax: `ConstructorArg`, `TypeArg`, and `SelfRef`. |
| [interface/](interface/) | User-facing `ADT`, `Constructor`, and `ADTFunction` wrappers; `RecFunction` is an alias. |
| [encoding/](encoding/) | Set-theoretic carriers, constructors, injectivity, and induction. |
| [height/](height/) | Height stages and their well-foundedness proofs. |
| [PatternMatching/](PatternMatching/) | `Case`, validated patterns, decision trees, and shared branch proofs. |
| [recursion/](recursion/) | Function specifications, graph witnesses, approximants, existence, and uniqueness. |
| [induction/](induction/) | The `Induction` tactic. |
| [support/](support/) | Shared proof utilities and symbol-definition helpers. |
| [library/](library/) | Prebuilt natural numbers, lists, trees, Booleans, options, products, unions, boxes, unit, and void. |

The public package exports the DSL, `SelfRef`, `Case`, `Pattern`, `Clause`, and `Induction`. General iteration, ordinal, function, and set lemmas used by the encoding live in the corresponding set-theory library modules. Quantifier tactics live in `lisa-utils`.

## Testing

Run these commands from the repository root:

```text
sbt "lisa-utils/testOnly lisa.utils.prooflib.QuantifierTacticsSuite"
sbt "lisa-sets/testOnly lisa.maths.SetTheory.Types.ADTRegressionSuite lisa.maths.SetTheory.Types.ADTv2.* lisa.maths.SetTheory.Ordinals.IntegerSuite"
sbt "lisa-examples/runMain ADTv2Examples.RunAll"
```

The regression suites cover successful declarations and proofs, invalid inputs, specialization, nested patterns, binder freshness, theorem reuse, and lazy proof construction. [RunAll.scala](../../../../../../../../../lisa-examples/src/main/scala/ADTv2Examples/RunAll.scala) executes all worked examples and both shared proof initializers. Compilation alone does not execute these proof-generating objects.
