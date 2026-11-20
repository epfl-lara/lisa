# ADT: algebraic data types over set theory

ADT provides declarations of polymorphic algebraic data types, functions defined by pattern matching, and structural induction. Its encoding and generated proofs are checked by LISA's kernel without admitted proofs.

## Declaring a datatype and a function

Import the public DSL and declare pattern variables explicitly. This example defines natural numbers and a nonrecursive predecessor function:

```scala
import lisa.maths.SetTheory.Types.ADT.*
import lisa.maths.SetTheory.Types.ADT.InductiveInfixSyntax.{inductive, SelfRef, |}

object Example extends lisa.Main {
  val previous = variable[Ind]
  val Nat = inductive(
    | zero(),
    | succ(previous :: SelfRef)
  )
  import Nat.{zero, succ}

  val pred = fun(Nat, Nat) {
    Case(zero):
      zero
    Case(succ, previous):
      previous
  }
}
```

The generated theorems are available through the corresponding objects: `succ.injectivity`, `Nat.induction`, `Nat.elim`, `pred.intro`, and `pred.elim(succ)`. Distinct constructors have a disjointness theorem, obtained with `Nat.disjointness(zero, succ)`.

The complete datatype is built before `inductive` returns, so it can be used immediately. The explicit import distinguishes this `inductive` from the set-theoretic predicate with the same name.

`fun` and `recFun` share the same construction using height-indexed approximants. `recFun` additionally supplies a self-reference to the case-building function. Both support nested patterns; cases must be exhaustive and nonoverlapping. The self-contained [example](../../../../../../../../../lisa-examples/src/main/scala/ADTExample.scala) demonstrates declarations, specialization, nested patterns, polymorphic and higher-order recursion, typing, computation, and induction.

## Parameters and declaration syntax

Use existing LISA variables for type parameters and field binders:

```scala
import lisa.maths.SetTheory.Types.ADT.*
import lisa.maths.SetTheory.Types.ADT.InductiveInfixSyntax.{inductive, SelfRef, |}

val A, head, tail = variable[Ind]
val List = inductive(A)(
  | nil(),
  | cons(head :: A, tail :: SelfRef)
)
```

Use `()` for nullary constructors and commas between clauses. Every field must be a variable assignment, such as `head :: A`. `SelfRef` denotes the recursive type, implicitly applied to all declared parameters in order; it takes no arguments. Omit `(A)` for a monomorphic datatype, or use `inductive((A, B))(...)` for several parameters, up to five. `inductive()` defines an empty datatype. Supply clauses directly; declare variables and helpers outside the declaration.

The result is an actual `ADT[S]` and therefore an `Expr[S]`, with statically checked constructor names exposed through `Selectable`. Constructor selections use a cached map without Java reflection. Names that conflict with inherited ADT or expression members, such as `induction`, `elim`, or `id`, are rejected at compile time.

`List.cons(Nat) * Nat.zero * List.nil(Nat)` supplies a type argument followed by value arguments. Field types must be declared parameters or `SelfRef`. Arbitrary type expressions, nested recursive occurrences, and non-uniform recursion are unsupported. Constructor arguments and pattern binders must have distinct names within their respective declarations or cases; internal proof variables are chosen independently of their names.

## Explicit builder

The explicit `adt` builder remains available for programmatically assembled declarations:

`adt(name, "A", constructors)` declares one type parameter; overloads accept tuples of up to five names. The Scala parameter of `ADT[S]` is the LISA sort of the symbol: `ADT[Ind]` for a monomorphic datatype and `ADT[Ind >>: Ind]` for one type parameter. Use `adt.specialize(typeArgs*)` when defining a function on a particular specialization. Functions can also declare their own parameters, independently of the domain's parameters, through `fun(parameters)(specializedDomain, returnType)` and `recFun(parameters)(specializedDomain, returnType)`.

In the explicit builder, constructor fields have one of two forms:

- `SelfRef` refers directly to the datatype being declared.
- `TypeArg("A")` refers to a declared type parameter. Import it from `lisa.maths.SetTheory.Types.ADT.syntax.AST` when using this explicit form.

A string naming the datatype is shorthand for `SelfRef`; a string naming a parameter is shorthand for `TypeArg`. This builder uses the `SelfRef` marker from `syntax.AST`, also exported by `ADT`, rather than the expression placeholder imported from `InductiveInfixSyntax`.

## Package structure

| Folder | Role |
|---|---|
| [InductiveInfixSyntax.scala](InductiveInfixSyntax.scala) | Datatype declarations with typed fields and statically checked constructor names. |
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
sbt "lisa-sets/testOnly lisa.maths.SetTheory.Types.ADTRegressionSuite lisa.maths.SetTheory.Types.ADT.* lisa.maths.SetTheory.Ordinals.IntegerSuite"
sbt "lisa-sets/testOnly lisa.maths.SetTheory.Types.InductiveInfixSyntaxSuite"
sbt "lisa-examples/runMain ADTExamples.Example"
sbt "lisa-examples/testOnly ADTExampleSuite"
```

The regression suites cover successful declarations and proofs, invalid inputs, specialization, nested patterns, binder freshness, theorem reuse, and lazy proof construction. `ProofInitializationSuite` executes the shared height and recursion proofs. `ADTExampleSuite` runs the example and checks its recorded LCF errors and `Sorry` dependencies; compilation alone does not execute these proofs.
