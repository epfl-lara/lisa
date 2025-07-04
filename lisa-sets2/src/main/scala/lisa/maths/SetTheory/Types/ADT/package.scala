package lisa.maths.settheory.types

/*
/** Provides definitional mechanisms for Algebraic Data Types (ADTs) and tactics
  * for reasoning about them.
  *
  * ===Usage===
  *
  * In order to use ADTs, you need to import
  * {{{
  *   lisa.maths.settheory.types.adt.{*, given}
  * }}}
  *
  * ====Defining an ADT====
  *
  * ADTs can be defined using the following syntax:
  * {{{
  *   val define(adtName: ADT[N], constructors(c1, ..., cn)) = (X1, .., Xk) --> (T1, ..., Tn) | ... | (S1, ..., Sm)
  * }}}
  *
  * where:
  *  - `adtName` is the identifier of the ADT
  *  - `N` is the number of poylmorphic variables
  *  - `c1 ... cn` are the identifiers of the different constructors of the ADT,
  *  - `X1, ..., Xk` are the polymorphic variables
  *  - `T1, ..., Tn, S1, ..., Sm` are the types defining the signature of each constructor.
  * Note that `adtName` and `c1 ... cn` are scala identifiers, respectively
  * referring to the ADT and the constructors.
  * In addition, you cannot define two ADT with the same name, even in different
  * scopes, as they introduce a new global definition.
  * Type variables must be declarated as variables before being used.
  * Here are some examples of ADT definitions:
  * {{{
  *
  *   //variables declaration
  *   val A = variable
  *
  *   // Definition of booleans with two constructors tru and fals. Each of them take no argument so their signature is ()
  *   val define(bool: ADT, constructors(tru, fals)) = () | ()
  *
  *   // Definition of options with two constructors none and some. Options are polymorphic over a type variable A.
  *   // Their second constructor, some, has signature A has it takes only a value of type A.
  *   val define(option: ADT, constructors(none, some)) = A ->  () | A
  *
  *   // Recursive definition of lists with two constructors nil and cons. Lists are polymorphic over a type variable A.
  *   // The constructor cons takes two arguments of respectively type A and list(A) and append an element to
  *   // a sublist.
  *   val define(list: ADT, constructors(nil, cons)) = A -> () | (A, list)
  *
  *   //Definition of natural numbers.
  *   val define(nat: ADT, constructors(zero, succ)) = () | nat
  * }}}
  *
  * ====Using an ADT and its theorem====
  *
  * Each constructor of an ADT comes with an introduction rule and an injectivity theorem.
  * The introduction rule gives the type of the constructor and is of the form
  *
  *    `∀ X1, ..., Xk. c(X1, ..., Xk) :: T1 -> ... Tn -> ADT(X1, ..., Xk)`
  *
  * The injection theorem stipulates that two instances of the same constructor are equal if and only if all their arguments are equal.
  *
  * For examples for lists we have
  *
  *   nil introduction: `∀ A. nil(A) :: list(A)`
  *
  *   cons introduction: `∀ A. cons(A) :: A -> list(A) -> list(A)`
  *
  *   nil injectivity: `nil(A) = nil(A)`
  *
  *   cons injectivity: `cons(A) * x0 * x1 = cons(A) * y0 * y1 <=> x0 = x1 /\ y0 = y1`
  *
  * Each ADT comes with an structural induction schema, an elimination rule (or pattern matching principle) and an injectivity theorem.
  *
  * Structural induction states that if a statement is true for each constructor
  * assuming that the proposition is true for the constructor's arguments, then
  * it is true for every element of the ADT.
  *
  *  e.g. list induction: ` P(nil(A)) => (∀ x0 :: A. ∀ x1 :: list(A). P(x1) => P(cons * x0 * x1)) => ∀ x :: list(A). P(x)`
  *
  * Elimination rule is a direct consequence of induction and states that each
  * instance of an ADT is an instance of one of its constructors
  *
  *   e.g. list elimination: ` x :: list(A) => x = nil(A) \/ ∃ x0, x1. x = cons(A) * x0 * x1`
  *
  * Finally injectivity tells us that instances of different constructors are
  * different
  *
  *   e.g. nil/cons injectivity: `nil(A) != cons(A) * x0 * x1`
  *
  * ====Type Checking====
  *
  * We provide a tactic to automatically type check instances of algebraic data
  * types. It can be called using `TypeChecker.prove`. For examples instances of
  * lists can be typechecked as follow.
  *
  * {{{
  * have(nil(A) :: list(A)) by TypeChecker.prove
  * have((x :: A, l :: list(A)) |- cons * x * l :: list(A)) by TypeChecker.prove
  * }}}
  *
  * ====Induction Tactic====
  *
  * We provide a tactic for performing proofs by induction.
  * The tactic can prove goals of the form
  *
  * ` ∀ x :: adt. P(x)`
  *
  * To work the user needs to provide a proof of P(c * x0 * ... * xn) for each constructor.
  * The syntax of the tactic is of the following form:
  * {{{
  * have(∀ x :: adt. P(x)) by Induction(adt) {
  *   Case(c1, v1, ..., vn) {
  *      // proof of (v1 :: T1, ..., vn :: Tn, P(vi), ..., P(vj)) |- P(c1 * v0 * ... * vn)
  *   }
  *   ...
  *   Case(ck, v1, ..., vm) {
  *      // proof of (v1 :: S1, ..., vm :: Sm, P(vi), ..., P(vj)) |- P(ck * v0 * ... * vn)
  *   }
  * }
  * }}}
  *
  * For lists it would look like:
  *  {{{
  * have(∀ x :: list(A). P(x)) by Induction(list) {
  *   Case(nil) {
  *      // ...
  *      have(P(nil)) by //Tactic to conclude the subcase
  *   }
  *   Case(cons, x, l) {
  *      // ...
  *      have((x :: A, l :: list(A), P(l)) |- P(cons * x * l)) by //Tactic to conclude the subcase
  *   }
  * }
  * }}}
  *
  * ====Defining functions====
  *
  * Functions over ADT can also be defined via the following syntax:
  *
  * {{{
  * val myFunction = fun(adt, returnType) {
  *   Case(c1, v1, ..., vn) {
  *     body1
  *   }
  *   ...
  *   Case(ck, v1, ..., vm) {
  *     bodyk
  *   }
  * }
  * }}}
  *
  * The body of each case is automatically typechecked at runtime.
  * For example let's define the predecessor function over natural numbers
  *
  * {{{
  * val pred = fun(nat, nat) {
  *   Case(zero) {
  *     zero
  *   }
  *   Case(succ, n) {
  *     n
  *   }
  * }
  * }}}
  *
  * Recursive functions are not yet supported.
  *
  * ====Using functions====
  *
  * Functions come with an introduction and elimination rules.
  * Their introduction rule is of the form
  *
  * `∀ X1, ..., Xk. f(X1, ..., Xk) :: ADT(X1, ..., Xk) -> T`
  *
  * where `T` is the return type of the function
  *
  * On the other hand, we have an elimination rule for each constructor, giving the result of the function when applied to some
  * constructor
  *
  * ` f * (ck * v1 * ... * vn) = body(ck) `
  *
  * For example, for the `pred` function defined above the introduction rule would be
  *
  * `pred :: nat -> nat`
  *
  * and its elimination rules
  *
  * ` pred * zero = zero`
  *
  * ` pred * (succ * n) = n`
  *
  * Functions are also fully compatible with the typechecking tactic. We can for instance write:
  *
  * {{{
  * have(n :: nat |- pred * succ * n :: nat)
  * }}}
  */
package object adt {
  export ADTSyntax.{|, define, constructors, adt_to_term, fun_to_term, constructor_to_term, Case, fun, -->}
  export ADTSyntax.ADTBuilder.|
  export lisa.maths.SetTheory.Types.TypeSystem.*
}

 */
