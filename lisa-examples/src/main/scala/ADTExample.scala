package ADTv2Examples

import lisa.maths.SetTheory.Functions.Pi.->:
import lisa.maths.SetTheory.Types.ADTv2.InductiveInfixSyntax.SelfRef
import lisa.maths.SetTheory.Types.ADTv2.InductiveInfixSyntax.inductive
import lisa.maths.SetTheory.Types.ADTv2.InductiveInfixSyntax.|
import lisa.maths.SetTheory.Types.ADTv2._
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.maths.SetTheory.Types.TypingHelpers

/**
 * Run with: sbt "lisa-examples/runMain ADTv2Examples.Example".
 */
object Example extends lisa.Main {

  val A, x, y, k, head, second, tail, xs, value = variable[Ind]

  // Declare field variables first. Empty parentheses introduce a nullary constructor.
  val Nat = inductive(
    | zero (),
    | succ (k :: SelfRef)
  )
  import Nat.{zero, succ}

  // Fields are declared parameters or SelfRef, which implicitly uses all parameters.
  // Arbitrary field types are unsupported. For several parameters, use inductive((A, B))(...).
  val List = inductive(A)(
    | nil (),
    | cons (head :: A, tail :: SelfRef)
  )
  import List.{nil, cons}

  // Parentheses supply type arguments; * applies set-theoretic functions to values.
  val singleton = cons(Nat) * zero * nil(Nat)
  val singletonTyping = Theorem(singleton :: List(Nat)) {
    have(thesis) by Typecheck.prove
  }

  // Generated constructor and carrier theorems can be used directly in ordinary proofs.
  val nilTyping = Theorem(nil(Nat) :: List(Nat)) {
    have(thesis) by Restate.from(nil.intro.of(Nat))
  }
  val natCases = Theorem(∀(x, x :: Nat ==> ((x === zero) \/ ∃(k, (k :: Nat) /\ (x === succ * k))))) {
    have(thesis) by Restate.from(Nat.elim)
  }
  val successorInjective = Theorem(∀(x, ∀(y, ((x :: Nat) /\ (y :: Nat)) ==> ((succ * x === succ * y) <=> (x === y))))) {
    have(thesis) by Restate.from(succ.injectivity)
  }
  val zeroNotSuccessor = Theorem(∀(k, k :: Nat ==> !(zero === succ * k))) {
    have(thesis) by Restate.from(Nat.disjointness(zero, succ))
  }

  // specialize fixes the domain's type arguments. This function has no remaining type parameters.
  // Cases must be exhaustive and nonoverlapping, with distinct binders in each case.
  val secondOrZero = fun(List.specialize(Nat), Nat) {
    Case(nil):
      zero
    Case(cons, head, nil(Nat)):
      zero
    Case(cons, head, cons(Nat) * second * tail):
      second
  }
  val secondOrZeroTyping = Theorem(secondOrZero :: (List(Nat) ->: Nat)) {
    have(thesis) by Restate.from(secondOrZero.intro)
  }

  // A generic domain supplies its type parameters to recFun. self is already specialized at A.
  // Recursive calls are on recursive subterms supplied by the patterns.
  val copy = recFun(List, List(A)) { self =>
    Case(nil):
      nil(A)
    Case(cons, head, tail):
      cons(A) * head * (self * tail)
  }

  // elim gives a defining equation. Type arguments use .of(type); free binders use .of(v := term).
  val copySingleton = Theorem(copy(Nat) * singleton === singleton) {
    val base = have(copy(Nat) * nil(Nat) === nil(Nat)) by Restate.from(copy.elim(nil).of(Nat))
    val step = have(copy(Nat) * singleton === cons(Nat) * zero * (copy(Nat) * nil(Nat))) by Tautology.from(
      copy.elim(cons).of(Nat).of(head := zero, tail := nil(Nat)),
      zero.intro,
      nil.intro.of(Nat)
    )
    have(thesis) by Congruence.from(base, step)
  }

  // Each induction case has field typings and recursive hypotheses; introduce them with assume.
  // Induction() can also infer the variable and datatype from the goal's typing assumption.
  val copyIdentity = Theorem(xs :: List(A) |- copy(A) * xs === xs) {
    have(thesis) by Induction(xs, List.specialize(A)) {
      Case(nil) subproof {
        have(thesis) by Restate.from(copy.elim(nil).of(A))
      }
      Case(cons, head, tail) subproof {
        assume(head :: A, tail :: List(A), copy(A) * tail === tail)
        val step = have(copy(A) * (cons(A) * head * tail) === cons(A) * head * (copy(A) * tail)) by
          Tautology.from(copy.elim(cons).of(A))
        have(thesis) by Congruence.from(step)
      }
    }
  }

  // Explicit function parameters need not come from the domain: repeat[A] : Nat -> A -> List[A].
  // TypingHelpers.fun builds a set-theoretic lambda, distinct from the ADT pattern-matching fun.
  val repeat = recFun(A)(Nat.specialize(), A ->: List(A)) { self =>
    Case(zero):
      TypingHelpers.fun(value :: A, nil(A))
    Case(succ, k):
      TypingHelpers.fun(value :: A, cons(A) * value * (self * k * value))
  }
  val repeatTyping = Theorem(repeat(Nat) * (succ * zero) * zero :: List(Nat)) {
    have(thesis) by Typecheck.prove
  }
}
