import lisa.maths.SetTheory.Functions.Pi.->:
import lisa.maths.SetTheory.Types.ADT.library.cons
import lisa.maths.SetTheory.Types.ADT.library.list
import lisa.maths.SetTheory.Types.ADT.library.nil
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.maths.SetTheory.Types.TypingHelpers.{_, given}

/**
 * Run with `sbt "lisa-examples/runMain TypingExample"`.
 */
object TypingExample extends lisa.Main:
  val A, B, x, a, f = variable[Ind]
  val family = variable[Ind >>: Ind]

  // A typing judgement t :: A is the membership statement t ∈ A.
  val idA = fun(x :: A, x)
  val identityTyping = Theorem(idA :: (A ->: A)):
    have(thesis) by Typecheck.prove

  // Applying f to a substitutes a for x in the result type.
  val dependentApplication = Theorem((f :: Π(x :: A, family(x)), a :: A) |- ((f * a) :: family(a))):
    have(thesis) by Typecheck.prove

  // Subsumption: membership in A also gives membership in any superset B.
  val subsumption = Theorem((x :: A, A ⊆ B) |- (x :: B)):
    have(thesis) by Typecheck.prove

  // cons has signature [A] => A → list(A) → list(A). Parentheses supply A.
  val consTyping = Theorem(cons(A) :: (A ->: list(A) ->: list(A))):
    have(thesis) by Typecheck.prove

  // Each * supplies one value to the specialized constructor.
  val singleton = cons(A) * x * nil(A)
  val singletonTyping = Theorem((x :: A) |- (singleton :: list(A))):
    have(thesis) by Typecheck.prove
