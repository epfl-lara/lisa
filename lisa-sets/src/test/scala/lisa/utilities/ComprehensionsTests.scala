package lisa.utilities

import org.scalatest.funsuite.AnyFunSuite

class ComprehensionsTests extends AnyFunSuite {

  object ComprehensionsTests extends lisa.Main {
    import lisa.maths.settheory.SetTheory.*
    import lisa.maths.settheory.Comprehensions.*

    private val x = variable
    private val x_1 = variable
    private val y = variable
    private val z = variable
    private val s = variable
    private val t = variable
    private val A = variable
    private val B = variable
    private val C = variable
    private val P = predicate[2]
    private val Q = predicate[1]
    private val Filter = predicate[1]
    private val Map = function[1]
    private val f = function[1]

    val singletonMap = Lemma(
      ∃(x_1, in(x_1, singleton(∅)) /\ (x === f(x_1))) <=> (x === f(∅))
    ) {
      val s1 = have(∃(x_1, in(x_1, singleton(∅)) /\ (x === f(x_1))) ==> (x === f(∅))) subproof {
        have(x === f(∅) |- x === f(∅)) by Restate
        thenHave((x_1 === ∅, x === f(x_1)) |- x === f(∅)) by Substitution.ApplyRules(x_1 === ∅)
        thenHave((x_1 === ∅) /\ (x === f(x_1)) |- x === f(∅)) by Restate
        thenHave((in(x_1, singleton(∅))) /\ ((x === f(x_1))) |- x === f(∅)) by Substitution.ApplyRules(singletonHasNoExtraElements of (y := x_1, x := ∅))
        thenHave(∃(x_1, in(x_1, singleton(∅)) /\ ((x === f(x_1)))) |- x === f(∅)) by LeftExists

      }

      val s2 = have((x === f(∅)) ==> ∃(x_1, in(x_1, singleton(∅)) /\ (x === f(x_1)))) subproof {
        have(x === f(∅) |- (∅ === ∅) /\ (x === f(∅))) by Restate
        thenHave(x === f(∅) |- in(∅, singleton(∅)) /\ (x === f(∅))) by Substitution.ApplyRules(singletonHasNoExtraElements of (y := x_1, x := ∅))
        thenHave(x === f(∅) |- ∃(x_1, in(x_1, singleton(∅)) /\ (x === f(x_1)))) by RightExists
        thenHave(thesis) by Restate.from

      }

      have(thesis) by Tautology.from(s1, s2)
    }

    val testCollector = Theorem(
      ∃(s, ∀(x, in(x, s) <=> (x === f(∅))))
    ) {
      val r = singleton(∅).collect(lambda(x, top), f)

      have(in(x, r) <=> (x === f(∅))) by Substitution.ApplyRules(singletonMap)(r.elim(x))
      thenHave(∀(x, in(x, r) <=> (x === f(∅)))) by RightForall
      thenHave(thesis) by RightExists
    }

    val testMap = Theorem(
      ∃(s, ∀(x, in(x, s) <=> (x === f(∅))))
    ) {
      val r = singleton(∅).map(f)
      have(in(x, r) <=> (x === f(∅))) by Substitution.ApplyRules(singletonMap)(r.elim(x))
      thenHave(∀(x, in(x, r) <=> (x === f(∅)))) by RightForall
      thenHave(thesis) by RightExists
    }

    val testFilter = Theorem(
      ∃(x, Q(x)) |- ∃(z, ∀(t, in(t, z) <=> ∀(y, Q(y) ==> in(t, y))))
    ) {
      val s1 = assume(∃(x_1, Q(x_1)))
      val x = witness(s1)
      val z = x.filter(lambda(t, ∀(y, Q(y) ==> in(t, y))))
      have(∀(y, Q(y) ==> in(t, y)) <=> ((t ∈ x) /\ ∀(y, Q(y) ==> in(t, y)))) by Tableau
      have(in(t, z) <=> ∀(y, Q(y) ==> (t ∈ y))) by Substitution.ApplyRules(lastStep)(z.elim(t))
      thenHave(∀(t, in(t, z) <=> ∀(y, Q(y) ==> in(t, y)))) by RightForall
      thenHave(thesis) by RightExists

    }
  }
  assert(ComprehensionsTests.theory.getTheorem("testFilter").nonEmpty)

}
