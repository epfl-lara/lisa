package lisa.maths.settheory

object SetTheory2 extends lisa.Main {
  import lisa.maths.settheory.SetTheory.*
  //import Comprehensions.*


  private val s = variable
  private val x = variable
  private val x_1 = variable
  private val y = variable
  private val z = variable
  private val f = function[1]
  private val t = variable
  private val A = variable
  private val B = variable
  private val C = variable
  private val P = predicate[2]
  private val Q = predicate[1]
  private val Filter = predicate[1]
  private val Map = function[1]

  val primReplacement = Theorem(
    ∀(x, in(x, A) ==> ∀(y, ∀(z, (P(x, y) /\ P(x, z)) ==> (y === z)))) |-
    ∃(B, forall(y, in(y, B) <=> ∃(x, in(x, A) /\ P(x, y))))
  ){
    have(thesis) by Restate.from(replacementSchema of (A := A, x := x, P := P))
  }



  val manyForall = Lemma (
    ∀(x, in(x, A) ==> ∀(y, ∀(z, (P(x, y) /\ P(x, z)) ==> (y === z)))).substitute(P := lambda((A, B), P(A, B) /\ ∀(C, P(A, C) ==> (B === C)) )) <=> top
  ) {
    have(thesis) by Tableau
  }

  val functionalIsFunctional = Lemma (
    ∀(x, in(x, A) ==> ∀(y, ∀(z, (P(x, y) /\ P(x, z)) ==> (y === z)))).substitute(P := lambda((A, B), Filter(A) /\ (B === Map(A)) )) <=> top
  ){

    have(y === Map(x) |- (y === Map(x))) by Restate
    thenHave((y === Map(x), z === Map(x)) |- y === z) by Substitution.ApplyRules(Map(x) === z)
    thenHave(in(x, A) |- ((Filter(x) /\ (y === Map(x)) /\ (z === Map(x))) ==> (y === z))) by Weakening
    thenHave(in(x, A) |- ∀(z, ((Filter(x) /\ (y === Map(x)) /\ (z === Map(x))) ==> (y === z)))) by RightForall
    thenHave(in(x, A) |- ∀(y, ∀(z, ((Filter(x) /\ (y === Map(x)) /\ (z === Map(x))) ==> (y === z))))) by RightForall
    thenHave(in(x, A) ==> ∀(y, ∀(z, ((Filter(x) /\ (y === Map(x)) /\ (z === Map(x))) ==> (y === z))))) by Restate
    thenHave(∀(x, in(x, A) ==> ∀(y, ∀(z, ((Filter(x) /\ (y === Map(x)) /\ (z === Map(x))) ==> (y === z)))))) by RightForall
    thenHave(thesis) by Restate

  }

  /**
    * Theorem --- the refined replacement axiom. Easier to use as a rule than primReplacement.
    */
  val replacement = Theorem(
    ∃(B, ∀(y, in(y, B) <=> ∃(x, in(x, A) /\ P(x, y) /\ ∀(z, P(x, z) ==> (z === y)))))
  ) {
    have(thesis) by Tautology.from(manyForall, primReplacement of (P := lambda((A, B), P(A, B) /\ ∀(C, P(A, C) ==> (B === C)) )))
  }

  val onePointRule = Theorem(
    ∃(x, (x===y) /\ Q(x)) <=> Q(y)
  ) {
    val s1 = have(∃(x, (x===y) /\ Q(x)) ==> Q(y)) subproof {
      assume(∃(x, (x===y) /\ Q(x)))
      val ex = witness(lastStep)
      val s1 = have(Q(ex)) by Tautology.from(ex.definition)
      val s2 = have(ex === y) by Tautology.from(ex.definition)
      have(Q(y)) by Substitution.ApplyRules(s2)(s1)
    }
    val s2 = have(Q(y) ==> ∃(x, (x===y) /\ Q(x))) subproof{
      assume(Q(y))
      thenHave((y === y) /\ Q(y)) by Restate
      thenHave(∃(x, (x===y) /\ Q(x))) by RightExists
      thenHave(thesis) by Restate.from
    }
    have(thesis) by Tautology.from(s1, s2)
  }


  /**
    * Theorem - `∃(x_1, in(x_1, singleton(∅)) /\ (x === f(x_1))) <=> (x === f(∅))`
    */
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

    val s2 = have( (x === f(∅)) ==> ∃(x_1, in(x_1, singleton(∅)) /\ (x === f(x_1)))) subproof {
      have(x === f(∅) |- (∅ === ∅) /\ (x === f(∅))) by Restate
      thenHave(x === f(∅) |- in(∅, singleton(∅)) /\ (x === f(∅))) by Substitution.ApplyRules(singletonHasNoExtraElements of (y := x_1, x := ∅))
      thenHave(x === f(∅) |- ∃(x_1, in(x_1, singleton(∅)) /\ (x === f(x_1)))) by RightExists
      thenHave(thesis) by Restate.from

    }

    have(thesis) by Tautology.from(s1, s2)
  }


}
