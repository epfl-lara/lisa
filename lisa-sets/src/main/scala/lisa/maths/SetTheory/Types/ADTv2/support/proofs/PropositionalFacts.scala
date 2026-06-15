package lisa.maths.SetTheory.Types.ADTv2.support.proofs

import lisa.maths.Quantifiers.∃!
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._

/**
 * Generic propositional, equivalence and equality lemmas, split out of the
 * former `UsefulTheorems` grab-bag.
 */
object PropositionalFacts {

  val equivalenceApply = Lemma((p1 <=> p2, p1) |- p2){
    have(thesis) by Tautology
  }

  val equivalenceRevApply = Lemma((p2 <=> p1, p1) |- p2){
    have(thesis) by Tautology
  }

  val equivalenceToRevApply = Lemma(p1 <=> p2 |- p2 ==> p1){
    have(thesis) by Tautology
  }

  val equivalenceAnd =
    Lemma((p2, p1 <=> (p2 /\ p3)) |- p1 <=> p3)(have(thesis) by Tautology)

  val disjunctionsImplies = Lemma((p1 ==> p2, q1 ==> q2) |- (p1 \/ q1) ==> (p2 \/ q2)) {

    val right = have((p1 ==> p2, q1 ==> q2, p1) |- p2 \/ q2) by Restate
    val left = have((p1 ==> p2, q1 ==> q2, q1) |- p2 \/ q2) by Restate

    have((p1 ==> p2, q1 ==> q2, p1 \/ q1) |- p2 \/ q2) by LeftOr(left, right)
  }

  val existsOneUniqueness =
    Lemma((∃!(x, P(x)), P(x), P(y)) |- x === y) {
      have(∃!(x, P(x)) |- ∀(x, ∀(y, P(x) /\ P(y) ==> (x === y)))) by
        Restate.from(lisa.maths.Quantifiers.existsOneUniqueness)
      thenHave(∃!(x, P(x)) |- P(x) /\ P(y) ==> (x === y)) by
        InstantiateForall(x, y)
      have(thesis) by Tautology.from(lastStep)
    }

  val altEqualityTransitivity =
    Lemma((x === y, y === z) |- x === z)(have(thesis) by Congruence)

  val equivalenceRewriting =
    Lemma((p1 <=> p2, p2 <=> p3) |- (p1 <=> p3))(have(thesis) by Tautology)

  val impliesEquivalence = Lemma((p1 <=> p2, p3 <=> p4) |- (p1 ==> p3) <=> (p2 ==> p4)) {
    have(thesis) by Tautology
  }

  val leftImpliesEquivalenceWeak =
    Lemma(p1 <=> p2 |- (p ==> p1) <=> (p ==> p2))(have(thesis) by Tautology)

  val leftImpliesEquivalenceStrong =
    Lemma(p ==> (p1 <=> p2) |- (p ==> p1) <=> (p ==> p2))(have(thesis) by Tautology)

  val existsNeg = Lemma(∃(x, !P(x)) |- !forall(x, P(x)))(have(thesis) by Tautology)

}
