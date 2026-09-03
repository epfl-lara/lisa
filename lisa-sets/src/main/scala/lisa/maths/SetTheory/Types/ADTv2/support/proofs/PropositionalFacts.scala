package lisa.maths.SetTheory.Types.ADTv2.support.proofs

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._

/**
 * Generic propositional, equivalence and equality lemmas, split out of the
 * former `UsefulTheorems` grab-bag.
 */
object PropositionalFacts {

  val equivalenceApply = Lemma((p1 <=> p2, p1) |- p2) {
    have(thesis) by Tautology
  }

  val equivalenceRevApply = Lemma((p2 <=> p1, p1) |- p2) {
    have(thesis) by Tautology
  }

  val altEqualityTransitivity =
    Lemma((x === y, y === z) |- x === z)(have(thesis) by Congruence)

  val equivalenceRewriting =
    Lemma((p1 <=> p2, p2 <=> p3) |- (p1 <=> p3))(have(thesis) by Tautology)

  val leftImpliesEquivalenceWeak =
    Lemma(p1 <=> p2 |- (p ==> p1) <=> (p ==> p2))(have(thesis) by Tautology)

  val leftImpliesEquivalenceStrong =
    Lemma(p ==> (p1 <=> p2) |- (p ==> p1) <=> (p ==> p2))(have(thesis) by Tautology)

}
