package lisa.maths.SetTheory.Relations
package Operations

import lisa.maths.SetTheory.Base.Pair.given
import lisa.maths.SetTheory.Base.Predef._
import lisa.maths.SetTheory.Relations.Predef._

/**
 * Given a set `S` of relations, the union `⋃S` is a relation
 * on the union of the domains of the relations ∈ `S`.
 */
object Union extends lisa.Main {

  private val R = variable[Ind]
  private val S = variable[Ind]

  /**
   * Theorem --- If all `R ∈ S` are relations, then `⋃S` is relation.
   */
  val unionRelation = Theorem(
    ∀(R, R ∈ S ==> relation(R)) |- relation(⋃(S))
  ) {
    assume(∀(R, R ∈ S ==> relation(R)))

    // For z ∈ ⋃(S), there exists some R ∈ S with z ∈ R.
    // Since relation(R), by inversion z = (fst(z), snd(z)).
    // Then fst(z) ∈ dom(⋃(S)) and snd(z) ∈ range(⋃(S)).
    // So z ∈ dom(⋃(S)) × range(⋃(S)), proving relation(⋃(S)).

    have(∀(R, R ∈ S ==> relation(R))) by Restate
    val `R ∈ S ==> relation(R)` = thenHave(R ∈ S ==> relation(R)) by InstantiateForall(R)

    // z ∈ R, R ∈ S |- z = (fst(z), snd(z))
    have((z ∈ R, R ∈ S) |- z === (fst(z), snd(z))) by Tautology.from(
      `R ∈ S ==> relation(R)`,
      BasicTheorems.inversion of (R := R)
    )
    // ∃R. R ∈ S ∧ z ∈ R |- z = (fst(z), snd(z))
    thenHave(R ∈ S /\ (z ∈ R) |- z === (fst(z), snd(z))) by Restate
    thenHave(∃(R, R ∈ S /\ (z ∈ R)) |- z === (fst(z), snd(z))) by LeftExists
    // z ∈ ⋃(S) |- z = (fst(z), snd(z))
    val `z is a pair` = thenHave(z ∈ ⋃(S) |- z === (fst(z), snd(z))) by Tautology.fromLastStep(
      unionAxiom of (x := S)
    )

    // From z ∈ ⋃(S) and z = (fst(z), snd(z)):
    // fst(z) ∈ dom(⋃(S)) and snd(z) ∈ range(⋃(S))
    have(z ∈ ⋃(S) |- (fst(z), snd(z)) ∈ ⋃(S)) by Congruence.from(`z is a pair`)
    thenHave(z ∈ ⋃(S) |- fst(z) ∈ dom(⋃(S)) /\ snd(z) ∈ range(⋃(S))) by Tautology.fromLastStep(
      BasicTheorems.domainMembership of (x := fst(z), y := snd(z), R := ⋃(S)),
      BasicTheorems.rangeMembership of (x := fst(z), y := snd(z), R := ⋃(S))
    )
    thenHave(z ∈ ⋃(S) |- (fst(z), snd(z)) ∈ (dom(⋃(S)) × range(⋃(S)))) by Tautology.fromLastStep(
      CartesianProduct.pairMembership of (x := fst(z), y := snd(z), A := dom(⋃(S)), B := range(⋃(S)))
    )
    thenHave(z ∈ ⋃(S) |- z ∈ (dom(⋃(S)) × range(⋃(S)))) by Substitute(`z is a pair`)
    thenHave(z ∈ ⋃(S) ==> z ∈ (dom(⋃(S)) × range(⋃(S)))) by Restate
    thenHave(∀(z, z ∈ ⋃(S) ==> z ∈ (dom(⋃(S)) × range(⋃(S))))) by RightForall
    thenHave(⋃(S) ⊆ (dom(⋃(S)) × range(⋃(S)))) by Substitute(⊆.definition of (x := ⋃(S), y := (dom(⋃(S)) × range(⋃(S)))))
    thenHave(∃(Y, ⋃(S) ⊆ (dom(⋃(S)) × Y))) by RightExists
    thenHave(∃(X, ∃(Y, ⋃(S) ⊆ (X × Y)))) by RightExists
    thenHave(thesis) by Substitute(relation.definition of (R := ⋃(S)))
  }

  /**
   * Theorem --- The domain of `⋃S` is the union of the domains of the
   * relation in `S`.
   */
  val unionRelationDomain = Theorem(
    relation(⋃(S)) |- dom(⋃(S)) === ⋃({ dom(R) | R ∈ S })
  ) {
    assume(relation(⋃(S)))

    // Characterizations
    have(x ∈ { fst(z) | z ∈ ⋃(S) } <=> ∃(z ∈ ⋃(S), fst(z) === x)) by Replacement.apply
    val `x ∈ dom(⋃(S))` = thenHave(x ∈ dom(⋃(S)) <=> ∃(z ∈ ⋃(S), fst(z) === x)) by Substitute(dom.definition of (R := ⋃(S)))

    // ⊆ direction: x ∈ dom(⋃(S)) ==> x ∈ ⋃({ dom(R) | R ∈ S })
    val forward = have(x ∈ dom(⋃(S)) ==> x ∈ ⋃({ dom(R) | R ∈ S })) subproof {
      // x ∈ dom(⋃(S)) means ∃z ∈ ⋃(S). fst(z) = x
      // z ∈ ⋃(S) means ∃R ∈ S. z ∈ R
      // z ∈ R, fst(z) = x → x ∈ dom(R) (by domainMembership-like reasoning)
      // dom(R) ∈ { dom(R) | R ∈ S } since R ∈ S
      // So x ∈ dom(R) ∈ { dom(R) | R ∈ S } → x ∈ ⋃({ dom(R) | R ∈ S })

      // From z ∈ R: fst(z) ∈ { fst(w) | w ∈ R } = dom(R)
      have(z ∈ R |- fst(z) ∈ { fst(z) | z ∈ R }) by Tautology.from(
        Replacement.map of (x := z, A := R, F := fst)
      )
      val fstInDomR = thenHave(z ∈ R |- fst(z) ∈ dom(R)) by Substitute(dom.definition of (R := R))

      // From R ∈ S: dom(R) ∈ { dom(R) | R ∈ S }
      val domRinSet = have(R ∈ S |- dom(R) ∈ { dom(R) | R ∈ S }) by Tautology.from(
        Replacement.map of (x := R, A := S, F := λ(R, dom(R)))
      )

      // Combine: fst(z) ∈ dom(R) ∧ dom(R) ∈ { dom(R) | R ∈ S } → fst(z) ∈ ⋃({ dom(R) | R ∈ S })
      have((z ∈ R, R ∈ S) |- dom(R) ∈ { dom(R) | R ∈ S } /\ fst(z) ∈ dom(R)) by Tautology.from(
        fstInDomR,
        domRinSet
      )
      thenHave((z ∈ R, R ∈ S) |- ∃(y, y ∈ { dom(R) | R ∈ S } /\ fst(z) ∈ y)) by RightExists
      thenHave((z ∈ R, R ∈ S) |- fst(z) ∈ ⋃({ dom(R) | R ∈ S })) by Tautology.fromLastStep(
        unionAxiom of (x := { dom(R) | R ∈ S }, z := fst(z))
      )
      thenHave((z ∈ R, R ∈ S, fst(z) === x) |- x ∈ ⋃({ dom(R) | R ∈ S })) by Congruence
      thenHave((R ∈ S /\ (z ∈ R), fst(z) === x) |- x ∈ ⋃({ dom(R) | R ∈ S })) by Restate
      thenHave((∃(R, R ∈ S /\ (z ∈ R)), fst(z) === x) |- x ∈ ⋃({ dom(R) | R ∈ S })) by LeftExists
      thenHave((z ∈ ⋃(S), fst(z) === x) |- x ∈ ⋃({ dom(R) | R ∈ S })) by Tautology.fromLastStep(unionAxiom of (x := S))
      thenHave((z ∈ ⋃(S)) /\ (fst(z) === x) |- x ∈ ⋃({ dom(R) | R ∈ S })) by Restate
      thenHave(∃(z, (z ∈ ⋃(S)) /\ (fst(z) === x)) |- x ∈ ⋃({ dom(R) | R ∈ S })) by LeftExists
      thenHave(thesis) by Tautology.fromLastStep(`x ∈ dom(⋃(S))`)
    }

    // ⊇ direction: x ∈ ⋃({ dom(R) | R ∈ S }) ==> x ∈ dom(⋃(S))
    val backward = have(x ∈ ⋃({ dom(R) | R ∈ S }) ==> x ∈ dom(⋃(S))) subproof {

      // x ∈ dom(R) means ∃z ∈ R. fst(z) = x
      have(x ∈ { fst(z) | z ∈ R } <=> ∃(z ∈ R, fst(z) === x)) by Replacement.apply
      val `x ∈ dom(R)` = thenHave(x ∈ dom(R) <=> ∃(z ∈ R, fst(z) === x)) by Substitute(dom.definition of (R := R))

      // z ∈ R, R ∈ S → z ∈ ⋃(S) → fst(z) ∈ dom(⋃(S))
      have((z ∈ R, R ∈ S) |- R ∈ S /\ z ∈ R) by Restate
      thenHave((z ∈ R, R ∈ S) |- ∃(y, y ∈ S /\ z ∈ y)) by RightExists
      thenHave((z ∈ R, R ∈ S) |- z ∈ ⋃(S)) by Tautology.fromLastStep(unionAxiom of (x := S))
      thenHave((z ∈ R, R ∈ S) |- fst(z) ∈ { fst(z) | z ∈ ⋃(S) }) by Tautology.fromLastStep(
        Replacement.map of (x := z, A := ⋃(S), F := fst)
      )
      thenHave((z ∈ R, R ∈ S) |- fst(z) ∈ dom(⋃(S))) by Substitute(dom.definition of (R := ⋃(S)))
      thenHave((z ∈ R, R ∈ S, fst(z) === x) |- x ∈ dom(⋃(S))) by Congruence
      thenHave(((z ∈ R) /\ (fst(z) === x), R ∈ S) |- x ∈ dom(⋃(S))) by Restate
      thenHave((∃(z, (z ∈ R) /\ (fst(z) === x)), R ∈ S) |- x ∈ dom(⋃(S))) by LeftExists
      thenHave((x ∈ dom(R), R ∈ S) |- x ∈ dom(⋃(S))) by Tautology.fromLastStep(`x ∈ dom(R)`)

      // Now: x ∈ y, dom(R) = y, R ∈ S → x ∈ dom(R), R ∈ S → x ∈ dom(⋃(S))
      thenHave((dom(R) === y, x ∈ y, R ∈ S) |- x ∈ dom(⋃(S))) by Congruence
      thenHave(((R ∈ S) /\ (dom(R) === y), x ∈ y) |- x ∈ dom(⋃(S))) by Restate
      thenHave((∃(R, (R ∈ S) /\ (dom(R) === y)), x ∈ y) |- x ∈ dom(⋃(S))) by LeftExists
      val fromExists = lastStep

      // y ∈ { dom(R) | R ∈ S } <=> ∃R ∈ S. dom(R) = y
      have(y ∈ { dom(R) | R ∈ S } <=> ∃(R ∈ S, dom(R) === y)) by Replacement.apply
      val repMem = lastStep
      // So: y ∈ { dom(R) | R ∈ S } ∧ x ∈ y → x ∈ dom(⋃(S))
      have((y ∈ { dom(R) | R ∈ S }) /\ (x ∈ y) |- x ∈ dom(⋃(S))) by Tautology.from(fromExists, repMem)
      thenHave(∃(y, (y ∈ { dom(R) | R ∈ S }) /\ (x ∈ y)) |- x ∈ dom(⋃(S))) by LeftExists
      thenHave(thesis) by Tautology.fromLastStep(unionAxiom of (x := { dom(R) | R ∈ S }, z := x))
    }

    have(x ∈ dom(⋃(S)) <=> x ∈ ⋃({ dom(R) | R ∈ S })) by Tautology.from(forward, backward)
    thenHave(thesis) by Extensionality
  }

  /*
  /**
   * Theorem --- The union of a set of relations is a relation itself.
   *
   *    `∀ R ∈ x. relation(R, X) |- relation(⋃x, X)
   *
   */
  val unionOfRelations = Theorem(
    ∀(R, R ∈ x ==> relation(R)(X)) |- relation(⋃(x))(X)
  ) {
    assume(∀(R, R ∈ x ==> relation(R)(X)))
    val isRelation = thenHave(y ∈ x ==> relation(y)(X)) by InstantiateForall(y)

    have(z ∈ ⋃(x) |- ∃(y, (y ∈ x) /\ (z ∈ y))) by Tautology.from(unionAxiom)

    thenHave((y ∈ x) /\ (z ∈ y) |- relation(y)(X) /\ (z ∈ y)) by Tautology.fromLastStep(isRelation)
    // thenHave((y ∈ x) /\ (z ∈ y) |- relation(y)(X) /\ (z ∈ (X × X))) by Tautology.fromLastStep(isRelation)
    sorry
    /*
    // union of a set of relations contains only pairs
    have(forall(t, in(t, z) ==> relation(t)) |- forall(t, in(t, union(z)) ==> exists(a, exists(b, (t === pair(a, b)))))) subproof {
      assume(forall(t, in(t, z) ==> relation(t)))
      have(in(x, z) ==> relation(x)) by InstantiateForall
      have(in(x, z) |- forall(t, in(t, x) ==> exists(a, exists(b, (t === pair(a, b)))))) by Tautology.from(lastStep, setOfPairsIsRelation of z -> x)
      thenHave((in(x, z) /\ in(t, x)) |- exists(a, exists(b, (t === pair(a, b))))) by InstantiateForall(t)
      thenHave(exists(x, in(x, z) /\ in(t, x)) |- exists(a, exists(b, (t === pair(a, b))))) by LeftExists

      have(in(t, union(z)) ==> exists(a, exists(b, (t === pair(a, b))))) by Tautology.from(lastStep, unionAxiom of (x -> z, z -> t))
      thenHave(thesis) by RightForall
    }

    // a set of pairs is a relation
    have(thesis) by Tautology.from(lastStep, setOfPairsIsRelation of z -> union(z))
   */
  }

   */
}
