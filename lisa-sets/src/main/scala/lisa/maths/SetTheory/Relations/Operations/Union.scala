package lisa.maths.SetTheory.Relations.Operations

import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Relations.Definitions.*

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
    sorry
  }

  /**
   * Theorem --- The domain of `⋃S` is the union of the domains of the
   * relation in `S`.
   */
  val unionRelationDomain = Theorem(
    relation(⋃(S)) |- dom(⋃(S)) === ⋃({ dom(R) | R ∈ S })
  ) {
    sorry
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
