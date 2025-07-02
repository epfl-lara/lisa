package lisa.maths.SetTheory.Base

import Comprehension.|
import Union.∪
import Pair.{pair, given}

/**
  * The Cartesian product of two sets `A` and `B` is the set `A × B` containing
  * all pairs `(x, y)` of sets where `x ∈ A` and `y ∈ B`.
  */
object CartesianProduct extends lisa.Main {

  private val x, y, z = variable[Ind]
  private val a, b = variable[Ind]
  private val A, B = variable[Ind]

  /**
    * Cartesian Product --- Given two sets `A` and `B`, their Cartesian product
    * is the set containing pairs with the first element in `A` and the second
    * in `B`. The Cartesian product can be seen as a comprehension on the set
    * `𝒫(𝒫(A ∪ B))`.
    *
    *     `A × B = {z ∈ 𝒫(𝒫(A ∪ B)) | ∃ x ∈ A, y ∈ B. z = (x, y)}`
    *
    * @param x set
    * @param y set
    */
  val × = DEF(λ(A, λ(B, {z ∈ 𝒫(𝒫(A ∪ B)) | ∃(x, ∃(y, (x ∈ A) /\ (y ∈ B) /\ (z === (x, y))))}))).printInfix()
  val cartesianProduct = ×

  extension(x: set) {
    inline infix def ×(y: set): set = cartesianProduct(x)(y)
  }

  /**
    * Lemma --- If `x ∈ A` and `y ∈ B` then `(x, y) ∈ 𝒫(𝒫(A ∪ B))`.
    */
  val pairInPowerPower = Lemma(
    (x ∈ A, y ∈ B) |- (x, y) ∈ 𝒫(𝒫(A ∪ B))
  ) {
    assume(x ∈ A)
    assume(y ∈ B)

    sorry
  }


  /**
   * Theorem --- `(x, y) ∈ A × B` if both `x ∈ A` and `y ∈ A`.
   *
   *  `(x, y) ∈ A × B <=> x ∈ A /\ y ∈ B`
   */
  val pairMembership = Theorem(
    (x, y) ∈ (A × B) <=> x ∈ A /\ y ∈ B
  ) {
    val `==>` = have((x, y) ∈ (A × B) |- x ∈ A /\ y ∈ B) subproof {
      sorry
    }

    val `<==` = have((x ∈ A, y ∈ B) |- (x, y) ∈ (A × B)) subproof {
      assume(x ∈ A)
      assume(y ∈ B)

      have(x ∈ A /\ (y ∈ B) /\ ((x, y) === (x, y))) by Tautology
      thenHave(∃(y, x ∈ A /\ (y ∈ B) /\ ((x, y) === (x, y)))) by RightExists
      thenHave(∃(x, ∃(y, x ∈ A /\ (y ∈ B) /\ ((x, y) === (x, y))))) by RightExists
      sorry
    }

    sorry
  }

  /**
    * Theorem --- The product of any set with ∅ on the left is ∅.
    *
    *  `∅ × B = ∅`
    */
  val leftEmpty = Theorem(
    ∅ × B === ∅
  ) {
    sorry
  }

  /**
    * Theorem --- The product of any set with ∅ on the right is ∅.
    *
    *  `A × ∅ = ∅`
    */
  val rightEmpty = Theorem(
    A × ∅ === ∅
  ) {
    sorry
  }

  /**
    * Theorem --- If `t` is a pair containing elements from `x` and `y`, then
    * it is in `PP(x ∪ y)`.
    *
    *    `∃ c, d. t = (c, d) ∧ c ∈ x ∧ d ∈ y ⊢ t ∈ PP(x ∪ y)`
    *
    * Asserts that the first part of the [[cartesianProduct]] definition is redundant.
    */
  /*
  val elemOfPowerPowerUnion = Theorem(
    ∃(c, ∃(d, (t === pair(c, d)) /\ in(c, x) /\ in(d, y))) |- in(t, powerSet(powerSet(setUnion(x, y))))
  ) {
    val upCD = have((in(c, x), in(d, y)) |- in(unorderedPair(c, d), powerSet(setUnion(x, y)))) subproof {

      have((in(c, x), in(d, y)) |- subset(unorderedPair(c, d), setUnion(x, y))) subproof {
        val zcd = have(in(z, unorderedPair(c, d)) <=> ((z === c) \/ (z === d))) by Restate.from(pairAxiom of (x -> c, y -> d))
        val zunion = have(in(z, setUnion(x, y)) <=> (in(z, x) \/ in(z, y))) by Restate.from(setUnionMembership)

        val zc = have((z === c) |- in(z, setUnion(x, y)) <=> (in(c, x) \/ in(c, y))) by Substitution.ApplyRules(z === c)(zunion)
        val zd = have((z === d) |- in(z, setUnion(x, y)) <=> (in(d, x) \/ in(d, y))) by Substitution.ApplyRules(z === d)(zunion)

        have((in(c, x), in(d, y)) |- in(z, unorderedPair(c, d)) ==> in(z, setUnion(x, y))) by Tautology.from(zcd, zc, zd)
        thenHave((in(c, x), in(d, y)) |- forall(z, in(z, unorderedPair(c, d)) ==> in(z, setUnion(x, y)))) by RightForall

        have(thesis) by Tautology.from(lastStep, subsetAxiom of (x -> unorderedPair(c, d), y -> setUnion(x, y)))
      }

      have(thesis) by Tautology.from(lastStep, powerSetAxiom of (y -> setUnion(x, y), x -> unorderedPair(c, d)))
    }

    val upCC = have((in(c, x)) |- in(unorderedPair(c, c), powerSet(setUnion(x, y)))) subproof {

      have((in(c, x)) |- subset(unorderedPair(c, c), setUnion(x, y))) subproof {
        val zcd = have(in(z, unorderedPair(c, c)) <=> (z === c)) by Restate.from(pairAxiom of (x -> c, y -> c))
        val zunion = have(in(z, setUnion(x, y)) <=> (in(z, x) \/ in(z, y))) by Restate.from(setUnionMembership)

        val zc = have((z === c) |- in(z, setUnion(x, y)) <=> (in(c, x) \/ in(c, y))) by Substitution.ApplyRules(z === c)(zunion)

        have(in(c, x) |- in(z, unorderedPair(c, c)) ==> in(z, setUnion(x, y))) by Tautology.from(zcd, zc)
        thenHave(in(c, x) |- forall(z, in(z, unorderedPair(c, c)) ==> in(z, setUnion(x, y)))) by RightForall

        have(thesis) by Tautology.from(lastStep, subsetAxiom of (x -> unorderedPair(c, c), y -> setUnion(x, y)))
      }

      have(thesis) by Tautology.from(lastStep, powerSetAxiom of (y -> setUnion(x, y), x -> unorderedPair(c, c)))

    }

    have((in(c, x), in(d, y)) |- in(pair(c, d), powerSet(powerSet(setUnion(x, y))))) subproof {

      have((in(c, x), in(d, y)) |- subset(pair(c, d), powerSet(setUnion(x, y)))) subproof {
        val zp = have(in(z, pair(c, d)) <=> ((z === unorderedPair(c, d)) \/ (z === unorderedPair(c, c)))) by Restate.from(pairAxiom of (x -> unorderedPair(c, d), y -> unorderedPair(c, c)))

        val zcc = have((z === unorderedPair(c, c), in(c, x)) |- in(z, powerSet(setUnion(x, y)))) by Substitution.ApplyRules(z === unorderedPair(c, c))(upCC)
        val zcd = have((z === unorderedPair(c, d), in(c, x), in(d, y)) |- in(z, powerSet(setUnion(x, y)))) by Substitution.ApplyRules(z === unorderedPair(c, d))(upCD)

        have((in(c, x), in(d, y)) |- in(z, pair(c, d)) ==> in(z, powerSet(setUnion(x, y)))) by Tautology.from(zp, zcc, zcd)
        thenHave((in(c, x), in(d, y)) |- forall(z, in(z, pair(c, d)) ==> in(z, powerSet(setUnion(x, y))))) by RightForall

        have(thesis) by Tautology.from(lastStep, subsetAxiom of (x -> pair(c, d), y -> powerSet(setUnion(x, y))))
      }

      have(thesis) by Tautology.from(lastStep, powerSetAxiom of (y -> powerSet(setUnion(x, y)), x -> pair(c, d)))

    }

    thenHave((t === pair(c, d), in(c, x), in(d, y)) |- in(t, powerSet(powerSet(setUnion(x, y))))) by Substitution.ApplyRules(t === pair(c, d))
    thenHave(((t === pair(c, d)) /\ in(c, x) /\ in(d, y)) |- in(t, powerSet(powerSet(setUnion(x, y))))) by Restate
    thenHave(exists(d, ((t === pair(c, d)) /\ in(c, x) /\ in(d, y))) |- in(t, powerSet(powerSet(setUnion(x, y))))) by LeftExists
    thenHave(thesis) by LeftExists
  }

  /**
   * Theorem --- the union of two Cartesian products is a subset of the product of unions.
   *
   *    `a * b ∪ c * d ⊆ (a ∪ c) * (b ∪ d)`
   */
  val unionOfCartesianProducts = Theorem(
    subset(setUnion(cartesianProduct(a, b), cartesianProduct(c, d)), cartesianProduct(setUnion(a, c), setUnion(b, d)))
  ) {
    val axb = cartesianProduct(a, b)
    val cxd = cartesianProduct(c, d)

    val unionDef = have(in(z, setUnion(axb, cxd)) |- in(z, axb) \/ in(z, cxd)) by Weakening(setUnionMembership of (x -> axb, y -> cxd))

    /*
      z in a x b
      <=>
      exist x, y. z = (x, y); x in a; y in b
      ==> x in a U c, y in b U d
      ==> z in (a U c) x (b U d)
     */
    val zab = have(in(z, axb) |- in(z, cartesianProduct(setUnion(a, c), setUnion(b, d)))) subproof {
      have(forall(z, in(z, a) ==> in(z, setUnion(a, c)))) by Tautology.from(unionSubsetFirst of (b -> c), subsetAxiom of (x -> a, y -> setUnion(a, c)))
      val xa = thenHave((in(x, a) ==> in(x, setUnion(a, c)))) by InstantiateForall(x)

      have(forall(z, in(z, b) ==> in(z, setUnion(b, d)))) by Tautology.from(unionSubsetFirst of (a -> b, b -> d), subsetAxiom of (x -> b, y -> setUnion(b, d)))
      val yb = thenHave((in(y, b) ==> in(y, setUnion(b, d)))) by InstantiateForall(y)

      have(in(x, a) /\ in(y, b) |- in(x, setUnion(a, c)) /\ in(y, setUnion(b, d))) by Tautology.from(xa, yb)
      thenHave((z === pair(x, y)) /\ in(x, a) /\ in(y, b) |- (z === pair(x, y)) /\ in(x, setUnion(a, c)) /\ in(y, setUnion(b, d))) by Tautology
      thenHave((z === pair(x, y)) /\ in(x, a) /\ in(y, b) |- exists(y, (z === pair(x, y)) /\ in(x, setUnion(a, c)) /\ in(y, setUnion(b, d)))) by RightExists
      thenHave((z === pair(x, y)) /\ in(x, a) /\ in(y, b) |- exists(x, exists(y, (z === pair(x, y)) /\ in(x, setUnion(a, c)) /\ in(y, setUnion(b, d))))) by RightExists
      thenHave(exists(y, (z === pair(x, y)) /\ in(x, a) /\ in(y, b)) |- exists(x, exists(y, (z === pair(x, y)) /\ in(x, setUnion(a, c)) /\ in(y, setUnion(b, d))))) by LeftExists
      thenHave(exists(x, exists(y, (z === pair(x, y)) /\ in(x, a) /\ in(y, b))) |- exists(x, exists(y, (z === pair(x, y)) /\ in(x, setUnion(a, c)) /\ in(y, setUnion(b, d))))) by LeftExists

      have(thesis) by Tautology.from(lastStep, elemOfCartesianProduct of (x -> a, y -> b, t -> z), elemOfCartesianProduct of (x -> setUnion(a, c), y -> setUnion(b, d), t -> z))
    }

    val zcd =
      have(in(z, cxd) |- in(z, cartesianProduct(setUnion(a, c), setUnion(b, d)))) by Substitution.ApplyRules(unionCommutativity)(
        lastStep of (a -> c, b -> d, c -> a, d -> b)
      )

    have(in(z, setUnion(axb, cxd)) ==> in(z, cartesianProduct(setUnion(a, c), setUnion(b, d)))) by Tautology.from(unionDef, zab, zcd)
    thenHave(forall(z, in(z, setUnion(axb, cxd)) ==> in(z, cartesianProduct(setUnion(a, c), setUnion(b, d))))) by RightForall

    have(thesis) by Tautology.from(lastStep, subsetAxiom of (x -> setUnion(axb, cxd), y -> cartesianProduct(setUnion(a, c), setUnion(b, d))))
  }
   */
}
