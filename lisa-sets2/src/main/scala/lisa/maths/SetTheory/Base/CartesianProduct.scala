package lisa.maths.SetTheory.Base

import Replacement.|
import Union.∪
import Pair.{pair, given}

/**
  * The Cartesian product of two sets `A` and `B` is the set `A × B` containing
  * all pairs `(x, y)` of sets where `x ∈ A` and `y ∈ B`.
  */
object CartesianProduct extends lisa.Main {

  private val x, y, z = variable[Ind]
  private val a, b, c, d = variable[Ind]
  private val A, B = variable[Ind]
  private val S = variable[Ind]
  private val f = variable[Ind >>: Ind]

  /**
    * Cartesian Product --- Given two sets `A` and `B`, their Cartesian product
    * is the set containing pairs with the first element in `A` and the second
    * in `B`. The Cartesian product can be obtained by two applications of the
    * [[replacementSchema]].
    *
    *     `A × B = ⋃{A × {b} | b ∈ B} = ⋃{{(a, b) | a ∈ A} | b ∈ B}`
    *
    * (Alternatively, it can be seen as a comprehension over `𝒫(𝒫(A ∪ B))`, but
    *  it would be harder to manipulate in practice.)
    *
    * @param x set
    * @param y set
    */
  val × = DEF(λ(A, λ(B, {
    val `A × {b}` = {(a, b) | a ∈ A}
    ⋃({`A × {b}` | b ∈ B})
  }))).printInfix()
  val cartesianProduct = ×

  extension(x: set) {
    inline infix def ×(y: set): set = cartesianProduct(x)(y)
  }

  /**
    * Theorem --- `z ∈ A × B` implies `z = (x, y)` such that `x ∈ A` and `y ∈ B`.
    */
  val membershipNecessaryCondition = Lemma(
    z ∈ (A × B) |- ∃(x, ∃(y, x ∈ A /\ (y ∈ B) /\ ((x, y) === z)))
  ) {
    val `A × {b}` = {(a, b) | a ∈ A}

    val definition = have(z ∈ (A × B) <=> ∃(y, y ∈ {`A × {b}` | b ∈ B} /\ (z ∈ y))) by Congruence.from(
      ×.definition,
      unionAxiom of (x := {`A × {b}` | b ∈ B})
    )

    val firstReplacement = have(y ∈ {`A × {b}` | b ∈ B} /\ (z ∈ y) <=> ∃(b, b ∈ B /\ (`A × {b}` === y)) /\ (z ∈ y)) by Tautology.from(
      Replacement.membership of (S := B, f := λ(b, `A × {b}`))
    )

    have((b ∈ B, `A × {b}` === y, z ∈ y) |- z ∈ `A × {b}`) by Congruence
    val secondReplacement = thenHave((b ∈ B, `A × {b}` === y, z ∈ y) |- ∃(a, a ∈ A /\ ((a, b) === z))) by Tautology.fromLastStep(
      Replacement.membership of (S := A, y := z, f := λ(a, (a, b)))
    )

    have((b ∈ B, a ∈ A, (a, b) === z) |- (a ∈ A) /\ (b ∈ B) /\ ((a, b) === z)) by Restate
    thenHave((b ∈ B, a ∈ A, (a, b) === z) |- ∃(y, (a ∈ A) /\ (y ∈ B) /\ ((a, y) === z))) by RightExists
    thenHave((b ∈ B, a ∈ A, (a, b) === z) |- ∃(x, ∃(y, (x ∈ A) /\ (y ∈ B) /\ ((x, y) === z)))) by RightExists
    thenHave((b ∈ B, a ∈ A /\ ((a, b) === z)) |- ∃(x, ∃(y, (x ∈ A) /\ (y ∈ B) /\ ((x, y) === z)))) by Restate
    thenHave((b ∈ B, ∃(a, a ∈ A /\ ((a, b) === z))) |- ∃(x, ∃(y, (x ∈ A) /\ (y ∈ B) /\ ((x, y) === z)))) by LeftExists

    have((b ∈ B, `A × {b}` === y, z ∈ y) |- ∃(x, ∃(y, (x ∈ A) /\ (y ∈ B) /\ ((x, y) === z)))) by Cut(secondReplacement, lastStep)
    thenHave((b ∈ B /\ (`A × {b}` === y), z ∈ y) |- ∃(x, ∃(y, (x ∈ A) /\ (y ∈ B) /\ ((x, y) === z)))) by Restate
    thenHave((∃(b, b ∈ B /\ (`A × {b}` === y)), z ∈ y) |- ∃(x, ∃(y, (x ∈ A) /\ (y ∈ B) /\ ((x, y) === z)))) by LeftExists
    thenHave(∃(b, b ∈ B /\ (`A × {b}` === y)) /\ (z ∈ y) |- ∃(x, ∃(y, (x ∈ A) /\ (y ∈ B) /\ ((x, y) === z)))) by Restate

    have(y ∈ {`A × {b}` | b ∈ B} /\ (z ∈ y) |- ∃(x, ∃(y, (x ∈ A) /\ (y ∈ B) /\ ((x, y) === z)))) by Tautology.from(firstReplacement, lastStep)
    thenHave(∃(y, y ∈ {`A × {b}` | b ∈ B} /\ (z ∈ y)) |- ∃(x, ∃(y, (x ∈ A) /\ (y ∈ B) /\ ((x, y) === z)))) by LeftExists

    have(thesis) by Tautology.from(lastStep, definition)
  }

  /**
    * Theorem --- If `x ∈ A` and `y ∈ B` then `(x, y) ∈ (A × B)`.
    */
  val membershipSufficientCondition = Lemma(
    (x ∈ A, y ∈ B) |- (x, y) ∈ (A × B)
  ) {
    val `A × {y}` = {(x, y) | x ∈ A}

    have((x, y) ∈ ⋃({`A × {y}` | y ∈ B}) <=> ∃(z, z ∈ {`A × {y}` | y ∈ B} /\ ((x, y) ∈ z))) by Tautology.from(
      unionAxiom of (x := {`A × {y}` | y ∈ B}, z := (x, y))
    )
    val definition = thenHave((x, y) ∈ (A × B) <=> ∃(z, z ∈ {`A × {y}` | y ∈ B} /\ ((x, y) ∈ z))) by Substitute(×.definition)

    assume(x ∈ A)
    assume(y ∈ B)

    // We show that `z = A × {y}` satisfies the definition requirements

    have(x ∈ A /\ ((x, y) === (x, y))) by Tautology
    thenHave(∃(a, a ∈ A /\ ((a, y) === (x, y)))) by RightExists
    val firstReplacement = thenHave((x, y) ∈ `A × {y}`) by Tautology.fromLastStep(
      Replacement.membership of (S := A, y := (x, y), f := λ(x, (x, y)))
    )

    thenHave(y ∈ B /\ (`A × {y}` === `A × {y}`)) by Tautology
    thenHave(∃(b, b ∈ B /\ ({(x, b) | x ∈ A} === `A × {y}`))) by RightExists
    val secondReplacement = thenHave(`A × {y}` ∈ {`A × {y}` | y ∈ B}) by Tautology.fromLastStep(
      Replacement.membership of (S := B, f := λ(y, `A × {y}`), y := `A × {y}`)
    )

    have(`A × {y}` ∈ {`A × {y}` | y ∈ B} /\ ((x, y) ∈ `A × {y}`)) by RightAnd(secondReplacement, firstReplacement)
    thenHave(∃(z, z ∈ {`A × {y}` | y ∈ B} /\ ((x, y) ∈ z))) by RightExists

    have(thesis) by Tautology.from(lastStep, definition)
  }

  /**
    * Theorem --- `z ∈ A × B` if and only if `z = (x, y)` for some `x ∈ A` and `y ∈ B`.
    */
  val membership = Theorem(
    z ∈ (A × B) <=> ∃(x, ∃(y, x ∈ A /\ (y ∈ B) /\ ((x, y) === z)))
  ) {
    val `==>` = membershipNecessaryCondition

    val `<==` = have(∃(x, ∃(y, x ∈ A /\ (y ∈ B) /\ ((x, y) === z))) |- z ∈ (A × B)) subproof {
      have((x ∈ A, y ∈ B, (x, y) === z) |- z ∈ (A × B)) by Congruence.from(membershipSufficientCondition)
      thenHave(((x ∈ A) /\ (y ∈ B) /\ ((x, y) === z)) |- z ∈ (A × B)) by Restate
      thenHave(∃(y, ((x ∈ A) /\ (y ∈ B) /\ ((x, y) === z))) |- z ∈ (A × B)) by LeftExists
      thenHave(thesis) by LeftExists
    }

    have(thesis) by Tautology.from(`==>`, `<==`)
  }

  /**
   * Theorem --- `(x, y) ∈ A × B` if both `x ∈ A` and `y ∈ A`.
   *
   *  `(x, y) ∈ A × B <=> x ∈ A /\ y ∈ B`
    *
    * Follows from [[membership]].
   */
  val pairMembership = Theorem(
    (x, y) ∈ (A × B) <=> x ∈ A /\ y ∈ B
  ) {
    val `==>` =
      have((x ∈ A, y ∈ B) |- (x ∈ A) /\ (y ∈ B) /\ ((x, y) === (x, y))) by Tautology
      thenHave((x ∈ A, y ∈ B) |- ∃(b, (x ∈ A) /\ (b ∈ B) /\ ((x, b) === (x, y)))) by RightExists
      thenHave((x ∈ A, y ∈ B) |- ∃(a, ∃(b, (a ∈ A) /\ (b ∈ B) /\ ((a, b) === (x, y))))) by RightExists

    val `<==` = {
      have((a ∈ A, b ∈ B, (a, b) === (x, y)) |- a === x) by Tautology.from(Pair.extensionality of (c := x, d := y))
      val `x ∈ A` = have((a ∈ A, b ∈ B, (a, b) === (x, y)) |- x ∈ A) by Congruence.from(lastStep)

      have((a ∈ A, b ∈ B, (a, b) === (x, y)) |- b === y) by Tautology.from(Pair.extensionality of (c := x, d := y))
      val `y ∈ B` = have((a ∈ A, b ∈ B, (a, b) === (x, y)) |- y ∈ B) by Congruence.from(lastStep)

      have((a ∈ A) /\ (b ∈ B) /\ ((a, b) === (x, y)) |- (x ∈ A) /\ (y ∈ B)) by Tautology.from(`x ∈ A`, `y ∈ B`)
      thenHave(∃(b, (a ∈ A) /\ (b ∈ B) /\ ((a, b) === (x, y))) |- (x ∈ A) /\ (y ∈ B)) by LeftExists
      thenHave(∃(a, ∃(b, (a ∈ A) /\ (b ∈ B) /\ ((a, b) === (x, y)))) |- (x ∈ A) /\ (y ∈ B)) by LeftExists
    }

    have(thesis) by Tautology.from(`==>`, `<==`, membership of (z := (x, y)))
  }


  /**
    * Theorem --- The product of any set with ∅ on the left is ∅.
    *
    *  `∅ × B = ∅`
    *
    * In other words, `∅` is left-absorbing.
    */
  val leftEmpty = Theorem(
    ∅ × B === ∅
  ) {
    have(z ∈ (∅ × B) |- z ∈ ∅) subproof {
      assume(z ∈ (∅ × B))
      have(x ∈ ∅ /\ (y ∈ B) /\ (z === (x, y)) |- ()) by Tautology.from(EmptySet.definition)
      thenHave(∃(y, x ∈ ∅ /\ (y ∈ B) /\ (z === (x, y))) |- ()) by LeftExists
      thenHave(∃(x, ∃(y, x ∈ ∅ /\ (y ∈ B) /\ (z === (x, y)))) |- ()) by LeftExists
      thenHave(thesis) by Tautology.fromLastStep(membership of (A := ∅))
    }
    thenHave(z ∈ (∅ × B) <=> z ∈ ∅) by Tautology.fromLastStep(EmptySet.definition of (x := z))
    thenHave(thesis) by Extensionality
  }

  /**
    * Theorem --- The product of any set with ∅ on the right is ∅.
    *
    *  `A × ∅ = ∅`
    */
  val rightEmpty = Theorem(
    A × ∅ === ∅
  ) {
    have(z ∈ (A × ∅) |- z ∈ ∅) subproof {
      assume(z ∈ (A × ∅))
      have(x ∈ A /\ (y ∈ ∅) /\ (z === (x, y)) |- ()) by Tautology.from(EmptySet.definition of (x := y))
      thenHave(∃(y, x ∈ A /\ (y ∈ ∅) /\ (z === (x, y))) |- ()) by LeftExists
      thenHave(∃(x, ∃(y, x ∈ A /\ (y ∈ ∅) /\ (z === (x, y)))) |- ()) by LeftExists
      thenHave(thesis) by Tautology.fromLastStep(membership of (B := ∅))
    }
    thenHave(z ∈ (A × ∅) <=> z ∈ ∅) by Tautology.fromLastStep(EmptySet.definition of (x := z))
    thenHave(thesis) by Extensionality
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
