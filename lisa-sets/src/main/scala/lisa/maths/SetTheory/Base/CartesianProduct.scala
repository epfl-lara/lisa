package lisa.maths.SetTheory.Base

import Replacement.|
import Union.∪
import Pair.{_, given}
import Symbols._

/**
 * The Cartesian product of two sets `A` and `B` is the set `A × B` containing
 * all pairs `(x, y)` of sets where `x ∈ A` and `y ∈ B`.
 */
object CartesianProduct extends lisa.Main {

  private val S = variable[Ind]

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
  val × = DEF(
    λ(
      A,
      λ(
        B, {
          val `A × {b}` = { (a, b) | a ∈ A }
          ⋃({ `A × {b}` | b ∈ B })
        }
      )
    )
  ).printInfix()
  val cartesianProduct = ×

  extension (x: Expr[Ind]) {
    inline infix def ×(y: Expr[Ind]): Expr[Ind] = cartesianProduct(x)(y)
  }

  /**
   * Theorem --- `z ∈ A × B` implies `z = (x, y)` such that `x ∈ A` and `y ∈ B`.
   */
  val membershipNecessaryCondition = Lemma(
    z ∈ (A × B) |- ∃(x, ∃(y, x ∈ A /\ (y ∈ B) /\ ((x, y) === z)))
  ) {
    val `A × {b}` = { (a, b) | a ∈ A }

    val definition = have(z ∈ (A × B) <=> ∃(y, y ∈ { `A × {b}` | b ∈ B } /\ (z ∈ y))) by Congruence.from(
      ×.definition,
      unionAxiom of (x := { `A × {b}` | b ∈ B })
    )

    have(y ∈ { `A × {b}` | b ∈ B } <=> ∃(b, b ∈ B /\ (`A × {b}` === y))) by Replacement.apply
    val firstReplacement = thenHave(y ∈ { `A × {b}` | b ∈ B } /\ (z ∈ y) <=> ∃(b, b ∈ B /\ (`A × {b}` === y)) /\ (z ∈ y)) by Tautology

    have((b ∈ B, `A × {b}` === y, z ∈ y) |- z ∈ `A × {b}`) by Congruence
    val secondReplacement = thenHave((b ∈ B, `A × {b}` === y, z ∈ y) |- ∃(a, a ∈ A /\ ((a, b) === z))) by Tautology.fromLastStep(
      Replacement.membership of (S := A, y := z, F := λ(a, (a, b)))
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

    have(y ∈ { `A × {b}` | b ∈ B } /\ (z ∈ y) |- ∃(x, ∃(y, (x ∈ A) /\ (y ∈ B) /\ ((x, y) === z)))) by Tautology.from(firstReplacement, lastStep)
    thenHave(∃(y, y ∈ { `A × {b}` | b ∈ B } /\ (z ∈ y)) |- ∃(x, ∃(y, (x ∈ A) /\ (y ∈ B) /\ ((x, y) === z)))) by LeftExists

    have(thesis) by Tautology.from(lastStep, definition)
  }

  /**
   * Theorem --- If `x ∈ A` and `y ∈ B` then `(x, y) ∈ (A × B)`.
   */
  val membershipSufficientCondition = Lemma(
    (x ∈ A, y ∈ B) |- (x, y) ∈ (A × B)
  ) {
    val `A × {y}` = { (x, y) | x ∈ A }

    have((x, y) ∈ ⋃({ `A × {y}` | y ∈ B }) <=> ∃(z, z ∈ { `A × {y}` | y ∈ B } /\ ((x, y) ∈ z))) by Tautology.from(
      unionAxiom of (x := { `A × {y}` | y ∈ B }, z := (x, y))
    )
    val definition = thenHave((x, y) ∈ (A × B) <=> ∃(z, z ∈ { `A × {y}` | y ∈ B } /\ ((x, y) ∈ z))) by Substitute(×.definition)

    assume(x ∈ A)
    assume(y ∈ B)

    // We show that `z = A × {y}` satisfies the definition requirements

    have(x ∈ A /\ ((x, y) === (x, y))) by Tautology
    thenHave(∃(a, a ∈ A /\ ((a, y) === (x, y)))) by RightExists
    val firstReplacement = thenHave((x, y) ∈ `A × {y}`) by Tautology.fromLastStep(
      Replacement.membership of (A := A, y := (x, y), F := λ(x, (x, y)))
    )

    thenHave(y ∈ B /\ (`A × {y}` === `A × {y}`)) by Tautology
    thenHave(∃(b, b ∈ B /\ ({ (x, b) | x ∈ A } === `A × {y}`))) by RightExists
    val secondReplacement = thenHave(`A × {y}` ∈ { `A × {y}` | y ∈ B }) by Tautology.fromLastStep(
      Replacement.membership of (A := B, F := λ(y, `A × {y}`), y := `A × {y}`)
    )

    have(`A × {y}` ∈ { `A × {y}` | y ∈ B } /\ ((x, y) ∈ `A × {y}`)) by RightAnd(secondReplacement, firstReplacement)
    thenHave(∃(z, z ∈ { `A × {y}` | y ∈ B } /\ ((x, y) ∈ z))) by RightExists

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
   * Inversion theorem --- If `z ∈ A × B` then `z` is a pair.
   *
   * Important theorem, since it allows us to work on pairs only.
   */
  val inversion = Theorem(
    z ∈ (A × B) |- z === (fst(z), snd(z))
  ) {
    have(z === (x, y) |- z === (fst(z), snd(z))) by Restate.from(Pair.inversion of (a := x, b := y, x := z))
    thenHave((x ∈ A) /\ (y ∈ B) /\ (z === (x, y)) |- z === (fst(z), snd(z))) by Tautology
    thenHave(∃(y, (x ∈ A) /\ (y ∈ B) /\ (z === (x, y))) |- z === (fst(z), snd(z))) by LeftExists
    thenHave(∃(x, ∃(y, (x ∈ A) /\ (y ∈ B) /\ (z === (x, y)))) |- z === (fst(z), snd(z))) by LeftExists
    thenHave(thesis) by Substitute(membership)
  }

  /**
   * Theorem --- If `z ∈ A × B` then `fst(z) ∈ A`.
   */
  val fstMembership = Theorem(
    z ∈ (A × B) |- fst(z) ∈ A
  ) {
    have(z ∈ (A × B) |- (fst(z), snd(z)) ∈ (A × B)) by Congruence.from(inversion)
    thenHave(thesis) by Tautology.fromLastStep(pairMembership of (x := fst(z), y := snd(z)))
  }

  /**
   * Theorem --- If `z ∈ A × B` then `snd(z) ∈ B`.
   */
  val sndMembership = Theorem(
    z ∈ (A × B) |- snd(z) ∈ B
  ) {
    have(z ∈ (A × B) |- (fst(z), snd(z)) ∈ (A × B)) by Congruence.from(inversion)
    thenHave(thesis) by Tautology.fromLastStep(pairMembership of (x := fst(z), y := snd(z)))
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
   * Theorem --- The Cartesian product is monotonic:
   *
   *   If `A ⊆ C` and `B ⊆ D` then `A × B ⊆ C × D`.
   */
  val monotonic = Theorem(
    (A ⊆ C, B ⊆ D) |- (A × B) ⊆ (C × D)
  ) {
    have(
      (
        ∀(x, x ∈ A ==> x ∈ C),
        ∀(x, x ∈ B ==> x ∈ D),
        ∃(x, ∃(y, x ∈ A /\ (y ∈ B) /\ ((x, y) === z)))
      ) |-
        ∃(x, ∃(y, x ∈ C /\ (y ∈ D) /\ ((x, y) === z)))
    ) by Tableau
    thenHave((A ⊆ C, B ⊆ D, z ∈ (A × B)) |- (z ∈ (C × D))) by Substitute(
      ⊆.definition of (x := A, y := C),
      ⊆.definition of (x := B, y := D),
      membership,
      membership of (A := C, B := D)
    )
    thenHave((A ⊆ C, B ⊆ D) |- z ∈ (A × B) ==> (z ∈ (C × D))) by Restate
    thenHave((A ⊆ C, B ⊆ D) |- ∀(z, z ∈ (A × B) ==> z ∈ (C × D))) by Generalize
    thenHave(thesis) by Substitute(⊆.definition of (x := (A × B), y := (C × D)))
  }

  /**
   * Theorem --- The Cartesian product is left-monotonic:
   *
   *   If `A ⊆ C` then `A × B ⊆ C × B`.
   */
  val leftMonotonic = Theorem(
    (A ⊆ C) |- (A × B) ⊆ (C × B)
  ) {
    have(thesis) by Tautology.from(
      monotonic of (D := B),
      Subset.reflexivity of (x := B)
    )
  }

  /**
   * Theorem --- The Cartesian product is right-monotonic:
   *
   *   If `B ⊆ D` then `A × B ⊆ A × D`.
   */
  val rightMonotonic = Theorem(
    (B ⊆ D) |- (A × B) ⊆ (A × D)
  ) {
    have(thesis) by Tautology.from(
      monotonic of (C := A),
      Subset.reflexivity of (x := A)
    )
  }

  val R = variable[Ind]
  val CongTest = Theorem(
    (A × B) ∪ (C × D) ⊆ R
  ) {
    val left = have((A × B) ⊆ R) by Sorry
    val right = have((C × D) ⊆ R) by Sorry
    val s1 = Union.idempotence of (x := R)
    val s2 = Union.monotonic of (x := (A × B), y := (C × D), a := R, b := R)

    have(s1.statement) by Restate.from(s1)
    have(s2.statement) by Restate.from(s2)

    have(thesis) by Congruence.from(
      s1,
      s2,
      left,
      right
    )
  }
  /**
   * Theorem --- The union of two Cartesian products `A × B` and `C × D` is a subset
   * of the Cartesian product of the unions.
   */
  val union = Theorem(
    (A × B) ∪ (C × D) ⊆ ((A ∪ C) × (B ∪ D))
  ) {
    val RHS = (A ∪ C) × (B ∪ D)

    val left = have((A × B) ⊆ RHS) by Tautology.from(
      monotonic of (C := A ∪ C, D := B ∪ D),
      Union.leftSubset of (x := A, y := C),
      Union.leftSubset of (x := B, y := D)
    )
    val right = have((C × D) ⊆ RHS) by Tautology.from(
      monotonic of (A := C, B := D, C := A ∪ C, D := B ∪ D),
      Union.rightSubset of (x := A, y := C),
      Union.rightSubset of (x := B, y := D)
    )
    val s1 = Union.idempotence of (x := RHS)
    val s2 = Union.monotonic of (x := (A × B), y := (C × D), a := RHS, b := RHS)

    have(s1.statement) by Restate.from(s1)
    have(s2.statement) by Restate.from(s2)

    have(thesis) by Congruence.from(
      s1,
      s2,
      left,
      right
    )
  }
}
