package lisa.maths.SetTheory.Ordinals

import lisa.maths.Quantifiers
import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Relations
import lisa.maths.SetTheory.Relations.Predef.*
import lisa.maths.SetTheory.Relations.Examples.MembershipRelation
import lisa.maths.SetTheory.Order
import lisa.maths.SetTheory.Order.Predef.*
import lisa.maths.SetTheory.Order.WellOrders.*

import WellOrder.*
import TransitiveSet.*
import InitialSegment.*
import MembershipRelation.*

/**
 * An ordinal is a set that is transitive and well-ordered by the membership relation:
 *
 *   `ordinal(α) <=> transitiveSet(α) /\ wellOrder(α, ∈_α)`
 *
 * @see [[TransitiveSet]]
 * @see [[WellOrder.wellOrder]]
 * @see [[MembershipRelation]]
 */
object Ordinal extends lisa.Main {

  private val x, y, z, a = variable[Ind]
  private val <, R, Q = variable[Ind]
  private val A, B, X = variable[Ind]
  private val α, β, γ, δ = variable[Ind]
  private val P = variable[Ind >>: Prop]
  private val C = variable[Class]

  extension (α: Expr[Ind]) {

    /**
     * Local notations for ordinal ordering.
     */
    inline infix def <(β: Expr[Ind]): Expr[Prop] = α ∈ β
    inline infix def <=(β: Expr[Ind]): Expr[Prop] = (α < β) \/ (α === β)
  }

  /**
   * Ordinal --- A set `α` is an ordinal if it is a transitive set that is
   * well-ordered by the membership relation `∈_α`.
   *
   *   `ordinal(α) <=> transitiveSet(α) /\ wellOrder(α, ∈_α)`
   *
   * @see [[transitiveSet]], [[membershipRelation]]
   */
  val ordinal = DEF(λ(α, transitiveSet(α) /\ wellOrder(α)(membershipRelation(α))))

  /**
   * Theorem --- The empty set is an ordinal.
   */
  val zeroOrdinal = Theorem(
    ordinal(∅)
  ) {
    have(wellOrder(∅)(membershipRelation(∅))) by Substitute(MembershipRelation.emptySet)(WellOrder.emptySet)
    thenHave(thesis) by Tautology.fromLastStep(
      TransitiveSet.emptySet,
      ordinal.definition of (α := ∅)
    )
  }

  /**
   * Zero is represented by the empty set.
   */
  val zero = ∅

  ////////////////////////////////////////////////////////////////////////////////
  section("Ordinal properties")

  /**
   * Theorem --- If `γ` is an ordinal such that `α ∈ β` and `β ∈ γ`, then `α ∈ γ`.
   *
   * Follows from the definition of a [[transitiveSet]].
   */
  val transitivity = Theorem(
    ordinal(γ) |- (α ∈ β) /\ (β ∈ γ) ==> (α ∈ γ)
  ) {
    have(thesis) by Tautology.from(
      ordinal.definition of (α := γ),
      TransitiveSet.transitivity of (x := α, y := β, A := γ)
    )
  }

  /**
   * Theorem --- If `α` is an ordinal then the membership relation on `α` is transitive.
   */
  val transitiveMembershipRelation = Theorem(
    ordinal(α) |- transitive(membershipRelation(α))(α)
  ) {
    assume(ordinal(α))
    have(thesis) by Tautology.from(
      WellOrder.transitivity of (A := α, < := membershipRelation(α)),
      ordinal.definition
    )
  }

  ////////////////////////////////////////////////////////////////////////////////
  section("Hereditary properties")

  /**
   * Ordinal are hereditarily transitive --- If `α` is an ordinal and `β ∈ α`, then `β` is transitive.
   */
  val hereditarilyTransitive = Theorem(
    (ordinal(α), β ∈ α) |- transitiveSet(β)
  ) {
    assume(ordinal(α))
    assume(β ∈ α)

    // Suppose that `x ∈ y` and `y ∈ β`. We show that `x ∈ β` holds.
    have((x ∈ y, y ∈ β) |- x ∈ β) subproof {
      assume(x ∈ y)
      assume(y ∈ β)

      // By transitivity of `α`, both `y ∈ α` and `x ∈ α` hold
      val `y ∈ α` = have(y ∈ α) by Tautology.from(transitivity of (α := y, β := β, γ := α))
      val `x ∈ α` = have(x ∈ α) by Tautology.from(lastStep, transitivity of (α := x, β := y, γ := α))

      // Which means that they are members of `∈_α`
      val `x ∈_α y` = have((x, y) ∈ membershipRelation(α)) by Tautology.from(MembershipRelation.membership of (A := α), `x ∈ α`, `y ∈ α`)
      val `y ∈_α β` = have((y, β) ∈ membershipRelation(α)) by Tautology.from(MembershipRelation.membership of (x := y, y := β, A := α), `y ∈ α`)

      // Since `(α, ∈_α)` is transitive, we get `x ∈_α β` and thus `x ∈ β` as desired
      have((x, β) ∈ membershipRelation(α)) by Tautology.from(
        transitiveMembershipRelation,
        Relations.BasicTheorems.appliedTransitivity of (R := membershipRelation(α), x := x, y := y, z := β, X := α),
        `x ∈ α`,
        `y ∈ α`,
        `x ∈_α y`,
        `y ∈_α β`,
      )
      thenHave(x ∈ β) by Tautology.fromLastStep(MembershipRelation.membership of (y := β, A := α))
    }
    thenHave((x ∈ y) /\ (y ∈ β) ==> x ∈ β) by Restate
    thenHave(∀(x, ∀(y, (x ∈ y) /\ (y ∈ β) ==> x ∈ β))) by Generalize
    thenHave(thesis) by Tautology.fromLastStep(transitiveSet.definition of (A := β))
  }

  /**
   * Theorem --- If `α` is an ordinal and `β ∈ α` then `(β, ∈_β)` is a well-order.
   */
  val hereditarilyWellOrdered = Theorem(
    (ordinal(α), β ∈ α) |- wellOrder(β)(membershipRelation(β))
  ) {
    assume(ordinal(α))
    assume(β ∈ α)

    // Irreflexivity: follows from the irreflexivity of any membership relation.
    val irreflexivity = have(irreflexive(membershipRelation(β))(β)) by Tautology.from(MembershipRelation.irreflexivity of (A := β))

    // Transitivity: Given `x ∈ y ∈ z ∈ β ∈ α`, then `x, y, z ∈ α` and since `(α, ∈_α)` is a well-order,
    // it follows that `x ∈ z` by transitivity.
    val transitivity = have(transitive(membershipRelation(β))(β)) subproof {
      have((x ∈ y, y ∈ z, z ∈ β) |- x ∈ z) subproof {
        assume(x ∈ y)
        assume(y ∈ z)
        assume(z ∈ β)

        // All of `x`, `y` and `z` belong to `α`
        val `z ∈ α` = have(z ∈ α) by Tautology.from(Ordinal.transitivity of (α := z, β := β, γ := α))
        val `y ∈ α` = have(y ∈ α) by Tautology.from(lastStep, Ordinal.transitivity of (α := y, β := z, γ := α))
        val `x ∈ α` = have(x ∈ α) by Tautology.from(lastStep, Ordinal.transitivity of (α := x, β := y, γ := α))

        // Which means that they belong to `∈_α`
        val `x ∈_α y` = have((x, y) ∈ membershipRelation(α)) by Tautology.from(MembershipRelation.membership of (x := x, y := y, A := α), `x ∈ α`, `y ∈ α`)
        val `y ∈_α z` = have((y, z) ∈ membershipRelation(α)) by Tautology.from(MembershipRelation.membership of (x := y, y := z, A := α), `y ∈ α`, `z ∈ α`)

        // Hence we can apply transitivity
        have((x, z) ∈ membershipRelation(α)) by Tautology.from(
          transitiveMembershipRelation,
          Relations.BasicTheorems.appliedTransitivity of (R := membershipRelation(α), X := α),
          `x ∈ α`,
          `y ∈ α`,
          `z ∈ α`,
          `x ∈_α y`,
          `y ∈_α z`,
        )
        thenHave(x ∈ z) by Tautology.fromLastStep(MembershipRelation.membership of (x := x, y := z, A := α))
      }
      // We must now convert that result to `∈_β`
      thenHave((x ∈ β, y ∈ β, z ∈ β) |- ((x, y) ∈ membershipRelation(β) /\ ((y, z) ∈ membershipRelation(β)) ==> (x, z) ∈ membershipRelation(β))) by Tautology.fromLastStep(
        MembershipRelation.membership of (x := x, y := y, A := β),
        MembershipRelation.membership of (x := y, y := z, A := β),
        MembershipRelation.membership of (x := x, y := z, A := β)
      )
      thenHave((x ∈ β) /\ (y ∈ β) /\ (z ∈ β) /\ (x, y) ∈ membershipRelation(β) /\ ((y, z) ∈ membershipRelation(β)) ==> (x, z) ∈ membershipRelation(β)) by Tautology
      thenHave(∀(x, ∀(y, ∀(z, (x ∈ β) /\ (y ∈ β) /\ (z ∈ β) /\ (x, y) ∈ membershipRelation(β) /\ ((y, z) ∈ membershipRelation(β)) ==> (x, z) ∈ membershipRelation(β))))) by Generalize
      thenHave(∀(x ∈ β, ∀(y ∈ β, ∀(z ∈ β, (x, y) ∈ membershipRelation(β) /\ ((y, z) ∈ membershipRelation(β)) ==> (x, z) ∈ membershipRelation(β))))) by Tableau
      thenHave(thesis) by Substitute(transitive.definition of (R := membershipRelation(β), X := β))
    }

    // Totality: Given `x, y ∈ β`, since `β ∈ α` we have `x, y ∈ α`, and thus we can conclude by totality of `∈_α`.
    val totality = have(total(membershipRelation(β))(β)) subproof {
      have((x ∈ β, y ∈ β) |- (x ∈ α) /\ (y ∈ α)) by Tautology.from(
        Ordinal.transitivity of (α := x, β := β, γ := α),
        Ordinal.transitivity of (α := y, β := β, γ := α)
      )
      thenHave((x ∈ β, y ∈ β) |- ((x, y) ∈ membershipRelation(α)) \/ ((y, x) ∈ membershipRelation(α)) \/ (x === y)) by Tautology.fromLastStep(
        ordinal.definition,
        WellOrder.totality of (< := membershipRelation(α), A := α),
        Relations.BasicTheorems.appliedTotality of (R := membershipRelation(α), X := α)
      )
      thenHave((x ∈ β) /\ (y ∈ β) ==> (x ∈ y) \/ (y ∈ x) \/ (x === y)) by Tautology.fromLastStep(
        MembershipRelation.membership of (x := x, y := y, A := α),
        MembershipRelation.membership of (x := y, y := x, A := α)
      )
      thenHave((x ∈ β) /\ (y ∈ β) ==> (((x, y) ∈ membershipRelation(β)) \/ ((y, x) ∈ membershipRelation(β)) \/ (x === y))) by Tautology.fromLastStep(
        MembershipRelation.membership of (x := x, y := y, A := β),
        MembershipRelation.membership of (x := y, y := x, A := β)
      )
      thenHave(∀(x, ∀(y, (x ∈ β) /\ (y ∈ β) ==> (((x, y) ∈ membershipRelation(β)) \/ ((y, x) ∈ membershipRelation(β)) \/ (x === y))))) by Generalize
      thenHave(∀(x ∈ β, ∀(y ∈ β, ((x, y) ∈ membershipRelation(β)) \/ ((y, x) ∈ membershipRelation(β)) \/ (x === y)))) by Tableau
      thenHave(thesis) by Substitute(total.definition of (R := membershipRelation(β), X := β))
    }

    // Well-foundedness: Given any non-empty `B ⊆ β`, by transitivity of `α`, `B ⊆ α` and therefore
    // `B` has a `∈_α`-minimal element `x ∈ B`. Since `∈_β ⊆ ∈_α`, `b` is also `∈_β`-minimal.
    val wellFoundedness = {
      have((B ⊆ β) /\ (B ≠ ∅) ==> ∃(x, minimal(x)(B)(membershipRelation(β)))) subproof {
        assume(B ⊆ β)
        assume(B ≠ ∅)

        // Since `β ⊆ α` one has `B ⊆ α` and therefore there exists `x ∈ B` which is
        // `∈_α`-minimal.
        val `β ⊆ α` = have(β ⊆ α) by Tautology.from(
          ordinal.definition,
          TransitiveSet.elementIsSubset of (x := β, A := α)
        )
        thenHave(B ⊆ α) by Tautology.fromLastStep(
          Subset.transitivity of (x := B, y := β, z := α),
        )
        val `x is ∈_α-minimal` = thenHave(∃(x, minimal(x)(B)(membershipRelation(α)))) by Tautology.fromLastStep(
          ordinal.definition,
          WellOrder.minimalElement of (A := α, < := membershipRelation(α))
        )

        // Since `∈_β ⊆ ∈_α`, x is also `∈_β`-minimal
        have(minimal(x)(B)(membershipRelation(α)) ==> minimal(x)(B)(membershipRelation(β))) by Tautology.from(
          Order.BasicTheorems.minimalElementSubset of (a := x, R := membershipRelation(α), Q := membershipRelation(β), A := B),
          MembershipRelation.monotonic of (A := β, B := α),
          `β ⊆ α`
        )
        val `x is ∈_α-minimal implies x is ∈_β-minimal` =
          thenHave(∀(x, minimal(x)(B)(membershipRelation(α)) ==> minimal(x)(B)(membershipRelation(β)))) by RightForall

        have(
          (
            ∀(x, minimal(x)(B)(membershipRelation(α)) ==> minimal(x)(B)(membershipRelation(β))),
            ∃(x, minimal(x)(B)(membershipRelation(α)))
          ) |-
            ∃(x, minimal(x)(B)(membershipRelation(β)))
        ) by Tableau
        thenHave(thesis) by Tautology.fromLastStep(
          `x is ∈_α-minimal`,
          `x is ∈_α-minimal implies x is ∈_β-minimal`,
        )
      }
      thenHave(∀(B, (B ⊆ β) /\ (B ≠ ∅) ==> ∃(x, minimal(x)(B)(membershipRelation(β))))) by RightForall
      thenHave(wellFounded(membershipRelation(β))(β)) by Substitute(wellFounded.definition of (R := membershipRelation(β), X := β))
    }

    // Conclude
    have(thesis) by Tautology.from(
      MembershipRelation.isRelation of (A := β),
      Relations.BasicTheorems.relationOnIsRelation of (R := membershipRelation(β), X := β),
      transitivity,
      irreflexivity,
      totality,
      wellFoundedness,
      strictPartialOrder.definition of (A := β, < := membershipRelation(β)),
      strictTotalOrder.definition of (A := β, < := membershipRelation(β)),
      wellOrder.definition of (A := β, < := membershipRelation(β))
    )
  }

  /**
   * Element of an ordinal --- If `α` is an ordinal and `β ∈ α` then `β` is an ordinal.
   */
  val elementOfOrdinal = Theorem(
    (ordinal(α), β ∈ α) |- ordinal(β)
  ) {
    have(thesis) by Tautology.from(
      hereditarilyWellOrdered,
      hereditarilyTransitive,
      ordinal.definition of (α := β)
    )
  }

  /**
   * Theorem --- If `β ∈ α` and `α` is an ordinal then `initialSegment(β)(α)(membershipRelation(α)) = β`.
   */
  val ordinalInitialSegment = Theorem(
    (ordinal(α), β ∈ α) |- initialSegment(β)(α)(membershipRelation(α)) === β
  ) {
    assume(ordinal(α))
    assume(β ∈ α)

    have(x ∈ initialSegment(β)(α)(membershipRelation(α)) <=> (x ∈ α) /\ ((x, β) ∈ membershipRelation(α))) by Tautology.from(
      InitialSegment.membership of (y := x, x := β, A := α, < := membershipRelation(α))
    )
    thenHave(x ∈ initialSegment(β)(α)(membershipRelation(α)) <=> (x ∈ α) /\ ((x ∈ α) /\ (β ∈ α) /\ (x ∈ β))) by Substitute(
      MembershipRelation.membership of (x := x, y := β, A := α)
    )
    thenHave(x ∈ initialSegment(β)(α)(membershipRelation(α)) <=> (x ∈ β)) by Tautology.fromLastStep(
      transitivity of (α := x, β := β, γ := α)
    )
    thenHave(thesis) by Extensionality
  }

  ////////////////////////////////////////////////////////////////////////////////
  section("Comparison")

  /**
   * Theorem --- If `(α, ∈_α)` is order-isomorphic to `(β, ∈_β)` then `α = β`
   */
  val isomorphic = Theorem(
    (α, membershipRelation(α)) ≈ (β, membershipRelation(β)) |- α === β
  ) {
    sorry
  }

  /**
   * Theorem --- Any two ordinals `α` and `β` are comparable.
   *
   * Also known as the law of trichotomy.
   */
  val comparability = Theorem(
    (ordinal(α), ordinal(β)) |- (α === β) \/ (α < β) \/ (β < α)
  ) {
    assume(ordinal(α))
    assume(ordinal(β))

    sorry
  }

  /**
    * Theorem --- If `α < β` then `¬(β <= α)`.
    */
  val asymmetry = Theorem(
    (ordinal(α), ordinal(β)) |- α < β <=> ¬(β <= α)
  ) {
    sorry
  }

  ////////////////////////////////////////////////////////////////////////////////
  section("Minimality")



  ////////////////////////////////////////////////////////////////////////////////
  section("Class of ordinals")

  /**
   * Definition --- `Ord` stands for the class of all ordinals.
   */
  val Ord: Constant[Class] = DEF(λ(α, ordinal(α)))

  /**
   * Theorem --- `Ord` is a proper class.
   *
   * Also known as the Burali-Forti paradox.
   */
  val `Ord is a proper class` = Theorem(
    proper(Ord)
  ) {
    have(A === Ord |- ()) subproof {
      // Towards a contradiction, assume that `A` is the set of all ordinals.
      assume(A === Ord)
      thenHave(α ∈ A <=> (α ∈ Ord)) by InstantiateForall(α)
      val `α ∈ A` = thenHave(α ∈ A <=> ordinal(α)) by Substitute(Ord.definition)

      // Notice that:
      // 1. A is transitive
      val `A is transitive` = have(transitiveSet(A)) subproof {
        have(α ∈ A ==> ordinal(α)) by Tautology.from(`α ∈ A`)
        thenHave((α ∈ A, β ∈ α) |- ordinal(β)) by Tautology.fromLastStep(elementOfOrdinal)
        thenHave((β ∈ α /\ (α ∈ A) ==> β ∈ A)) by Tautology.fromLastStep(`α ∈ A` of (α := β))
        thenHave(∀(β, ∀(α, (β ∈ α /\ (α ∈ A) ==> β ∈ A)))) by Generalize
        thenHave(thesis) by Substitute(transitiveSet.definition)
      }

      // 2. (A, ∈_A) is a well-order:
      val `(A, ∈_A) is a well-order` = have(wellOrder(A)(membershipRelation(A))) subproof {
        // a. ∈_A is irreflexive
        val irreflexivity = have(irreflexive(membershipRelation(A))(A)) by Tautology.from(MembershipRelation.irreflexivity)

        // b. ∈_A is transitive
        val transitivity = have(transitive(membershipRelation(A))(A)) subproof {
          have((ordinal(α), ordinal(β), ordinal(γ)) |- (α ∈ β) /\ (β ∈ γ) ==> (α ∈ γ)) by Weakening(Ordinal.transitivity)
          thenHave((α ∈ A) /\ (β ∈ A) /\ (γ ∈ A) /\ ((α, β) ∈ membershipRelation(A)) /\ ((β, γ) ∈ membershipRelation(A)) ==> ((α, γ) ∈ membershipRelation(A))) by Tautology.fromLastStep(
            `α ∈ A`,
            `α ∈ A` of (α := β),
            `α ∈ A` of (α := γ),
            MembershipRelation.membership of (x := α, y := β),
            MembershipRelation.membership of (x := β, y := γ),
            MembershipRelation.membership of (x := α, y := γ),
          )
          thenHave(∀(α, ∀(β, ∀(γ, (α ∈ A) /\ (β ∈ A) /\ (γ ∈ A) /\ ((α, β) ∈ membershipRelation(A)) /\ ((β, γ) ∈ membershipRelation(A)) ==> ((α, γ) ∈ membershipRelation(A)))))) by Generalize
          thenHave(∀(α ∈ A, ∀(β ∈ A, ∀(γ ∈ A, ((α, β) ∈ membershipRelation(A)) /\ ((β, γ) ∈ membershipRelation(A)) ==> ((α, γ) ∈ membershipRelation(A)))))) by Tableau
          thenHave(thesis) by Substitute(transitive.definition of (R := membershipRelation(A), X := A))
        }

        // c. ∈_A is total
        val totality = have(total(membershipRelation(A))(A)) subproof {
          have((ordinal(α) /\ ordinal(β)) ==> (α < β) \/ (β < α) \/ (α === β)) by Tautology.from(comparability)
          thenHave((α ∈ A) /\ (β ∈ A) ==> (((α, β) ∈ membershipRelation(A)) \/ ((β, α) ∈ membershipRelation(A)) \/ (α === β))) by Tautology.fromLastStep(
            `α ∈ A`,
            `α ∈ A` of (α := β),
            MembershipRelation.membership of (x := α, y := β),
            MembershipRelation.membership of (x := β, y := α),
          )
          thenHave(∀(α, ∀(β, (α ∈ A) /\ (β ∈ A) ==> (((α, β) ∈ membershipRelation(A)) \/ ((β, α) ∈ membershipRelation(A)) \/ (α === β))))) by Generalize
          thenHave(∀(α ∈ A, ∀(β ∈ A, ((α, β) ∈ membershipRelation(A)) \/ ((β, α) ∈ membershipRelation(A)) \/ (α === β)))) by Tableau
          thenHave(thesis) by Substitute(total.definition of (R := membershipRelation(A), X := A))
        }

        // d. ∈_A is well-founded
        val wellFoundedness = {
          /*
          have((B ⊆ A, B ≠ ∅) |- ∃(a, minimal(a)(B)(membershipRelation(A)))) subproof {
            assume(B ⊆ A)
            assume(B ≠ ∅)

            // We have that `B` is a non-∅ set of ordinals
            val `α ∈ B` = have(α ∈ B ==> ordinal(α)) by Tautology.from(
              `α ∈ A`,
              Subset.membership of (x := B, y := A, z := α)
            )
            thenHave(∀(α, α ∈ B ==> ordinal(α))) by RightForall

            // Thus we can apply [[setOfOrdinalsMinimalElement]]
            val minimalElement = have(∃(α, α ∈ B /\ ∀(β, β ∈ B ==> (α <= β)))) by Tautology.from(
              setOfOrdinalsMinimalElement of (A := B),
              lastStep
            )

            // We now replace `α <= β` by `(β, α) ∉ membershipRelation(A)`
            have((α ∈ B, β ∈ B, α <= β) |- (β, α) ∉ membershipRelation(A)) by Tautology.from(
              MembershipRelation.membership of (x := β, y := α),
              asymmetry of (α := β, β := α),
              `α ∈ B`, `α ∈ B` of (α := β)
            )
            thenHave((α ∈ B, β ∈ B ==> α <= β) |- β ∈ B ==> (β, α) ∉ membershipRelation(A)) by Tautology
            thenHave((α ∈ B, ∀(β, β ∈ B ==> α <= β)) |- β ∈ B ==> (β, α) ∉ membershipRelation(A)) by LeftForall
            thenHave((α ∈ B, ∀(β, β ∈ B ==> α <= β)) |- ∀(β, β ∈ B ==> (β, α) ∉ membershipRelation(A))) by RightForall
            thenHave((α ∈ B /\ ∀(β, β ∈ B ==> α <= β)) |- α ∈ B /\ ∀(β, β ∈ B ==> (β, α) ∉ membershipRelation(A))) by Tautology
            thenHave((α ∈ B /\ ∀(β, β ∈ B ==> α <= β)) |- ∃(α, α ∈ B /\ ∀(β, β ∈ B ==> (β, α) ∉ membershipRelation(A)))) by RightExists
            thenHave(∃(α, α ∈ B /\ ∀(β, β ∈ B ==> α <= β)) |- ∃(α, α ∈ B /\ ∀(β, β ∈ B ==> (β, α) ∉ membershipRelation(A)))) by LeftExists

            have(thesis) by Tautology.from(lastStep, minimalElement)
          }
          thenHave((B ⊆ A) /\ (B ≠ ∅) ==> ∃(α, α ∈ B /\ ∀(β, β ∈ B ==> (β, α) ∉ membershipRelation(A)))) by Restate
          thenHave(∀(B, (B ⊆ A) /\ (B ≠ ∅) ==> ∃(α, α ∈ B /\ ∀(β, β ∈ B ==> (β, α) ∉ membershipRelation(A))))) by Generalize
           */
          sorry
        }

        have(thesis) by Tautology.from(
          wellOrder.definition of (< := membershipRelation(A)),
          strictTotalOrder.definition of (< := membershipRelation(A)),
          strictPartialOrder.definition of (< := membershipRelation(A)),
          MembershipRelation.isRelation,
          transitivity,
          irreflexivity,
          totality,
          wellFoundedness,
        )
      }

      // Therefore A is an ordinal, which leads to A ∈ A.
      // A contradiction with [[FoundationAxiom.selfNonInclusion]].
      have(ordinal(A)) by Tautology.from(
        ordinal.definition of (α := A),
        `A is transitive`,
        `(A, ∈_A) is a well-order`
      )
      thenHave(A ∈ A) by Tautology.fromLastStep(`α ∈ A` of (α := A))
      thenHave(thesis) by Tautology.fromLastStep(FoundationAxiom.selfNonInclusion of (x := A))
    }
    thenHave(∃(A, ∀(α, α ∈ A <=> Ord(α))) |- ()) by LeftExists
    thenHave(¬(∃(A, ∀(α, α ∈ A <=> Ord(α))))) by Restate
    thenHave(thesis) by Substitute(proper.definition of (C := Ord))
  }
  val `Burali-Forti paradox` = `Ord is a proper class`

  ////////////////////////////////////////////////////////////////////////////////
  section("Successor ordinal")

  /**
   * Successor --- Given an ordinal `α`, its sucessor is `S(α) = α ∪ {α}`.
   */
  val S = DEF(λ(α, α ∪ singleton(α)))

  /**
   * Theorem --- For every ordinal `α` we have `β < S(α)` <=> `β <= α`.
   */
  val successorMembership = Theorem(
    ordinal(α) |- β < S(α) <=> (β <= α)
  ) {
    have(β ∈ (α ∪ singleton(α)) <=> (β <= α)) by Tautology.from(
      Union.membership of (x := α, y := singleton(α), z := β),
      Singleton.membership of (x := α, y := β)
    )
    thenHave(thesis) by Substitute(S.definition)
  }

  /**
   * Theorem --- For every ordinal `α` we have `α < S(α)`.
   */
  val lessThanSuccessor = Theorem(
    ordinal(α) |- α < S(α)
  ) {
    have(thesis) by Tautology.from(successorMembership of (β := α))
  }

  /**
   * Theorem --- If `α` is an ordinal, so is `S(α)`.
   */
  val sucessorIsOrdinal = Theorem(
    ordinal(α) |- ordinal(S(α))
  ) {
    sorry
  }

  ////////////////////////////////////////////////////////////////////////////////
  section("Classification of ordinals")

  /**
   * Successor ordinals --- `α` is a successor ordinal if `α = β + 1`.
   */
  val successorOrdinal = DEF(λ(α, ∃(β, ordinal(β) /\ (α === S(β)))))

  /**
   * Limit ordinal --- `α` is a limit ordinal if `α ≠ ∅` and `α` is not successor.
   */
  val limitOrdinal = DEF(λ(α, ordinal(α) /\ (α ≠ ∅) /\ ¬(successorOrdinal(α))))

  /**
   * Theorem --- An ordinal `α` is either zero, successor or limit.
   */
  val ordinalClassification = Theorem(
    ordinal(α) |- (α === ∅) \/ successorOrdinal(α) \/ limitOrdinal(α)
  ) {
    have(thesis) by Tautology.from(limitOrdinal.definition)
  }

}
