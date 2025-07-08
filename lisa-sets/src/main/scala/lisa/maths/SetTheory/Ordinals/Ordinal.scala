package lisa.maths.SetTheory.Ordinals

import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Relations
import lisa.maths.SetTheory.Relations.Predef.*
import lisa.maths.SetTheory.Relations.Examples.MembershipRelation
import lisa.maths.SetTheory.Order.Predef.*
import lisa.maths.SetTheory.Order.WellOrders.*

import WellOrder.*
import TransitiveSet.*
import InitialSegment.*
import MembershipRelation.*

/**
 * An ordinal is a set that is transitive and well-ordered by the membership relation:
 *
 *   `ordinal(α) <=> transitiveSet(α) /\ wellOrdering(α, ∈_α)`
 *
 * @see [[TransitiveSet]]
 * @see [[WellOrder.wellOrdering]]
 * @see [[MembershipRelation]]
 */
object Ordinal extends lisa.Main {

  private val x, y, z = variable[Ind]
  private val <, R = variable[Ind]
  private val A, B, X = variable[Ind]
  private val α, β, γ, δ = variable[Ind]
  private val P = variable[Ind >>: Prop]

  extension (α: set) {

    /**
     * Local notations for ordinal ordering.
     */
    infix def <(β: set): Expr[Prop] = α ∈ β
    infix def <=(β: set): Expr[Prop] = (α < β) \/ (α === β)
  }

  /**
   * Ordinal --- A set `α` is an ordinal if it is transitive and `∈_α` is a
   * well-ordering on `α`.
   *
   *   `ordinal(α) <=> transitiveSet(α) /\ wellOrdering(α, ∈_α)`
   *
   * @see [[transitiveSet]], [[membershipRelation]]
   */
  val ordinal = DEF(λ(α, transitiveSet(α) /\ wellOrdering(α)(membershipRelation(α))))

  /**
   * Theorem --- The empty set is an ordinal.
   */
  val emptySet = Theorem(
    ordinal(∅)
  ) {
    have(wellOrdering(∅)(membershipRelation(∅))) by Substitute(MembershipRelation.emptySet)(WellOrder.emptySet)
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
    ordinal(α) |- transitive(membershipRelation(α))
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
        Relations.Properties.appliedTransitivity of (R := membershipRelation(α), x := x, y := y, z := β),
        `x ∈_α y`,
        `y ∈_α β`
      )
      thenHave(x ∈ β) by Tautology.fromLastStep(MembershipRelation.membership of (y := β, A := α))
    }
    thenHave((x ∈ y) /\ (y ∈ β) ==> x ∈ β) by Restate
    thenHave(∀(x, ∀(y, (x ∈ y) /\ (y ∈ β) ==> x ∈ β))) by Generalize
    thenHave(thesis) by Tautology.fromLastStep(transitiveSet.definition of (A := β))
  }

  /**
   * Theorem --- If `α` is an ordinal and `β ∈ α` then `(β, ∈_β)` is a well-ordering.
   */
  val hereditarilyWellOrdered = Theorem(
    (ordinal(α), β ∈ α) |- wellOrdering(β)(membershipRelation(β))
  ) {
    assume(ordinal(α))
    assume(β ∈ α)

    // Irreflexivity: follows from the irreflexivity of any membership relation.
    val irreflexivity = have(irreflexive(membershipRelation(β))) by Tautology.from(MembershipRelation.irreflexivity of (A := β))

    // Transitivity: Given `x ∈ y ∈ z ∈ β ∈ α`, then `x, y, z ∈ α` and since `(α, ∈_α)` is a well-ordering,
    // it follows that `x ∈ z` by transitivity.
    val transitivity = have(transitive(membershipRelation(β))) subproof {
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
          Relations.Properties.appliedTransitivity of (R := membershipRelation(α)),
          `x ∈_α y`,
          `y ∈_α z`
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
      thenHave(thesis) by Tautology.fromLastStep(
        Relations.Properties.restrictedTransitivity of (R := membershipRelation(β), X := β),
        MembershipRelation.isRelation of (A := β)
      )
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
        Relations.Properties.appliedTotality of (R := membershipRelation(α), X := α)
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
      thenHave(thesis) by Tautology.fromLastStep(
        MembershipRelation.isRelation of (A := β),
        total.definition of (R := membershipRelation(β), X := β)
      )
    }

    // Well-foundedness: Given any non-empty `B ⊆ β`, by transitivity of `α`, `B ⊆ α` and therefore
    // `B` has a `∈_α`-minimal element `b ∈ B`. Since `∈_β ⊆ ∈_α`, `b` is also `∈_β`-minimal.

    sorry
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
    sorry
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
   */
  val ordinalComparison = Theorem(
    (ordinal(α), ordinal(β)) |- (α === β) \/ (α < β) \/ (β < α)
  ) {
    sorry
  }

  ////////////////////////////////////////////////////////////////////////////////
  section("Minimality")

  /**
   * Theorem --- If `A` is a non-empty set of ordinals, then it admits a ∈-minimal element.
   *
   *   `∀α ∈ A. ordinal(α) /\ A ≠ ∅ ==> ∃α ∈ A. ∀β ∈ A. α <= β.
   */
  val ordinalSetMinimalElement = Theorem(
    (∀(α, α ∈ A ==> ordinal(α)), A ≠ ∅) |- ∃(α, α ∈ A /\ ∀(β, β ∈ A ==> (α <= β)))
  ) {
    assume(A ≠ ∅)

    // Since A ≠ ∅, take any α ∈ A.
    assume(∀(α, α ∈ A ==> ordinal(α)))
    val `α ordinal` = thenHave(α ∈ A ==> ordinal(α)) by InstantiateForall(α)

    // If ∀β ∈ A, α <= β, we are done.
    val case1 =
      have((α ∈ A, ∀(β, β ∈ A ==> (α <= β))) |- α ∈ A /\ ∀(β, β ∈ A ==> (α <= β))) by Restate
      thenHave((α ∈ A, ∀(β, β ∈ A ==> (α <= β))) |- ∃(α, α ∈ A /\ ∀(β, β ∈ A ==> (α <= β)))) by RightExists

    // If ∃β ∈ A, ¬(α <= β), then it means that β < α by [[ordinalComparison]]
    val case2 = have((α ∈ A, β ∈ A, ¬(α <= β)) |- ∃(α, α ∈ A /\ ∀(β, β ∈ A ==> (α <= β)))) subproof {
      assume(α ∈ A)
      assume(β ∈ A)
      assume(¬(α <= β))

      have(β < α) by Tautology.from(
        ordinalComparison,
        `α ordinal`,
        `α ordinal` of (α := β)
      )

      // Therefore A ∩ α ≠ ∅.
      val `A ∩ α ≠ ∅` = have((α ∈ A, β ∈ A, ¬(α <= β)) |- A ∩ α ≠ ∅) by Tautology.from(
        EmptySet.setWithElementNonEmpty of (x := β, y := (A ∩ α)),
        Intersection.membership of (z := β, x := A, y := α),
        lastStep
      )

      // Since α is well-ordered, we can take the ∈-minimal element of A ∩ α, call it δ.
      // It satisfies ∀β ∈ A. δ <= β
      have((δ ∈ (A ∩ α), minimal(δ)(A ∩ α)(membershipRelation(α))) |- ∀(β, β ∈ A ==> δ <= β)) subproof {
        assume(δ ∈ (A ∩ α))
        assume(minimal(δ)(A ∩ α)(membershipRelation(α)))

        /*
        val `δ is ordinal` = have(ordinal(δ)) by Tautology.from(
          Intersection.membership of (z := δ, x := A, y := α),
          Ordinal.elementOfOrdinal of (β := δ)
        )

        thenHave(∀(β, β ∈ (A ∩ α) ==> (β, δ) ∉ membershipRelation(α))) by Substitute(minimal.definition)
        thenHave(β ∈ (A ∩ α) ==> (β, δ) ∉ membershipRelation(α)) by InstantiateForall(β)
        thenHave(β ∈ (A ∩ α) ==> ¬((β ∈ α) /\ (δ ∈ α) /\ (β ∈ δ))) by Tautology.fromLastStep(MembershipRelation.membership of (x := β, y := δ, A := α))
        thenHave(β ∈ (A ∩ α) ==> ¬(β ∈ δ)) by Tautology.fromLastStep(
          Intersection.membership of (z := β, x := A, y := α),
          Intersection.membership of (z := δ, x := A, y := α)
        )
        thenHave(β ∈ (A ∩ α) ==> δ <= β) by Tautology.fromLastStep(
          Ordinal.ordinalComparison of (α := β, β := δ),
          Intersection.membership of (z := β, x := A, y := α),
          Ordinal.elementOfOrdinal of (β := δ)
        )
         */

        sorry
      }
      sorry
    }

    sorry
  }

  /**
   * Theorem --- If `P` is a non-empty class of ordinals, then it admits a ∈-minimal element.
   *
   *   `∃α ∈ On. P(α) ==> ∃α ∈ On. P(α) /\ ∀β < α. ¬P(β)`
   */
  val ordinalClassMinimalElement = Theorem(
    (ordinal(α), P(α)) |- ∃(α, ordinal(α) /\ P(α) /\ ∀(β, β ∈ α ==> ¬(P(β))))
  ) {
    assume(ordinal(α))
    assume(P(α))

    // Consider the set `Q = {β ∈ α | P(β)}`
    val Q = { β ∈ α | P(β) }
    val `β ∈ Q` = have(β ∈ Q <=> (β ∈ α) /\ P(β)) by Comprehension.apply
    val `β is an ordinal` = thenHave(β ∈ Q |- ordinal(β)) by Tautology.fromLastStep(elementOfOrdinal)

    // If Q is empty, `α` is minimal since there is no `β ∈ α` such that `P(β)` holds.
    val `case Q = ∅` = have(Q === ∅ |- ∃(α, ordinal(α) /\ P(α) /\ ∀(β, β ∈ α ==> ¬(P(β))))) subproof {
      assume(Q === ∅)

      have(¬(β ∈ ∅)) by Tautology.from(EmptySet.definition of (x := β))
      thenHave(¬(β ∈ Q)) by Substitute(Q === ∅)
      thenHave(¬(β ∈ α /\ P(β))) by Substitute(`β ∈ Q`)
      thenHave(β ∈ α ==> ¬(P(β))) by Tautology
      thenHave(∀(β, β ∈ α ==> ¬(P(β)))) by RightForall
      thenHave(ordinal(α) /\ P(α) /\ ∀(β, β ∈ α ==> ¬(P(β)))) by Tautology
      thenHave(thesis) by RightExists
    }

    // If Q is not empty, since `Q` is a set of ordinals it has a minimal element `β` that satisfies `P`.
    val `case Q ≠ ∅` = have(Q ≠ ∅ |- ∃(β, ordinal(β) /\ P(β) /\ ∀(x, x ∈ β ==> ¬(P(x))))) subproof {
      assume(Q ≠ ∅)

      // If `β ∈ S` is minimal, no element below it satisfy `P`.
      have((β ∈ Q, ∀(x, x ∈ Q ==> (β ∈ x) \/ (β === x))) |- ∀(x, x ∈ β ==> ¬(P(x)))) subproof {
        assume(β ∈ Q)

        val minimality = assume(∀(x, x ∈ Q ==> (β ∈ x) \/ (β === x)))

        val `x is an ordinal` = have(x ∈ β |- ordinal(x)) by Tautology.from(
          `β is an ordinal`,
          elementOfOrdinal of (α := β, β := x)
        )
        thenHave(x ∈ β ==> x ∈ α) by Tautology.fromLastStep(
          `β ∈ Q`,
          transitivity of (α := x, β := β, γ := α)
        )

        // Let x ∈ β. If x ∉ Q then ¬P(x) by comprehension.
        val `x ∉ Q` = have((x ∈ β, x ∉ Q) |- ¬(P(x))) by Tautology.from(`β ∈ Q` of (β := x), lastStep)

        // If x ∈ Q then by minimality either β ∈ x or β === x, and both cases lead to self-inclusion
        val `x ∈ Q` = have((x ∈ β, x ∈ Q) |- ¬(P(x))) subproof {
          have(x ∈ Q ==> (β ∈ x) \/ (β === x)) by InstantiateForall(x)(minimality)
          val cases = thenHave(x ∈ Q |- (β ∈ x) \/ (β === x)) by Restate

          assume(x ∈ β)
          assume(x ∈ Q)

          val case1 = have(β ∈ x |- ()) by Tautology.from(
            `x is an ordinal`,
            `β is an ordinal`,
            transitivity of (α := β, β := x, γ := β),
            WellFounded.selfNonInclusion of (x := β)
          )

          val case2 = {
            have(β === x |- β ∈ β) by Congruence
            thenHave(β === x |- ()) by Tautology.fromLastStep(WellFounded.selfNonInclusion of (x := β))
          }

          have(thesis) by Tautology.from(cases, case1, case2)
        }

        have(x ∈ β ==> ¬(P(x))) by Tautology.from(`x ∉ Q`, `x ∈ Q`)
        thenHave(thesis) by RightForall
      }
      thenHave((β ∈ Q) /\ ∀(x, x ∈ Q ==> (β ∈ x) \/ (β === x)) |- ordinal(β) /\ P(β) /\ ∀(x, x ∈ β ==> ¬(P(x)))) by Tautology.fromLastStep(`β ∈ Q`, `β is an ordinal`)
      thenHave((β ∈ Q) /\ ∀(x, x ∈ Q ==> (β ∈ x) \/ (β === x)) |- ∃(β, ordinal(β) /\ P(β) /\ ∀(x, x ∈ β ==> ¬(P(x))))) by RightExists
      val conclusion = thenHave(∃(β, (β ∈ Q) /\ ∀(x, x ∈ Q ==> (β ∈ x) \/ (β === x))) |- ∃(β, ordinal(β) /\ P(β) /\ ∀(x, x ∈ β ==> ¬(P(x))))) by LeftExists

      // We show that `Q` is a non-empty set of ordinals to satisfy the assumptions of [[ordinalSetMinimalElement]]
      have(β ∈ Q ==> β ∈ α) by Tautology.from(`β ∈ Q`)
      thenHave(β ∈ Q ==> ordinal(β)) by Tautology.fromLastStep(elementOfOrdinal)
      thenHave(∀(β, β ∈ Q ==> ordinal(β))) by RightForall

      have(thesis) by Tautology.from(
        lastStep,
        ordinalSetMinimalElement of (A := Q),
        conclusion
      )
    }

    have(thesis) by Tautology.from(`case Q = ∅`, `case Q ≠ ∅`)
  }

  ////////////////////////////////////////////////////////////////////////////////
  section("Class of ordinal")

  /**
   * Definition --- `On` stands for the class of all ordinals.
   */
  val On: Expr[Class] = DEF(λ(α, ordinal(α)))

  /**
   * Theorem --- `On` is a proper class.
   */
  val `On is a proper class` = Theorem(
    proper(On)
  ) {
    sorry
  }

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

  /**
   * Definition --- An ordinal `α` is an integer if and only if all its predecessors are zero or successors.
   */
  val integer = DEF(λ(α, ∀(β, β <= α ==> (β === ∅) \/ successorOrdinal(β))))
}
