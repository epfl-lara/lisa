package lisa.maths.SetTheory.Ordinals

import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Order
import lisa.maths.SetTheory.Order.LowerSet
import lisa.maths.SetTheory.Order.Predef._
import lisa.maths.SetTheory.Order.WellOrders._
import lisa.maths.SetTheory.Relations
import lisa.maths.SetTheory.Relations.Examples.MembershipRelation
import lisa.maths.SetTheory.Relations.Predef._

import WellOrder._
import TransitiveSet._
import InitialSegment._
import MembershipRelation._

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
        `y ∈_α β`
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
          Subset.transitivity of (x := B, y := β, z := α)
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
          `x is ∈_α-minimal implies x is ∈_β-minimal`
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

    // Let γ = α ∩ β.
    val G = α ∩ β

    // Local variable matching LowerSet's internal variable S
    val lsS: Variable[Ind] = variable[Ind]("S")

    // G ⊆ α and G ⊆ β
    val `G ⊆ α` = have(G ⊆ α) by Weakening(Intersection.subsetLeft of (x := α, y := β))
    val `G ⊆ β` = have(G ⊆ β) by Weakening(Intersection.subsetRight of (x := α, y := β))

    // G is a lower set of (α, ∈_α):
    // If x ∈ G and y ∈ α and y ∈ x, then y ∈ α (given) and y ∈ β (by transitivity of β since x ∈ β, y ∈ x)
    val `G lower set of α` = have(LowerSet.lowerSet(G)(α)(membershipRelation(α))) subproof {
      have((x ∈ G, y ∈ α, (y, x) ∈ membershipRelation(α)) |- y ∈ G) subproof {
        assume(x ∈ G)
        assume(y ∈ α)
        assume((y, x) ∈ membershipRelation(α))
        // x ∈ β from G ⊆ β, and y ∈ x from membership relation
        val `y ∈ x` = have(y ∈ x) by Tautology.from(MembershipRelation.membership of (x := y, y := x, A := α))
        // Since β is transitive and x ∈ β, y ∈ x implies y ∈ β
        val `x ∈ β` = have(x ∈ β) by Tautology.from(
          Subset.membership of (x := G, y := β, z := x),
          `G ⊆ β`
        )
        have(y ∈ β) by Tautology.from(
          TransitiveSet.transitivity of (A := β, x := y, y := x),
          ordinal.definition of (α := β),
          `x ∈ β`,
          `y ∈ x`
        )
        thenHave(thesis) by Tautology.fromLastStep(Intersection.membership of (z := y, x := α, y := β))
      }
      thenHave(x ∈ G |- y ∈ α ==> ((y, x) ∈ membershipRelation(α) ==> y ∈ G)) by Restate
      thenHave(x ∈ G |- ∀(y ∈ α, (y, x) ∈ membershipRelation(α) ==> y ∈ G)) by RightForall
      thenHave(x ∈ G ==> ∀(y ∈ α, (y, x) ∈ membershipRelation(α) ==> y ∈ G)) by Restate
      thenHave(∀(x ∈ G, ∀(y ∈ α, (y, x) ∈ membershipRelation(α) ==> y ∈ G))) by RightForall
      thenHave(thesis) by Tautology.fromLastStep(
        LowerSet.lowerSet.definition of (lsS := G, A := α, < := membershipRelation(α)),
        `G ⊆ α`
      )
    }

    // Key lemma: G = α ∨ G ∈ α
    // If G = α we are done. If G ≠ α, then (α ∖ G) is nonempty and a subset of α.
    // Take the ∈_α-minimal element δ. Show δ = G, hence G ∈ α.
    val `G = α or G ∈ α` = have((G === α) \/ (G ∈ α)) subproof {
      val D = α ∖ G

      // membership of the difference
      val `z ∈ D` = have(z ∈ D <=> (z ∈ α) /\ (z ∉ G)) subproof {
        have(z ∈ { z ∈ α | z ∉ G } <=> (z ∈ α) /\ (z ∉ G)) by Comprehension.apply
        thenHave(thesis) by Substitute(∖.definition of (x := α, y := G))
      }

      val `D ⊆ α` = have(D ⊆ α) subproof {
        have(z ∈ D ==> z ∈ α) by Tautology.from(`z ∈ D`)
        thenHave(∀(z, z ∈ D ==> z ∈ α)) by RightForall
        thenHave(thesis) by Substitute(⊆.definition of (x := D, y := α))
      }

      // Case 1: G = α (i.e. D = ∅)
      val case1 = have(D === ∅ |- G === α) subproof {
        assume(D === ∅)
        // If α ∖ G = ∅, then every element of α is in G, so α ⊆ G
        have(z ∉ D) by Congruence.from(EmptySet.definition of (x := z))
        thenHave(¬(z ∈ α /\ z ∉ G)) by Tautology.fromLastStep(`z ∈ D`)
        thenHave(z ∈ α ==> z ∈ G) by Tautology
        thenHave(∀(z, z ∈ α ==> z ∈ G)) by RightForall
        thenHave(α ⊆ G) by Substitute(⊆.definition of (x := α, y := G))
        thenHave(thesis) by Tautology.fromLastStep(
          Subset.doubleInclusion of (x := G, y := α),
          `G ⊆ α`
        )
      }

      // Case 2: D ≠ ∅
      val case2 = have(D ≠ ∅ |- G ∈ α) subproof {
        assume(D ≠ ∅)

        // D ⊆ α and D ≠ ∅, so by well-ordering of α, there exists a minimal element δ
        val minExists = have(∃(δ, minimal(δ)(D)(membershipRelation(α)))) by Tautology.from(
          ordinal.definition,
          WellOrder.minimalElement of (A := α, < := membershipRelation(α), B := D),
          `D ⊆ α`
        )

        // Now work with a specific minimal δ
        have(minimal(δ)(D)(membershipRelation(α)) |- G ∈ α) subproof {
          assume(minimal(δ)(D)(membershipRelation(α)))

          // Unpack: δ ∈ D and ∀(x, x ∈ D ==> (x, δ) ∉ ∈_α)
          val `δ ∈ D` = have(δ ∈ D) by Tautology.from(minimal.definition of (a := δ, A := D, < := membershipRelation(α)))
          val `δ ∈ α` = have(δ ∈ α) by Tautology.from(`δ ∈ D`, `z ∈ D` of (z := δ))
          val `δ ∉ G` = have(δ ∉ G) by Tautology.from(`δ ∈ D`, `z ∈ D` of (z := δ))

          have(∀(z, z ∈ D ==> (z, δ) ∉ membershipRelation(α))) by Tautology.from(minimal.definition of (a := δ, A := D, < := membershipRelation(α)))
          thenHave(z ∈ D ==> (z, δ) ∉ membershipRelation(α)) by InstantiateForall(z)
          val minimality = thenHave(z ∈ D ==> ¬((z ∈ α) /\ (δ ∈ α) /\ (z ∈ δ))) by Tautology.fromLastStep(MembershipRelation.membership of (x := z, y := δ, A := α))

          // Show initialSegment(δ)(α)(∈_α) = G, equivalently δ = G (by ordinalInitialSegment)
          // Since δ ∈ α and α is ordinal, initialSegment(δ)(α)(∈_α) = δ
          val segEqδ = have(initialSegment(δ)(α)(membershipRelation(α)) === δ) by Tautology.from(ordinalInitialSegment of (β := δ), `δ ∈ α`)

          // Show δ = G by double inclusion.
          // Part 1: δ ⊆ G
          // If x ∈ δ, then x ∈ α (by transitivity of α) and x ∉ D (by minimality since x ∈ δ means (x,δ)∈∈_α).
          // x ∉ D means ¬(x ∈ α ∧ x ∉ G), so since x ∈ α, we get x ∈ G.
          val `δ ⊆ G` = have(δ ⊆ G) subproof {
            have(z ∈ δ |- z ∈ G) subproof {
              assume(z ∈ δ)
              val `z ∈ α` = have(z ∈ α) by Tautology.from(
                transitivity of (α := z, β := δ, γ := α),
                `δ ∈ α`
              )
              // z ∈ δ and δ ∈ α and z ∈ α mean (z, δ) ∈ ∈_α
              // So z ∉ D by minimality
              have(z ∉ D) by Tautology.from(
                minimality,
                `z ∈ α`,
                `δ ∈ α`
              )
              thenHave(thesis) by Tautology.fromLastStep(`z ∈ D` of (z := z), `z ∈ α`)
            }
            thenHave(z ∈ δ ==> z ∈ G) by Restate
            thenHave(∀(z, z ∈ δ ==> z ∈ G)) by RightForall
            thenHave(thesis) by Substitute(⊆.definition of (x := δ, y := G))
          }

          // Part 2: G ⊆ δ
          // If x ∈ G then x ∈ α (since G ⊆ α). By totality of ∈_α, either x ∈ δ, δ ∈ x, or x = δ.
          // If δ ∈ x: Since x ∈ G and G is a lower set of α, and δ ∈ α and δ ∈ x, we get δ ∈ G. Contradiction with δ ∉ G.
          // If x = δ: Then δ ∈ G. Contradiction.
          // So x ∈ δ.
          val `G ⊆ δ` = have(G ⊆ δ) subproof {
            have(z ∈ G |- z ∈ δ) subproof {
              assume(z ∈ G)
              val `z ∈ α` = have(z ∈ α) by Tautology.from(
                Subset.membership of (x := G, y := α, z := z),
                `G ⊆ α`
              )
              // By totality on α: z ∈ δ, δ ∈ z, or z = δ
              val trichotomy = have((z ∈ δ) \/ (δ ∈ z) \/ (z === δ)) by Tautology.from(
                ordinal.definition,
                WellOrder.totality of (A := α, < := membershipRelation(α)),
                Relations.BasicTheorems.appliedTotality of (R := membershipRelation(α), X := α, x := z, y := δ),
                MembershipRelation.membership of (x := z, y := δ, A := α),
                MembershipRelation.membership of (x := δ, y := z, A := α),
                `z ∈ α`,
                `δ ∈ α`
              )

              // Case δ ∈ z: since G is lower set and z ∈ G and δ ∈ α, (δ, z) ∈ ∈_α, so δ ∈ G. Contradiction.
              val `case δ ∈ z` = have(δ ∈ z |- z ∈ δ) subproof {
                assume(δ ∈ z)
                have((δ, z) ∈ membershipRelation(α)) by Tautology.from(
                  MembershipRelation.membership of (x := δ, y := z, A := α),
                  `δ ∈ α`,
                  `z ∈ α`
                )
                have(δ ∈ G) by Tautology.from(
                  LowerSet.membership of (lsS := G, A := α, < := membershipRelation(α), x := z, y := δ),
                  `G lower set of α`,
                  `δ ∈ α`,
                  lastStep
                )
                thenHave(thesis) by Tautology.fromLastStep(`δ ∉ G`)
              }

              // Case z = δ: then δ ∈ G. Contradiction.
              val `case z = δ` = have((z === δ) |- z ∈ δ) subproof {
                assume(z === δ)
                have(δ ∈ G) by Congruence
                thenHave(thesis) by Tautology.fromLastStep(`δ ∉ G`)
              }

              have(thesis) by Tautology.from(trichotomy, `case δ ∈ z`, `case z = δ`)
            }
            thenHave(z ∈ G ==> z ∈ δ) by Restate
            thenHave(∀(z, z ∈ G ==> z ∈ δ)) by RightForall
            thenHave(thesis) by Substitute(⊆.definition of (x := G, y := δ))
          }

          // G = δ by double inclusion
          val `G = δ` = have(G === δ) by Tautology.from(
            Subset.doubleInclusion of (x := G, y := δ),
            `δ ⊆ G`,
            `G ⊆ δ`
          )

          // Since δ ∈ α, G ∈ α
          have(thesis) by Congruence.from(`G = δ`, `δ ∈ α`)
        }
        thenHave(minimal(δ)(D)(membershipRelation(α)) ==> (G ∈ α)) by Restate
        thenHave(∀(δ, minimal(δ)(D)(membershipRelation(α)) ==> (G ∈ α))) by RightForall
        have(thesis) by Tautology.from(lastStep, minExists)
      }

      have(thesis) by Tautology.from(case1, case2)
    }

    // By symmetry (swapping α and β): G = β ∨ G ∈ β
    // G' = β ∩ α = α ∩ β = G (by commutativity of intersection)
    val `G = β or G ∈ β` = have((G === β) \/ (G ∈ β)) subproof {
      // β ∩ α = α ∩ β
      val comm = have(G === (β ∩ α)) by Weakening(Intersection.commutativity of (x := α, y := β))

      // The same argument with α and β swapped gives (β ∩ α) = β ∨ (β ∩ α) ∈ β
      // But we need to redo the argument. Instead, let's use the symmetric structure.
      // Actually, the proof above was specifically for α. Let's do the same for β.

      val D2 = β ∖ G
      val `z ∈ D2` = have(z ∈ D2 <=> (z ∈ β) /\ (z ∉ G)) subproof {
        have(z ∈ { z ∈ β | z ∉ G } <=> (z ∈ β) /\ (z ∉ G)) by Comprehension.apply
        thenHave(thesis) by Substitute(∖.definition of (x := β, y := G))
      }

      val `D2 ⊆ β` = have(D2 ⊆ β) subproof {
        have(z ∈ D2 ==> z ∈ β) by Tautology.from(`z ∈ D2`)
        thenHave(∀(z, z ∈ D2 ==> z ∈ β)) by RightForall
        thenHave(thesis) by Substitute(⊆.definition of (x := D2, y := β))
      }

      // G is a lower set of (β, ∈_β)
      val `G lower set of β` = have(LowerSet.lowerSet(G)(β)(membershipRelation(β))) subproof {
        have((x ∈ G, y ∈ β, (y, x) ∈ membershipRelation(β)) |- y ∈ G) subproof {
          assume(x ∈ G)
          assume(y ∈ β)
          assume((y, x) ∈ membershipRelation(β))
          val `y ∈ x` = have(y ∈ x) by Tautology.from(MembershipRelation.membership of (x := y, y := x, A := β))
          val `x ∈ α` = have(x ∈ α) by Tautology.from(
            Subset.membership of (x := G, y := α, z := x),
            `G ⊆ α`
          )
          have(y ∈ α) by Tautology.from(
            TransitiveSet.transitivity of (A := α, x := y, y := x),
            ordinal.definition,
            `x ∈ α`,
            `y ∈ x`
          )
          thenHave(thesis) by Tautology.fromLastStep(Intersection.membership of (z := y, x := α, y := β))
        }
        thenHave(x ∈ G |- y ∈ β ==> ((y, x) ∈ membershipRelation(β) ==> y ∈ G)) by Restate
        thenHave(x ∈ G |- ∀(y ∈ β, (y, x) ∈ membershipRelation(β) ==> y ∈ G)) by RightForall
        thenHave(x ∈ G ==> ∀(y ∈ β, (y, x) ∈ membershipRelation(β) ==> y ∈ G)) by Restate
        thenHave(∀(x ∈ G, ∀(y ∈ β, (y, x) ∈ membershipRelation(β) ==> y ∈ G))) by RightForall
        thenHave(thesis) by Tautology.fromLastStep(
          LowerSet.lowerSet.definition of (lsS := G, A := β, < := membershipRelation(β)),
          `G ⊆ β`
        )
      }

      // Case 1: D2 = ∅ → G = β
      val case1b = have(D2 === ∅ |- G === β) subproof {
        assume(D2 === ∅)
        have(z ∉ D2) by Congruence.from(EmptySet.definition of (x := z))
        thenHave(¬(z ∈ β /\ z ∉ G)) by Tautology.fromLastStep(`z ∈ D2`)
        thenHave(z ∈ β ==> z ∈ G) by Tautology
        thenHave(∀(z, z ∈ β ==> z ∈ G)) by RightForall
        thenHave(β ⊆ G) by Substitute(⊆.definition of (x := β, y := G))
        thenHave(thesis) by Tautology.fromLastStep(
          Subset.doubleInclusion of (x := G, y := β),
          `G ⊆ β`
        )
      }

      // Case 2: D2 ≠ ∅ → G ∈ β
      val case2b = have(D2 ≠ ∅ |- G ∈ β) subproof {
        assume(D2 ≠ ∅)

        val minExists2 = have(∃(δ, minimal(δ)(D2)(membershipRelation(β)))) by Tautology.from(
          ordinal.definition of (α := β),
          WellOrder.minimalElement of (A := β, < := membershipRelation(β), B := D2),
          `D2 ⊆ β`
        )

        have(minimal(δ)(D2)(membershipRelation(β)) |- G ∈ β) subproof {
          assume(minimal(δ)(D2)(membershipRelation(β)))

          val `δ ∈ D2` = have(δ ∈ D2) by Tautology.from(minimal.definition of (a := δ, A := D2, < := membershipRelation(β)))
          val `δ ∈ β` = have(δ ∈ β) by Tautology.from(`δ ∈ D2`, `z ∈ D2` of (z := δ))
          val `δ ∉ G` = have(δ ∉ G) by Tautology.from(`δ ∈ D2`, `z ∈ D2` of (z := δ))

          have(∀(z, z ∈ D2 ==> (z, δ) ∉ membershipRelation(β))) by Tautology.from(minimal.definition of (a := δ, A := D2, < := membershipRelation(β)))
          thenHave(z ∈ D2 ==> (z, δ) ∉ membershipRelation(β)) by InstantiateForall(z)
          val minimality2 = thenHave(z ∈ D2 ==> ¬((z ∈ β) /\ (δ ∈ β) /\ (z ∈ δ))) by Tautology.fromLastStep(MembershipRelation.membership of (x := z, y := δ, A := β))

          // δ ⊆ G
          val `δ ⊆ G` = have(δ ⊆ G) subproof {
            have(z ∈ δ |- z ∈ G) subproof {
              assume(z ∈ δ)
              val `z ∈ β` = have(z ∈ β) by Tautology.from(
                transitivity of (α := z, β := δ, γ := β),
                ordinal.definition of (α := β),
                `δ ∈ β`
              )
              have(z ∉ D2) by Tautology.from(minimality2, `z ∈ β`, `δ ∈ β`)
              thenHave(thesis) by Tautology.fromLastStep(`z ∈ D2` of (z := z), `z ∈ β`)
            }
            thenHave(z ∈ δ ==> z ∈ G) by Restate
            thenHave(∀(z, z ∈ δ ==> z ∈ G)) by RightForall
            thenHave(thesis) by Substitute(⊆.definition of (x := δ, y := G))
          }

          // G ⊆ δ
          val `G ⊆ δ` = have(G ⊆ δ) subproof {
            have(z ∈ G |- z ∈ δ) subproof {
              assume(z ∈ G)
              val `z ∈ β` = have(z ∈ β) by Tautology.from(
                Subset.membership of (x := G, y := β, z := z),
                `G ⊆ β`
              )
              val trichotomy2 = have((z ∈ δ) \/ (δ ∈ z) \/ (z === δ)) by Tautology.from(
                ordinal.definition of (α := β),
                WellOrder.totality of (A := β, < := membershipRelation(β)),
                Relations.BasicTheorems.appliedTotality of (R := membershipRelation(β), X := β, x := z, y := δ),
                MembershipRelation.membership of (x := z, y := δ, A := β),
                MembershipRelation.membership of (x := δ, y := z, A := β),
                `z ∈ β`,
                `δ ∈ β`
              )
              val `case δ ∈ z` = have(δ ∈ z |- z ∈ δ) subproof {
                assume(δ ∈ z)
                have((δ, z) ∈ membershipRelation(β)) by Tautology.from(
                  MembershipRelation.membership of (x := δ, y := z, A := β),
                  `δ ∈ β`,
                  `z ∈ β`
                )
                have(δ ∈ G) by Tautology.from(
                  LowerSet.membership of (lsS := G, A := β, < := membershipRelation(β), x := z, y := δ),
                  `G lower set of β`,
                  `δ ∈ β`,
                  lastStep
                )
                thenHave(thesis) by Tautology.fromLastStep(`δ ∉ G`)
              }
              val `case z = δ` = have((z === δ) |- z ∈ δ) subproof {
                assume(z === δ)
                have(δ ∈ G) by Congruence
                thenHave(thesis) by Tautology.fromLastStep(`δ ∉ G`)
              }
              have(thesis) by Tautology.from(trichotomy2, `case δ ∈ z`, `case z = δ`)
            }
            thenHave(z ∈ G ==> z ∈ δ) by Restate
            thenHave(∀(z, z ∈ G ==> z ∈ δ)) by RightForall
            thenHave(thesis) by Substitute(⊆.definition of (x := G, y := δ))
          }

          val `G = δ` = have(G === δ) by Tautology.from(
            Subset.doubleInclusion of (x := G, y := δ),
            `δ ⊆ G`,
            `G ⊆ δ`
          )

          have(thesis) by Congruence.from(`G = δ`, `δ ∈ β`)
        }
        thenHave(minimal(δ)(D2)(membershipRelation(β)) ==> (G ∈ β)) by Restate
        thenHave(∀(δ, minimal(δ)(D2)(membershipRelation(β)) ==> (G ∈ β))) by RightForall
        have(thesis) by Tautology.from(lastStep, minExists2)
      }

      have(thesis) by Tautology.from(case1b, case2b)
    }

    // Now combine: (G = α ∨ G ∈ α) and (G = β ∨ G ∈ β)
    // Case 1: G = α and G = β → α = β
    val case1final = have(((G === α), (G === β)) |- (α === β) \/ (α ∈ β) \/ (β ∈ α)) subproof {
      assume(G === α)
      assume(G === β)
      have(α === β) by Congruence
      thenHave(thesis) by Tautology.fromLastStep()
    }
    // Case 2: G = α and G ∈ β → α ∈ β
    val case2final = have(((G === α), G ∈ β) |- (α === β) \/ (α ∈ β) \/ (β ∈ α)) subproof {
      assume(G === α)
      assume(G ∈ β)
      have(α ∈ β) by Congruence
      thenHave(thesis) by Tautology.fromLastStep()
    }
    // Case 3: G ∈ α and G = β → β ∈ α
    val case3final = have((G ∈ α, (G === β)) |- (α === β) \/ (α ∈ β) \/ (β ∈ α)) subproof {
      assume(G ∈ α)
      assume(G === β)
      have(β ∈ α) by Congruence
      thenHave(thesis) by Tautology.fromLastStep()
    }
    // Case 4: G ∈ α and G ∈ β → G ∈ (α ∩ β) = G, i.e. G ∈ G. Contradiction.
    val case4 = have((G ∈ α, G ∈ β) |- (α === β) \/ (α ∈ β) \/ (β ∈ α)) subproof {
      assume(G ∈ α)
      assume(G ∈ β)
      have(G ∈ G) by Tautology.from(Intersection.membership of (z := G, x := α, y := β))
      thenHave(thesis) by Tautology.fromLastStep(FoundationAxiom.selfNonInclusion of (x := G))
    }

    have(thesis) by Tautology.from(
      `G = α or G ∈ α`,
      `G = β or G ∈ β`,
      case1final,
      case2final,
      case3final,
      case4
    )
  }

  /**
   * Theorem --- If `α < β` then `¬(β <= α)`.
   */
  val asymmetry = Theorem(
    (ordinal(α), ordinal(β)) |- α < β <=> ¬(β <= α)
  ) {
    // Forward: α ∈ β → ¬(β ∈ α ∨ β = α)
    val forward = have((ordinal(α), ordinal(β), α ∈ β) |- ¬((β ∈ α) \/ (β === α))) subproof {
      assume(ordinal(α))
      assume(ordinal(β))
      assume(α ∈ β)

      // If β ∈ α, then by transitivity β ∈ β, contradiction
      val case1 = have(β ∈ α |- ()) subproof {
        assume(β ∈ α)
        have(β ∈ β) by Tautology.from(transitivity of (α := β, β := α, γ := β))
        thenHave(thesis) by Tautology.fromLastStep(FoundationAxiom.selfNonInclusion of (x := β))
      }

      // If β = α, then α ∈ α, contradiction
      val case2 = have((β === α) |- ()) subproof {
        assume(β === α)
        have(α ∈ α) by Congruence
        thenHave(thesis) by Tautology.fromLastStep(FoundationAxiom.selfNonInclusion of (x := α))
      }

      have(thesis) by Tautology.from(case1, case2)
    }

    // Backward: ¬(β ∈ α ∨ β = α) → α ∈ β
    val backward = have((ordinal(α), ordinal(β), ¬((β ∈ α) \/ (β === α))) |- α ∈ β) subproof {
      assume(ordinal(α))
      assume(ordinal(β))
      assume(¬((β ∈ α) \/ (β === α)))
      // By comparability: α = β ∨ α ∈ β ∨ β ∈ α
      // ¬(β ∈ α) rules out β ∈ α
      // ¬(β = α) rules out α = β (since α = β ↔ β = α)
      have(thesis) by Tautology.from(comparability)
    }

    have(thesis) by Tautology.from(forward, backward)
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
            MembershipRelation.membership of (x := α, y := γ)
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
            MembershipRelation.membership of (x := β, y := α)
          )
          thenHave(∀(α, ∀(β, (α ∈ A) /\ (β ∈ A) ==> (((α, β) ∈ membershipRelation(A)) \/ ((β, α) ∈ membershipRelation(A)) \/ (α === β))))) by Generalize
          thenHave(∀(α ∈ A, ∀(β ∈ A, ((α, β) ∈ membershipRelation(A)) \/ ((β, α) ∈ membershipRelation(A)) \/ (α === β)))) by Tableau
          thenHave(thesis) by Substitute(total.definition of (R := membershipRelation(A), X := A))
        }

        // d. ∈_A is well-founded
        val wellFoundedness = {
          have((B ⊆ A, B ≠ ∅) |- ∃(a, minimal(a)(B)(membershipRelation(A)))) subproof {
            assume(B ⊆ A)
            assume(B ≠ ∅)

            // We have that `B` is a non-∅ set of ordinals
            val `α ∈ B` = have(α ∈ B ==> ordinal(α)) by Tautology.from(
              `α ∈ A`,
              Subset.membership of (x := B, y := A, z := α)
            )
            thenHave(∀(α, α ∈ B ==> ordinal(α))) by RightForall

            // Prove inline: B has a ≤-minimal element
            // Since B ≠ ∅, pick any α₀ ∈ B. α₀ is an ordinal.
            // Case 1: B ∩ α₀ = ∅ → α₀ is minimal.
            // Case 2: B ∩ α₀ ≠ ∅ → use well-ordering of α₀ to find minimal δ in B ∩ α₀,
            //   then show δ is ≤-minimal in all of B.
            val minimalElement = have(∃(α, α ∈ B /\ ∀(β, β ∈ B ==> (α <= β)))) subproof {
              // Pick α ∈ B
              val `α ordinal from B` = have(α ∈ B |- ordinal(α)) by Tautology.from(`α ∈ B`)

              // Case 1: B ∩ α = ∅ → α is minimal
              val case1 = have((α ∈ B, (B ∩ α) === ∅) |- ∃(α, α ∈ B /\ ∀(β, β ∈ B ==> (α <= β)))) subproof {
                assume(α ∈ B)
                assume((B ∩ α) === ∅)

                have(β ∉ (B ∩ α)) by Congruence.from(EmptySet.definition of (x := β))
                thenHave(¬(β ∈ B /\ β ∈ α)) by Substitute(Intersection.membership of (z := β, x := B, y := α))
                thenHave(β ∈ B ==> ¬(β ∈ α)) by Tautology
                val `β ∉ α` = thenHave(β ∈ B |- ¬(β ∈ α)) by Restate

                // By comparability: since ¬(β ∈ α), either α ∈ β or α = β, so α ≤ β
                have(β ∈ B |- (α <= β)) by Tautology.from(
                  `β ∉ α`,
                  comparability of (β := β),
                  `α ordinal from B`,
                  `α ordinal from B` of (α := β)
                )
                thenHave(β ∈ B ==> (α <= β)) by Restate
                thenHave(∀(β, β ∈ B ==> (α <= β))) by RightForall
                thenHave(α ∈ B /\ ∀(β, β ∈ B ==> (α <= β))) by Tautology
                thenHave(thesis) by RightExists
              }

              // Case 2: B ∩ α ≠ ∅ → find minimal in B ∩ α
              val case2 = have((α ∈ B, (B ∩ α) ≠ ∅) |- ∃(α, α ∈ B /\ ∀(β, β ∈ B ==> (α <= β)))) subproof {
                assume(α ∈ B)
                assume((B ∩ α) ≠ ∅)

                val `α is ordinal` = have(ordinal(α)) by Tautology.from(`α ordinal from B`)

                // α is well-ordered
                val `α well-ordered` = have(wellOrder(α)(membershipRelation(α))) by Tautology.from(
                  ordinal.definition,
                  `α is ordinal`
                )

                // B ∩ α ⊆ α
                val `B∩α ⊆ α` = have((B ∩ α) ⊆ α) by Weakening(Intersection.subsetRight of (x := B, y := α))

                // ∃δ, minimal(δ)(B ∩ α)(membershipRelation(α))
                val minExists = have(∃(δ, minimal(δ)(B ∩ α)(membershipRelation(α)))) by Tautology.from(
                  WellOrder.minimalElement of (A := α, < := membershipRelation(α), B := (B ∩ α)),
                  `α well-ordered`,
                  `B∩α ⊆ α`
                )

                // From the minimal element δ, show the thesis
                have((δ ∈ (B ∩ α), minimal(δ)(B ∩ α)(membershipRelation(α))) |- ∃(α, α ∈ B /\ ∀(β, β ∈ B ==> (α <= β)))) subproof {
                  assume(δ ∈ (B ∩ α))
                  assume(minimal(δ)(B ∩ α)(membershipRelation(α)))

                  val `δ ∈ α` = have(δ ∈ α) by Tautology.from(
                    Intersection.membership of (z := δ, x := B, y := α)
                  )
                  val `δ ∈ B` = have(δ ∈ B) by Tautology.from(
                    Intersection.membership of (z := δ, x := B, y := α)
                  )
                  val `δ is ordinal` = have(ordinal(δ)) by Tautology.from(
                    elementOfOrdinal of (β := δ),
                    `α is ordinal`,
                    `δ ∈ α`
                  )

                  // Minimality: ∀z ∈ B ∩ α, (z, δ) ∉ ∈_α, i.e., ¬(z ∈ δ)
                  have(∀(z, z ∈ (B ∩ α) ==> ¬(pair(z)(δ) ∈ membershipRelation(α)))) by Tautology.from(
                    minimal.definition of (a := δ, A := (B ∩ α), < := membershipRelation(α))
                  )
                  thenHave(γ ∈ (B ∩ α) ==> ¬(pair(γ)(δ) ∈ membershipRelation(α))) by InstantiateForall(γ)
                  val minimality = thenHave(γ ∈ (B ∩ α) ==> ¬((γ ∈ α) /\ (δ ∈ α) /\ (γ ∈ δ))) by Tautology.fromLastStep(
                    MembershipRelation.membership of (x := γ, y := δ, A := α)
                  )
                  val minSimple = have(γ ∈ (B ∩ α) ==> ¬(γ ∈ δ)) by Tautology.from(
                    minimality,
                    Intersection.membership of (z := γ, x := B, y := α),
                    `δ ∈ α`
                  )

                  // Show ∀γ ∈ B, δ ≤ γ
                  have(γ ∈ B |- (δ <= γ)) subproof {
                    assume(γ ∈ B)
                    val `γ ordinal` = have(ordinal(γ)) by Tautology.from(`α ordinal from B` of (α := γ))

                    // Sub-case 2a: γ ∈ α
                    val caseInAlpha = have(γ ∈ α |- (δ <= γ)) subproof {
                      assume(γ ∈ α)
                      have(γ ∈ (B ∩ α)) by Tautology.from(Intersection.membership of (z := γ, x := B, y := α))
                      have(¬(γ ∈ δ)) by Tautology.from(lastStep, minSimple)
                      have(thesis) by Tautology.from(
                        lastStep,
                        comparability of (α := δ, β := γ),
                        `δ is ordinal`,
                        `γ ordinal`
                      )
                    }

                    // Sub-case 2b: γ ∉ α
                    val caseNotInAlpha = have(¬(γ ∈ α) |- (δ <= γ)) subproof {
                      assume(¬(γ ∈ α))
                      val alphaLeGamma = have((α ∈ γ) \/ (α === γ)) by Tautology.from(
                        comparability of (β := γ),
                        `α is ordinal`,
                        `γ ordinal`
                      )
                      // If α ∈ γ: δ ∈ α and α ∈ γ, γ transitive → δ ∈ γ
                      val subcase1 = have(α ∈ γ |- (δ ∈ γ)) by Tautology.from(
                        Ordinal.transitivity of (α := δ, β := α, γ := γ),
                        `γ ordinal`,
                        `δ ∈ α`
                      )
                      // If α = γ: δ ∈ α = γ → δ ∈ γ
                      val subcase2 = have((α === γ) |- (δ ∈ γ)) subproof {
                        assume(α === γ)
                        have(thesis) by Congruence.from(lastStep, `δ ∈ α`)
                      }
                      have(δ ∈ γ) by Tautology.from(alphaLeGamma, subcase1, subcase2)
                      thenHave(thesis) by Tautology.fromLastStep()
                    }

                    have(thesis) by Tautology.from(caseInAlpha, caseNotInAlpha)
                  }
                  thenHave(γ ∈ B ==> (δ <= γ)) by Restate
                  thenHave(∀(γ, γ ∈ B ==> (δ <= γ))) by RightForall

                  have(δ ∈ B /\ ∀(γ, γ ∈ B ==> (δ <= γ))) by Tautology.from(lastStep, `δ ∈ B`)
                  thenHave(∃(α, α ∈ B /\ ∀(β, β ∈ B ==> (α <= β)))) by RightExists
                }

                // Unpack the ∃δ, minimal(δ)... and connect
                have(minimal(δ)(B ∩ α)(membershipRelation(α)) |- ∃(α, α ∈ B /\ ∀(β, β ∈ B ==> (α <= β)))) by Tautology.from(
                  lastStep,
                  minimal.definition of (a := δ, A := (B ∩ α), < := membershipRelation(α))
                )
                val fromMinimal = thenHave(∃(δ, minimal(δ)(B ∩ α)(membershipRelation(α))) |- ∃(α, α ∈ B /\ ∀(β, β ∈ B ==> (α <= β)))) by LeftExists

                have(thesis) by Cut(minExists, fromMinimal)
              }

              // Combine cases: for any α ∈ B, thesis holds (either case 1 or case 2)
              have(α ∈ B |- ∃(α, α ∈ B /\ ∀(β, β ∈ B ==> (α <= β)))) by Tautology.from(case1, case2)
              val fromAnyAlpha = thenHave(∃(α, α ∈ B) |- ∃(α, α ∈ B /\ ∀(β, β ∈ B ==> (α <= β)))) by LeftExists

              // B ≠ ∅ → ∃α, α ∈ B
              have(∃(α, α ∈ B)) by Tautology.from(EmptySet.nonEmptyHasElement of (x := B))
              have(thesis) by Cut(lastStep, fromAnyAlpha)
            }

            // We now replace `α <= β` by `(β, α) ∉ membershipRelation(A)`
            have((α ∈ B, β ∈ B, α <= β) |- (β, α) ∉ membershipRelation(A)) by Tautology.from(
              MembershipRelation.membership of (x := β, y := α),
              asymmetry of (α := β, β := α),
              `α ∈ B`,
              `α ∈ B` of (α := β)
            )
            thenHave((α ∈ B, β ∈ B ==> α <= β) |- β ∈ B ==> (β, α) ∉ membershipRelation(A)) by Tautology
            thenHave((α ∈ B, ∀(β, β ∈ B ==> α <= β)) |- β ∈ B ==> (β, α) ∉ membershipRelation(A)) by LeftForall
            thenHave((α ∈ B, ∀(β, β ∈ B ==> α <= β)) |- ∀(β, β ∈ B ==> (β, α) ∉ membershipRelation(A))) by RightForall
            thenHave((α ∈ B /\ ∀(β, β ∈ B ==> α <= β)) |- α ∈ B /\ ∀(β, β ∈ B ==> (β, α) ∉ membershipRelation(A))) by Tautology
            thenHave((α ∈ B /\ ∀(β, β ∈ B ==> α <= β)) |- ∃(α, α ∈ B /\ ∀(β, β ∈ B ==> (β, α) ∉ membershipRelation(A)))) by RightExists
            thenHave(∃(α, α ∈ B /\ ∀(β, β ∈ B ==> α <= β)) |- ∃(α, α ∈ B /\ ∀(β, β ∈ B ==> (β, α) ∉ membershipRelation(A)))) by LeftExists

            val unfoldedExists = have(∃(α, α ∈ B /\ ∀(β, β ∈ B ==> (β, α) ∉ membershipRelation(A)))) by Cut(minimalElement, lastStep)

            // Now fold back: α ∈ B ∧ ∀(β, β ∈ B → ¬((β,α) ∈ ∈_A)) is exactly minimal(α)(B)(∈_A)
            val minDef = have(minimal(α)(B)(membershipRelation(A)) <=> (α ∈ B /\ ∀(x, x ∈ B ==> ¬(pair(x)(α) ∈ membershipRelation(A))))) by Tautology.from(
              minimal.definition of (a := α, A := B, < := membershipRelation(A))
            )
            have((α ∈ B /\ ∀(β, β ∈ B ==> (β, α) ∉ membershipRelation(A))) |- minimal(α)(B)(membershipRelation(A))) by Tautology.from(minDef)
            thenHave((α ∈ B /\ ∀(β, β ∈ B ==> (β, α) ∉ membershipRelation(A))) |- ∃(a, minimal(a)(B)(membershipRelation(A)))) by RightExists
            val foldStep = thenHave(∃(α, α ∈ B /\ ∀(β, β ∈ B ==> (β, α) ∉ membershipRelation(A))) |- ∃(a, minimal(a)(B)(membershipRelation(A)))) by LeftExists

            have(thesis) by Cut(unfoldedExists, foldStep)
          }
          thenHave((B ⊆ A) /\ (B ≠ ∅) ==> ∃(a, minimal(a)(B)(membershipRelation(A)))) by Restate
          thenHave(∀(B, (B ⊆ A) /\ (B ≠ ∅) ==> ∃(a, minimal(a)(B)(membershipRelation(A))))) by Generalize
          thenHave(wellFounded(membershipRelation(A))(A)) by Substitute(
            wellFounded.definition of (R := membershipRelation(A), X := A)
          )
        }

        have(thesis) by Tautology.from(
          wellOrder.definition of (< := membershipRelation(A)),
          strictTotalOrder.definition of (< := membershipRelation(A)),
          strictPartialOrder.definition of (< := membershipRelation(A)),
          Relations.BasicTheorems.relationOnIsRelation of (R := membershipRelation(A), X := A),
          MembershipRelation.isRelation,
          transitivity,
          irreflexivity,
          totality,
          wellFoundedness
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
    assume(ordinal(α))

    val Sα = S(α)

    // ==========================================
    // Part 1: transitiveSet(S(α))
    // ==========================================

    val `S(α) is transitive` = have(transitiveSet(Sα)) subproof {
      // Show: x ∈ y ∧ y ∈ S(α) → x ∈ S(α)
      // y ∈ S(α) means y ≤ α, i.e. y ∈ α ∨ y = α.
      // In either case, x ∈ y implies x ∈ α, hence x ∈ S(α).
      have((x ∈ y, y ∈ Sα) |- x ∈ Sα) subproof {
        assume(x ∈ y)
        assume(y ∈ Sα)

        // y ∈ S(α) <=> y ≤ α, i.e. y ∈ α ∨ y = α
        val `y ≤ α` = have(y ∈ α \/ (y === α)) by Tautology.from(successorMembership of (β := y))

        // If y ∈ α: by transitiveSet(α), y ⊆ α, so x ∈ y → x ∈ α
        // If y = α: x ∈ y = x ∈ α
        // In both cases x ∈ α.
        have((y ∈ α) |- x ∈ α) by Tautology.from(
          ordinal.definition,
          TransitiveSet.transitivity of (A := α)
        )
        val `x ∈ α from y ∈ α` = thenHave((y ∈ α) |- x ∈ Sα) by Tautology.fromLastStep(successorMembership of (β := x))

        have((y === α) |- x ∈ α) by Congruence
        val `x ∈ α from y = α` = thenHave((y === α) |- x ∈ Sα) by Tautology.fromLastStep(successorMembership of (β := x))

        have(thesis) by Tautology.from(`y ≤ α`, `x ∈ α from y ∈ α`, `x ∈ α from y = α`)
      }
      thenHave((x ∈ y) /\ (y ∈ Sα) ==> x ∈ Sα) by Restate
      thenHave(∀(x, ∀(y, (x ∈ y) /\ (y ∈ Sα) ==> x ∈ Sα))) by Generalize
      thenHave(thesis) by Tautology.fromLastStep(transitiveSet.definition of (A := Sα))
    }

    // ==========================================
    // Part 2: wellOrder(S(α))(∈_{S(α)})
    // ==========================================

    val `S(α) is well-ordered` = have(wellOrder(Sα)(membershipRelation(Sα))) subproof {

      // --- Irreflexivity ---
      val irreflexivity = have(irreflexive(membershipRelation(Sα))(Sα)) by Tautology.from(
        MembershipRelation.irreflexivity of (A := Sα)
      )

      // --- Transitivity ---
      // For x, y, z ∈ S(α) with x ∈ y and y ∈ z, show x ∈ z.
      val transitivity = have(transitive(membershipRelation(Sα))(Sα)) subproof {
        have((x ∈ y, y ∈ z, z ∈ Sα) |- x ∈ z) subproof {
          assume(x ∈ y)
          assume(y ∈ z)
          assume(z ∈ Sα)

          // z ∈ S(α) means z ≤ α
          val `z ≤ α` = have(z ∈ α \/ (z === α)) by Tautology.from(successorMembership of (β := z))

          // Case z ∈ α: y ∈ z ∈ α → y ∈ α (by transitivity of α), and x ∈ y ∈ α → x ∈ α.
          // Then x, y, z all ∈ α, so transitivity of ∈_α gives x ∈ z.
          have(z ∈ α |- x ∈ z) subproof {
            assume(z ∈ α)
            val `y ∈ α` = have(y ∈ α) by Tautology.from(Ordinal.transitivity of (α := y, β := z, γ := α))
            val `x ∈ α` = have(x ∈ α) by Tautology.from(`y ∈ α`, Ordinal.transitivity of (α := x, β := y, γ := α))

            val `x ∈_α y` = have((x, y) ∈ membershipRelation(α)) by Tautology.from(MembershipRelation.membership of (A := α), `x ∈ α`, `y ∈ α`)
            val `y ∈_α z` = have((y, z) ∈ membershipRelation(α)) by Tautology.from(MembershipRelation.membership of (x := y, y := z, A := α), `y ∈ α`)

            have((x, z) ∈ membershipRelation(α)) by Tautology.from(
              transitiveMembershipRelation,
              Relations.BasicTheorems.appliedTransitivity of (R := membershipRelation(α), X := α),
              `x ∈ α`,
              `y ∈ α`,
              `x ∈_α y`,
              `y ∈_α z`
            )
            thenHave(thesis) by Tautology.fromLastStep(MembershipRelation.membership of (y := z, A := α))
          }
          val caseZinAlpha = lastStep

          // Case z = α: y ∈ z = y ∈ α. Since transitiveSet(α), y ⊆ α, so x ∈ y → x ∈ α = z.
          have((z === α) |- x ∈ z) subproof {
            assume(z === α)
            have(y ∈ α) by Congruence
            thenHave(x ∈ α) by Tautology.fromLastStep(
              ordinal.definition,
              TransitiveSet.transitivity of (A := α)
            )
            thenHave(thesis) by Congruence
          }
          val caseZeqAlpha = lastStep

          have(thesis) by Tautology.from(`z ≤ α`, caseZinAlpha, caseZeqAlpha)
        }
        // Convert to ∈_{S(α)} form
        thenHave((x ∈ Sα, y ∈ Sα, z ∈ Sα) |- (x, y) ∈ membershipRelation(Sα) /\ ((y, z) ∈ membershipRelation(Sα)) ==> (x, z) ∈ membershipRelation(Sα)) by Tautology.fromLastStep(
          MembershipRelation.membership of (A := Sα),
          MembershipRelation.membership of (x := y, y := z, A := Sα),
          MembershipRelation.membership of (y := z, A := Sα)
        )
        thenHave((x ∈ Sα) /\ (y ∈ Sα) /\ (z ∈ Sα) /\ (x, y) ∈ membershipRelation(Sα) /\ ((y, z) ∈ membershipRelation(Sα)) ==> (x, z) ∈ membershipRelation(Sα)) by Tautology
        thenHave(∀(x, ∀(y, ∀(z, (x ∈ Sα) /\ (y ∈ Sα) /\ (z ∈ Sα) /\ (x, y) ∈ membershipRelation(Sα) /\ ((y, z) ∈ membershipRelation(Sα)) ==> (x, z) ∈ membershipRelation(Sα))))) by Generalize
        thenHave(∀(x ∈ Sα, ∀(y ∈ Sα, ∀(z ∈ Sα, (x, y) ∈ membershipRelation(Sα) /\ ((y, z) ∈ membershipRelation(Sα)) ==> (x, z) ∈ membershipRelation(Sα))))) by Tableau
        thenHave(thesis) by Substitute(transitive.definition of (R := membershipRelation(Sα), X := Sα))
      }

      // --- Totality ---
      // For x, y ∈ S(α), show (x,y) ∈ ∈_{S(α)} ∨ (y,x) ∈ ∈_{S(α)} ∨ x = y.
      val totality = have(total(membershipRelation(Sα))(Sα)) subproof {
        have((x ∈ Sα, y ∈ Sα) |- (x ∈ y) \/ (y ∈ x) \/ (x === y)) subproof {
          assume(x ∈ Sα)
          assume(y ∈ Sα)

          val `x ≤ α` = have(x ∈ α \/ (x === α)) by Tautology.from(successorMembership of (β := x))
          val `y ≤ α` = have(y ∈ α \/ (y === α)) by Tautology.from(successorMembership of (β := y))

          // Case x ∈ α, y ∈ α: by totality of ∈_α on α
          have((x ∈ α, y ∈ α) |- (x ∈ y) \/ (y ∈ x) \/ (x === y)) by Tautology.from(
            ordinal.definition,
            WellOrder.totality of (< := membershipRelation(α), A := α),
            Relations.BasicTheorems.appliedTotality of (R := membershipRelation(α), X := α),
            MembershipRelation.membership of (A := α),
            MembershipRelation.membership of (x := y, y := x, A := α)
          )
          val caseXinYin = lastStep

          // Case x ∈ α, y = α: x ∈ α = y
          have((x ∈ α, y === α) |- x ∈ y) by Congruence
          val caseXinYeq = lastStep

          // Case x = α, y ∈ α: y ∈ α = x
          have((x === α, y ∈ α) |- y ∈ x) by Congruence
          val caseXeqYin = lastStep

          // Case x = α, y = α: x = y
          have((x === α, y === α) |- x === y) by Congruence
          val caseXeqYeq = lastStep

          have(thesis) by Tautology.from(`x ≤ α`, `y ≤ α`, caseXinYin, caseXinYeq, caseXeqYin, caseXeqYeq)
        }
        thenHave((x ∈ Sα) /\ (y ∈ Sα) ==> ((x, y) ∈ membershipRelation(Sα) \/ ((y, x) ∈ membershipRelation(Sα)) \/ (x === y))) by Tautology.fromLastStep(
          MembershipRelation.membership of (A := Sα),
          MembershipRelation.membership of (x := y, y := x, A := Sα)
        )
        thenHave(∀(x, ∀(y, (x ∈ Sα) /\ (y ∈ Sα) ==> ((x, y) ∈ membershipRelation(Sα) \/ ((y, x) ∈ membershipRelation(Sα)) \/ (x === y))))) by Generalize
        thenHave(∀(x ∈ Sα, ∀(y ∈ Sα, ((x, y) ∈ membershipRelation(Sα) \/ ((y, x) ∈ membershipRelation(Sα)) \/ (x === y))))) by Tableau
        thenHave(thesis) by Substitute(total.definition of (R := membershipRelation(Sα), X := Sα))
      }

      // --- Well-foundedness ---
      // Use the Foundation Axiom: every non-empty set has an ∈-minimal element.
      val wellFoundedness = {
        have((B ⊆ Sα) /\ (B ≠ ∅) ==> ∃(x, minimal(x)(B)(membershipRelation(Sα)))) subproof {
          assume(B ⊆ Sα)
          assume(B ≠ ∅)

          // By the Foundation Axiom, there exists m ∈ B such that ∀z ∈ B. z ∉ m.
          val foundation = have(∃(a, (a ∈ B) /\ ∀(z, z ∈ B ==> z ∉ a))) by Tautology.from(
            axiomOfFoundation of (x := B)
          )

          // Show: if a ∈ B and ∀z ∈ B. z ∉ a, then minimal(a)(B)(∈_{S(α)})
          have((a ∈ B, ∀(z, z ∈ B ==> z ∉ a)) |- minimal(a)(B)(membershipRelation(Sα))) subproof {
            assume(a ∈ B)
            assume(∀(z, z ∈ B ==> z ∉ a))

            // ∀z. z ∈ B → z ∉ a
            have(∀(z, z ∈ B ==> z ∉ a)) by Restate
            thenHave(x ∈ B ==> x ∉ a) by InstantiateForall(x)
            // (x,a) ∈ ∈_{S(α)} → x ∈ a (by MembershipRelation.membership)
            // So z ∉ a → (z,a) ∉ ∈_{S(α)}
            thenHave(x ∈ B ==> ¬((x, a) ∈ membershipRelation(Sα))) by Tautology.fromLastStep(
              MembershipRelation.membership of (y := a, A := Sα)
            )
            thenHave(∀(x, x ∈ B ==> ¬((x, a) ∈ membershipRelation(Sα)))) by RightForall
            thenHave(a ∈ B /\ ∀(x, x ∈ B ==> ¬((x, a) ∈ membershipRelation(Sα)))) by Tautology
            thenHave(thesis) by Substitute(minimal.definition of (< := membershipRelation(Sα), A := B))
          }
          val minimalFromFoundation = lastStep
          thenHave((a ∈ B, ∀(z, z ∈ B ==> z ∉ a)) |- ∃(x, minimal(x)(B)(membershipRelation(Sα)))) by RightExists
          thenHave((a ∈ B) /\ ∀(z, z ∈ B ==> z ∉ a) |- ∃(x, minimal(x)(B)(membershipRelation(Sα)))) by Restate
          thenHave(∃(a, (a ∈ B) /\ ∀(z, z ∈ B ==> z ∉ a)) |- ∃(x, minimal(x)(B)(membershipRelation(Sα)))) by LeftExists

          have(thesis) by Tautology.from(lastStep, foundation)
        }
        thenHave(∀(B, (B ⊆ Sα) /\ (B ≠ ∅) ==> ∃(x, minimal(x)(B)(membershipRelation(Sα))))) by RightForall
        thenHave(wellFounded(membershipRelation(Sα))(Sα)) by Substitute(wellFounded.definition of (R := membershipRelation(Sα), X := Sα))
      }

      // --- Conclude ---
      have(thesis) by Tautology.from(
        MembershipRelation.isRelation of (A := Sα),
        Relations.BasicTheorems.relationOnIsRelation of (R := membershipRelation(Sα), X := Sα),
        transitivity,
        irreflexivity,
        totality,
        wellFoundedness,
        strictPartialOrder.definition of (A := Sα, < := membershipRelation(Sα)),
        strictTotalOrder.definition of (A := Sα, < := membershipRelation(Sα)),
        wellOrder.definition of (A := Sα, < := membershipRelation(Sα))
      )
    }

    // Conclude: ordinal(S(α))
    have(thesis) by Tautology.from(
      ordinal.definition of (α := Sα),
      `S(α) is transitive`,
      `S(α) is well-ordered`
    )
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
