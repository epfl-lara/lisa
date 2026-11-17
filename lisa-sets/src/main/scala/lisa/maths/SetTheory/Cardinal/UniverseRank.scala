package lisa.maths.SetTheory.Cardinal

import lisa.maths.Quantifiers.existsEpsilon
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Order.Predef._
import lisa.maths.SetTheory.Order.WellOrders.WellOrder
import lisa.maths.SetTheory.Ordinals.Ordinal
import lisa.maths.SetTheory.Ordinals.Ordinal.comparability
import lisa.maths.SetTheory.Ordinals.Ordinal.elementOfOrdinal
import lisa.maths.SetTheory.Ordinals.Ordinal.ordinal
import lisa.maths.SetTheory.Ordinals.TransitiveSet
import lisa.maths.SetTheory.Relations.BasicTheorems
import lisa.maths.SetTheory.Relations.Examples.MembershipRelation
import lisa.maths.SetTheory.Relations.Predef._

import Universe._

object UniverseRank extends lisa.Main:
  private val x, y, z, k, a, S = variable[Ind]
  private val α, β, γ = variable[Ind]
  private val U, U1, U2 = variable[Ind]

  /**
   * Von Neumann hierarchy
   */
  val V = constant[Ind >>: Ind]

  /**
   * The Level (or Rank) of a Universe.
   * If U = V_k, then level(U) = k.
   * Implementation: level(U) is the set of all ordinals contained in U.
   * Since U is transitive, this set is exactly the ordinal k.
   */
  val level = DEF(λ(U, ε(k, ∀(x, x ∈ k <=> (x ∈ U /\ ordinal(x))))))

  /**
   * Membership in the set of ordinals contained in U.
   */
  val levelMembership = Theorem(
    x ∈ level(U) <=> (x ∈ U /\ ordinal(x))
  ) {
    def property(k: Expr[Ind]) = ∀(x, x ∈ k <=> (x ∈ U /\ ordinal(x)))
    have(∃(k, property(k))) by Restate.from(comprehensionSchema of (y := U, φ := λ(x, ordinal(x))))
    thenHave(property(ε(k, property(k)))) by Tautology.fromLastStep(existsEpsilon of (x := k, P := λ(k, property(k))))
    thenHave(∀(x, x ∈ level(U) <=> (x ∈ U /\ ordinal(x)))) by Substitute(level.definition)
    thenHave(thesis) by InstantiateForall(x)
  }

  /**
   * The ordinals contained in a universe form an ordinal.
   */
  val levelIsOrdinal = Theorem(
    isUniverse(U) ==> ordinal(level(U))
  ) {
    assume(isUniverse(U))
    val L = level(U)
    val r = MembershipRelation.membershipRelation(L)

    val transitiveLevel = have(TransitiveSet.transitiveSet(L)) subproof {
      have((x ∈ y, y ∈ L) |- x ∈ L) subproof {
        assume(x ∈ y)
        assume(y ∈ L)
        val yOrdinal = have(ordinal(y)) by Tautology.from(levelMembership of (x := y))
        val yInU = have(y ∈ U) by Tautology.from(levelMembership of (x := y))
        val ySubsetU = have(y ⊆ U) by Tautology.from(yInU, universeTransitivity of (x := y))
        val xInU = have(x ∈ U) by Tautology.from(ySubsetU, Subset.membership of (x := y, y := U, z := x))
        val xOrdinal = have(ordinal(x)) by Tautology.from(yOrdinal, elementOfOrdinal of (α := y, β := x))
        have(thesis) by Tautology.from(xInU, xOrdinal, levelMembership)
      }
      thenHave(x ∈ y /\ (y ∈ L) ==> x ∈ L) by Restate
      thenHave(∀(x, ∀(y, x ∈ y /\ (y ∈ L) ==> x ∈ L))) by Generalize
      thenHave(thesis) by Substitute(TransitiveSet.transitiveSet.definition of (A := L))
    }

    val transitiveRelation = have(transitive(r)(L)) subproof {
      have((x ∈ L, y ∈ L, z ∈ L) |- ((x, y) ∈ r) /\ ((y, z) ∈ r) ==> ((x, z) ∈ r)) by Tautology.from(
        levelMembership of (x := z),
        Ordinal.transitivity of (α := x, β := y, γ := z),
        MembershipRelation.membership of (A := L),
        MembershipRelation.membership of (x := y, y := z, A := L),
        MembershipRelation.membership of (x := x, y := z, A := L)
      )
      val implication = (x ∈ L) ==> ((y ∈ L) ==> ((z ∈ L) ==> (((x, y) ∈ r) /\ ((y, z) ∈ r) ==> ((x, z) ∈ r))))
      thenHave(implication) by Restate
      thenHave(∀(x, ∀(y, ∀(z, implication)))) by Generalize
      thenHave(∀(x ∈ L, ∀(y ∈ L, ∀(z ∈ L, ((x, y) ∈ r) /\ ((y, z) ∈ r) ==> ((x, z) ∈ r))))) by Tableau
      thenHave(thesis) by Substitute(transitive.definition of (R := r, X := L))
    }

    val totalRelation = have(total(r)(L)) subproof {
      have((x ∈ L, y ∈ L) |- ((x, y) ∈ r) \/ ((y, x) ∈ r) \/ (x === y)) by Tautology.from(
        levelMembership,
        levelMembership of (x := y),
        comparability of (α := x, β := y),
        MembershipRelation.membership of (A := L),
        MembershipRelation.membership of (x := y, y := x, A := L)
      )
      val implication = (x ∈ L) ==> ((y ∈ L) ==> (((x, y) ∈ r) \/ ((y, x) ∈ r) \/ (x === y)))
      thenHave(implication) by Restate
      thenHave(∀(x, ∀(y, implication))) by Generalize
      thenHave(∀(x ∈ L, ∀(y ∈ L, ((x, y) ∈ r) \/ ((y, x) ∈ r) \/ (x === y)))) by Tableau
      thenHave(thesis) by Substitute(total.definition of (R := r, X := L))
    }

    val foundedRelation = have(wellFounded(r)(L)) subproof {
      have((S ⊆ L, S ≠ ∅) |- ∃(a, minimal(a)(S)(r))) subproof {
        assume(S ⊆ L)
        assume(S ≠ ∅)
        val foundation = have(∃(a, a ∈ S /\ ∀(x, x ∈ S ==> x ∉ a))) by Tautology.from(axiomOfFoundation of (x := S))
        have((a ∈ S, ∀(x, x ∈ S ==> x ∉ a)) |- minimal(a)(S)(r)) subproof {
          assume(a ∈ S)
          assume(∀(x, x ∈ S ==> x ∉ a))
          thenHave(x ∈ S ==> x ∉ a) by InstantiateForall(x)
          thenHave(x ∈ S ==> (x, a) ∉ r) by Tautology.fromLastStep(MembershipRelation.membership of (x := x, y := a, A := L))
          thenHave(∀(x, x ∈ S ==> (x, a) ∉ r)) by RightForall
          thenHave(a ∈ S /\ ∀(x, x ∈ S ==> (x, a) ∉ r)) by Tautology
          thenHave(thesis) by Substitute(minimal.definition of (a := a, A := S, < := r))
        }
        thenHave((a ∈ S, ∀(x, x ∈ S ==> x ∉ a)) |- ∃(a, minimal(a)(S)(r))) by RightExists
        thenHave(a ∈ S /\ ∀(x, x ∈ S ==> x ∉ a) |- ∃(a, minimal(a)(S)(r))) by Restate
        thenHave(∃(a, a ∈ S /\ ∀(x, x ∈ S ==> x ∉ a)) |- ∃(a, minimal(a)(S)(r))) by LeftExists
        have(thesis) by Cut(foundation, lastStep)
      }
      thenHave((S ⊆ L) /\ (S ≠ ∅) ==> ∃(a, minimal(a)(S)(r))) by Restate
      thenHave(∀(S, (S ⊆ L) /\ (S ≠ ∅) ==> ∃(a, minimal(a)(S)(r)))) by Generalize
      thenHave(thesis) by Substitute(wellFounded.definition of (R := r, X := L))
    }

    have(ordinal(L)) by Tautology.from(
      transitiveLevel,
      transitiveRelation,
      totalRelation,
      foundedRelation,
      MembershipRelation.irreflexivity of (A := L),
      MembershipRelation.isRelation of (A := L),
      BasicTheorems.relationOnIsRelation of (R := r, X := L),
      strictPartialOrder.definition of (A := L, < := r),
      strictTotalOrder.definition of (A := L, < := r),
      WellOrder.wellOrder.definition of (A := L, < := r),
      ordinal.definition of (α := L)
    )
    thenHave(thesis) by Restate
  }

  /**
   * Axiom: Universes are nested.
   * Based on the fact that universes correspond to V_k where k are cardinals,
   * and cardinals are totally ordered.
   */
  val universesAreNested = Theorem(
    (isUniverse(U1), isUniverse(U2)) |- (U1 ⊆ U2) \/ (U2 ⊆ U1)
  ) {
    sorry
  }
