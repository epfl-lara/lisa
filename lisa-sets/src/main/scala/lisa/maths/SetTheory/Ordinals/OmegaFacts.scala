package lisa.maths.SetTheory.Ordinals

import lisa.maths.SetTheory.Base.FoundationAxiom
import lisa.maths.SetTheory.Base.Pair.given
import lisa.maths.SetTheory.Base.Subset
import lisa.maths.SetTheory.Order.Extrema.minimal
import lisa.maths.SetTheory.Order.Predef._
import lisa.maths.SetTheory.Order.WellOrders.WellOrder
import lisa.maths.SetTheory.Ordinals.Integer.omegaOrdinal
import lisa.maths.SetTheory.Ordinals.Integer.subsetIsNat
import lisa.maths.SetTheory.Ordinals.Integer.ω
import lisa.maths.SetTheory.Ordinals.Ordinal
import lisa.maths.SetTheory.Ordinals.Ordinal.ordinal
import lisa.maths.SetTheory.Ordinals.TransitiveSet
import lisa.maths.SetTheory.Relations
import lisa.maths.SetTheory.Relations.Examples.MembershipRelation
import lisa.maths.SetTheory.Relations.Predef._
import lisa.maths.SetTheory.SetTheory.{_, given}

/**
 * `ω` is an ordinal: it is a transitive set well-ordered by membership.
 */
object OmegaFacts {

  private val A = variable[Ind]
  private val X = variable[Ind]
  private val a = variable[Ind]
  private val α, β = variable[Ind]
  private val γ = variable[Ind]
  private val m, n = variable[Ind]
  private val x, y, z = variable[Ind]
  private val NatMem = MembershipRelation.membershipRelation(ω)


  private val NTransitive = Theorem(TransitiveSet.transitiveSet(ω)) {
    have((x ∈ y) /\ (y ∈ ω) ==> (x ∈ ω)) by Tautology
      .from(subsetIsNat of (x := x, y := y))
    thenHave(∀(x, ∀(y, ((x ∈ y) /\ (y ∈ ω)) ==> (x ∈ ω)))) by Generalize
    have(thesis) by Tautology
      .from(TransitiveSet.transitiveSet.definition of (A := ω), lastStep)
  }


  private val isRelTransitive = Theorem(transitive(NatMem)(ω)) {
    have(
      (x ∈ ω, y ∈ ω, z ∈ ω) |- (
        (x, y) ∈ NatMem
      ) /\ ((y, z) ∈ NatMem) ==> ((x, z) ∈ NatMem)
    ) subproof {
      assume(x ∈ ω)
      assume(y ∈ ω)
      assume(z ∈ ω)
      assume(((x, y) ∈ NatMem) /\ ((y, z) ∈ NatMem))

      val xy = have((x, y) ∈ NatMem) by Tautology
      val yz = have((y, z) ∈ NatMem) by Tautology
      val xInY = have(x ∈ y) by Tautology
        .from(xy, MembershipRelation.membership of (x := x, y := y, A := ω))
      val yInZ = have(y ∈ z) by Tautology
        .from(yz, MembershipRelation.membership of (x := y, y := z, A := ω))
      val ordZ = have(ordinal(z)) by Tautology
        .from(omegaOrdinal of (α := z))
      val xInZ = have(x ∈ z) by Tautology
        .from(ordZ, xInY, yInZ, Ordinal.transitivity of (α := x, β := y, γ := z))
      have((x, z) ∈ NatMem) by Tautology.from(
        xInZ,
        MembershipRelation.membership of (x := x, y := z, A := ω),
        have(x ∈ ω) by Tautology,
        have(z ∈ ω) by Tautology
      )
      thenHave(thesis) by Tautology
    }
    thenHave(
      () |- ((x ∈ ω) /\ (y ∈ ω) /\ (z ∈ ω) /\ ((x, y) ∈ NatMem) /\ (
        (y, z) ∈ NatMem
      ) ==> (x, z) ∈ NatMem)
    ) by Restate
    thenHave(
      () |- ∀(
        z,
        (x ∈ ω) /\ (y ∈ ω) /\ (z ∈ ω) /\ ((x, y) ∈ NatMem) /\ (
          (y, z) ∈ NatMem
        ) ==> (x, z) ∈ NatMem
      )
    ) by RightForall
    thenHave(
      () |- ∀(
        y,
        ∀(
          z,
          (x ∈ ω) /\ (y ∈ ω) /\ (z ∈ ω) /\ ((x, y) ∈ NatMem) /\ (
            (y, z) ∈ NatMem
          ) ==> (x, z) ∈ NatMem
        )
      )
    ) by RightForall
    thenHave(
      () |- ∀(
        x,
        ∀(
          y,
          ∀(
            z,
            (x ∈ ω) /\ (y ∈ ω) /\ (z ∈ ω) /\ ((x, y) ∈ NatMem) /\ (
              (y, z) ∈ NatMem
            ) ==> (x, z) ∈ NatMem
          )
        )
      )
    ) by RightForall
    thenHave(∀(
      x ∈ ω,
      ∀(y ∈ ω, ∀(z ∈ ω, ((x, y) ∈ NatMem) /\ ((y, z) ∈ NatMem) ==> ((x, z) ∈ NatMem)))
    )) by Tableau
    have(thesis) by Tautology
      .from(transitive.definition of (R := NatMem, X := ω), lastStep)
  }

  private val isRelTotal = Theorem(total(NatMem)(ω)) {
    val goal = ((m, n) ∈ NatMem) \/ ((n, m) ∈ NatMem) \/ (m === n)

    have((m ∈ ω, n ∈ ω) |- goal) subproof {
      assume(m ∈ ω)
      assume(n ∈ ω)

      val cmp = have((m === n) \/ (m ∈ n) \/ (n ∈ m)) by
        Tautology.from(Integer.comparability of (m := m, n := n))

      val mInRel = have(m ∈ n |- (m, n) ∈ NatMem) by Tautology.from(
        MembershipRelation.membership of (x := m, y := n, A := ω),
        have(m ∈ ω) by Tautology,
        have(n ∈ ω) by Tautology
      )
      val nInRel = have(n ∈ m |- (n, m) ∈ NatMem) by Tautology.from(
        MembershipRelation.membership of (x := n, y := m, A := ω),
        have(n ∈ ω) by Tautology,
        have(m ∈ ω) by Tautology
      )

      val caseEq = have(m === n |- goal) by Tautology
      val caseMn = have(m ∈ n |- goal) by Tautology.from(mInRel)
      val caseNm = have(n ∈ m |- goal) by Tautology.from(nInRel)

      have(thesis) by Tautology.from(cmp, caseEq, caseMn, caseNm)
    }
    thenHave(() |- ((m ∈ ω) /\ (n ∈ ω)) ==> goal) by Restate
    thenHave(() |- ∀(n, ((m ∈ ω) /\ (n ∈ ω)) ==> goal)) by RightForall
    thenHave(() |- ∀(m, ∀(n, ((m ∈ ω) /\ (n ∈ ω)) ==> goal))) by RightForall
    thenHave(∀(m ∈ ω, ∀(n ∈ ω, goal))) by Tableau
    have(thesis) by Tautology.from(total.definition of (R := NatMem, X := ω), lastStep)
  }

  private val isWellOrder = Theorem(WellOrder.wellOrder(ω)(NatMem)) {
    val irreflexivity = have(irreflexive(NatMem)(ω)) by Tautology
      .from(MembershipRelation.irreflexivity of (A := ω))

    val wellFoundedness = have(wellFounded(NatMem)(ω)) subproof {
      have((A ⊆ ω) /\ (A =/= ∅) ==> ∃(a, minimal(a)(A)(NatMem))) subproof {
        assume((A ⊆ ω) /\ (A =/= ∅))

        val foundation = have(∃(a, (a ∈ A) /\ ∀(x, x ∈ A ==> x ∉ a))) by Tautology
          .from(FoundationAxiom.axiomOfFoundation of (x := A))

        have((a ∈ A) /\ ∀(x, x ∈ A ==> x ∉ a) |- minimal(a)(A)(NatMem)) subproof {
          assume((a ∈ A) /\ ∀(x, x ∈ A ==> x ∉ a))
          val aInA = have(a ∈ A) by Tautology
          val aInNat = have(a ∈ ω) by Tautology.from(
            aInA,
            Subset.membership of (x := A, y := ω, z := a),
            have(A ⊆ ω) by Tautology
          )

          have(∀(x, x ∈ A ==> ¬((x, a) ∈ NatMem))) subproof {
            val noMember = have(∀(x, x ∈ A ==> x ∉ a)) by Tautology
            have(x ∈ A ==> x ∉ a) by InstantiateForall(x)(noMember)
            val notMemRel = have((x ∈ A, (x, a) ∈ NatMem) |- ()) by Tautology.from(
              lastStep,
              MembershipRelation.membership of (x := x, y := a, A := ω),
              aInNat
            )
            have(x ∈ A ==> ¬((x, a) ∈ NatMem)) by Tautology.from(notMemRel)
            thenHave(thesis) by RightForall
          }

          have(thesis) by Tautology
            .from(minimal.definition of (a := a, A := A, < := NatMem), aInA, lastStep)
        }
        thenHave(
          (a ∈ A) /\ ∀(x, x ∈ A ==> x ∉ a) |- ∃(a, minimal(a)(A)(NatMem))
        ) by RightExists
        thenHave(
          ∃(a, (a ∈ A) /\ ∀(x, x ∈ A ==> x ∉ a)) |- ∃(a, minimal(a)(A)(NatMem))
        ) by LeftExists

        have(thesis) by Tautology.from(foundation, lastStep)
      }
      thenHave(∀(A, (A ⊆ ω) /\ (A =/= ∅) ==> ∃(a, minimal(a)(A)(NatMem)))) by RightForall
      have(thesis) by Tautology
        .from(wellFounded.definition of (R := NatMem, X := ω), lastStep)
    }

    have(thesis) by Tautology.from(
      MembershipRelation.isRelation of (A := ω),
      Relations.BasicTheorems.relationOnIsRelation of (R := NatMem, X := ω),
      isRelTransitive,
      irreflexivity,
      isRelTotal,
      wellFoundedness,
      strictPartialOrder.definition of (A := ω, < := NatMem),
      strictTotalOrder.definition of (A := ω, < := NatMem),
      WellOrder.wellOrder.definition of (A := ω, < := NatMem)
    )
  }

  val isOrdinal = Theorem(ordinal(ω)) {
    have(thesis) by Tautology
      .from(NTransitive, isWellOrder, ordinal.definition of (α := ω))
  }
}
