package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Types.ADTv2.support.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.recursion.NatFacts.*
import lisa.maths.SetTheory.Types.ADTv2.support.UsefulTheorems.subsetIsNat
import lisa.maths.SetTheory.Types.ADTv2.support.ExtendedInteger.omegaOrdinal

import lisa.maths.SetTheory.Base.Pair.given
import lisa.maths.SetTheory.Base.{FoundationAxiom, Subset}
import lisa.maths.SetTheory.Order.Extrema.minimal
import lisa.maths.SetTheory.Order.Predef.*
import lisa.maths.SetTheory.Order.WellOrders.WellOrder
import lisa.maths.SetTheory.Ordinals.{Ordinal, TransitiveSet}
import lisa.maths.SetTheory.Ordinals.Ordinal.ordinal
import lisa.maths.SetTheory.Relations
import lisa.maths.SetTheory.Relations.Examples.MembershipRelation
import lisa.maths.SetTheory.Relations.Predef.*
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.BasicStepTactic.*

object OmegaFacts {

  private val X = variable[Ind]
  private val γ = variable[Ind]


  private val NTransitive = Theorem(TransitiveSet.transitiveSet(N)) {
    have((x ∈ y) /\ (y ∈ N) ==> (x ∈ N)) by Tautology
      .from(subsetIsNat of (x := x, y := y))
    thenHave(∀(x, ∀(y, ((x ∈ y) /\ (y ∈ N)) ==> (x ∈ N)))) by Generalize
    have(thesis) by Tautology
      .from(TransitiveSet.transitiveSet.definition of (A := N), lastStep)
  }


  private val isRelTransitive = Theorem(transitive(NatMem)(N)) {
    have(
      (x ∈ N, y ∈ N, z ∈ N) |- (
        (x, y) ∈ NatMem
      ) /\ ((y, z) ∈ NatMem) ==> ((x, z) ∈ NatMem)
    ) subproof {
      assume(x ∈ N)
      assume(y ∈ N)
      assume(z ∈ N)
      assume(((x, y) ∈ NatMem) /\ ((y, z) ∈ NatMem))

      val xy = have((x, y) ∈ NatMem) by Tautology
      val yz = have((y, z) ∈ NatMem) by Tautology
      val xInY = have(x ∈ y) by Tautology
        .from(xy, MembershipRelation.membership of (x := x, y := y, A := N))
      val yInZ = have(y ∈ z) by Tautology
        .from(yz, MembershipRelation.membership of (x := y, y := z, A := N))
      val ordZ = have(ordinal(z)) by Tautology
        .from(omegaOrdinal of (α := z))
      val xInZ = have(x ∈ z) by Tautology
        .from(ordZ, xInY, yInZ, Ordinal.transitivity of (α := x, β := y, γ := z))
      have((x, z) ∈ NatMem) by Tautology.from(
        xInZ,
        MembershipRelation.membership of (x := x, y := z, A := N),
        have(x ∈ N) by Tautology,
        have(z ∈ N) by Tautology
      )
      thenHave(thesis) by Tautology
    }
    thenHave(
      () |- ((x ∈ N) /\ (y ∈ N) /\ (z ∈ N) /\ ((x, y) ∈ NatMem) /\ (
        (y, z) ∈ NatMem
      ) ==> (x, z) ∈ NatMem)
    ) by Tableau
    thenHave(
      () |- ∀(
        z,
        (x ∈ N) /\ (y ∈ N) /\ (z ∈ N) /\ ((x, y) ∈ NatMem) /\ (
          (y, z) ∈ NatMem
        ) ==> (x, z) ∈ NatMem
      )
    ) by RightForall
    thenHave(
      () |- ∀(
        y,
        ∀(
          z,
          (x ∈ N) /\ (y ∈ N) /\ (z ∈ N) /\ ((x, y) ∈ NatMem) /\ (
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
            (x ∈ N) /\ (y ∈ N) /\ (z ∈ N) /\ ((x, y) ∈ NatMem) /\ (
              (y, z) ∈ NatMem
            ) ==> (x, z) ∈ NatMem
          )
        )
      )
    ) by RightForall
    thenHave(∀(
      x ∈ N,
      ∀(y ∈ N, ∀(z ∈ N, ((x, y) ∈ NatMem) /\ ((y, z) ∈ NatMem) ==> ((x, z) ∈ NatMem)))
    )) by Tableau
    have(thesis) by Tautology
      .from(transitive.definition of (R := NatMem, X := N), lastStep)
  }

  private val isRelTotal = Theorem(total(NatMem)(N)) {
    val goal = ((m, n) ∈ NatMem) \/ ((n, m) ∈ NatMem) \/ (m === n)

    have((m ∈ N, n ∈ N) |- goal) subproof {
      assume(m ∈ N)
      assume(n ∈ N)

      val cmp = have((m === n) \/ (m ∈ n) \/ (n ∈ m)) by Tautology.from(comparability)

      val mInRel = have(m ∈ n |- (m, n) ∈ NatMem) by Tautology.from(
        MembershipRelation.membership of (x := m, y := n, A := N),
        have(m ∈ N) by Tautology,
        have(n ∈ N) by Tautology
      )
      val nInRel = have(n ∈ m |- (n, m) ∈ NatMem) by Tautology.from(
        MembershipRelation.membership of (x := n, y := m, A := N),
        have(n ∈ N) by Tautology,
        have(m ∈ N) by Tautology
      )

      val caseEq = have(m === n |- goal) by Tautology
      val caseMn = have(m ∈ n |- goal) by Tautology.from(mInRel)
      val caseNm = have(n ∈ m |- goal) by Tautology.from(nInRel)

      have(thesis) by Tautology.from(cmp, caseEq, caseMn, caseNm)
    }
    thenHave(() |- ((m ∈ N) /\ (n ∈ N)) ==> goal) by Tableau
    thenHave(() |- ∀(n, ((m ∈ N) /\ (n ∈ N)) ==> goal)) by RightForall
    thenHave(() |- ∀(m, ∀(n, ((m ∈ N) /\ (n ∈ N)) ==> goal))) by RightForall
    thenHave(∀(m ∈ N, ∀(n ∈ N, goal))) by Tableau
    have(thesis) by Tautology.from(total.definition of (R := NatMem, X := N), lastStep)
  }

  private val isWellOrder = Theorem(WellOrder.wellOrder(N)(NatMem)) {
    val irreflexivity = have(irreflexive(NatMem)(N)) by Tautology
      .from(MembershipRelation.irreflexivity of (A := N))

    val wellFoundedness = have(wellFounded(NatMem)(N)) subproof {
      have((A ⊆ N) /\ (A =/= ∅) ==> ∃(a, minimal(a)(A)(NatMem))) subproof {
        assume((A ⊆ N) /\ (A =/= ∅))

        val foundation = have(∃(a, (a ∈ A) /\ ∀(x, x ∈ A ==> x ∉ a))) by Tautology
          .from(FoundationAxiom.axiomOfFoundation of (x := A))

        have((a ∈ A) /\ ∀(x, x ∈ A ==> x ∉ a) |- minimal(a)(A)(NatMem)) subproof {
          assume((a ∈ A) /\ ∀(x, x ∈ A ==> x ∉ a))
          val aInA = have(a ∈ A) by Tautology
          val aInNat = have(a ∈ N) by Tautology.from(
            aInA,
            Subset.membership of (x := A, y := N, z := a),
            have(A ⊆ N) by Tautology
          )

          have(∀(x, x ∈ A ==> ¬((x, a) ∈ NatMem))) subproof {
            val noMember = have(∀(x, x ∈ A ==> x ∉ a)) by Tautology
            have(x ∈ A ==> x ∉ a) by InstantiateForall(x)(noMember)
            val notMemRel = have((x ∈ A, (x, a) ∈ NatMem) |- ()) by Tautology.from(
              lastStep,
              MembershipRelation.membership of (x := x, y := a, A := N),
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
      thenHave(∀(A, (A ⊆ N) /\ (A =/= ∅) ==> ∃(a, minimal(a)(A)(NatMem)))) by RightForall
      have(thesis) by Tautology
        .from(wellFounded.definition of (R := NatMem, X := N), lastStep)
    }

    have(thesis) by Tautology.from(
      MembershipRelation.isRelation of (A := N),
      Relations.BasicTheorems.relationOnIsRelation of (R := NatMem, X := N),
      isRelTransitive,
      irreflexivity,
      isRelTotal,
      wellFoundedness,
      strictPartialOrder.definition of (A := N, < := NatMem),
      strictTotalOrder.definition of (A := N, < := NatMem),
      WellOrder.wellOrder.definition of (A := N, < := NatMem)
    )
  }

  val isOrdinal = Theorem(ordinal(N)) {
    have(thesis) by Tautology
      .from(NTransitive, isWellOrder, ordinal.definition of (α := N))
  }
}
