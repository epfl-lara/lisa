package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Types.ADTv2.support.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.UsefulTheorems.{
  nInSuccN,
  natInduction,
  subsetIsNat,
  successorIsNat,
  zeroIsNotSucc
}
import lisa.maths.SetTheory.Types.ADTv2.support.ExtendedInteger.{
  integerIsOrdinal,
  omegaCharacterization
}

import lisa.maths.SetTheory.Base.Extensionality
import lisa.maths.SetTheory.Base.Pair.given
import lisa.maths.SetTheory.Base.Union.∪
import lisa.maths.SetTheory.Base.{EmptySet, FoundationAxiom, Singleton, Subset, Union}
import lisa.maths.SetTheory.Order.Extrema.minimal
import lisa.maths.SetTheory.Order.Predef.*
import lisa.maths.SetTheory.Order.WellOrders.WellOrder
import lisa.maths.SetTheory.Ordinals.{Ordinal, TransitiveSet}
import lisa.maths.SetTheory.Ordinals.Ordinal.{ordinal, S}
import lisa.maths.SetTheory.Relations
import lisa.maths.SetTheory.Relations.Examples.MembershipRelation
import lisa.maths.SetTheory.Relations.Predef.*
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.BasicStepTactic.*

object Nums {

  private val Pred = variable[Ind >>: Prop]
  private val X = variable[Ind]
  private val γ = variable[Ind]

  val Zero = DEF(∅)
  val Succ = DEF(λ(x, successor(x)))
  val NatMem = MembershipRelation.membershipRelation(N)

  private val elementIsOrdinal = Lemma(n ∈ N |- ordinal(n)) {
    have(n ∈ N <=> lisa.maths.SetTheory.Ordinals.Integer.integer(n)) by
      InstantiateForall(n)(omegaCharacterization)
    have(thesis) by Tautology.from(lastStep, integerIsOrdinal of (α := n))
  }

  val succIntro = Theorem(n ∈ N |- Succ(n) ∈ N) {
    assume(n ∈ N)
    val succInNat = have(successor(n) ∈ N) by Tautology.from(successorIsNat of (n := n))
    val succEq = have(Succ(n) === successor(n)) by Tautology
      .from(Succ.definition of (x := n))
    have(thesis) by Congruence.from(succInNat, succEq)
  }

  val induction = Theorem(
    (Pred(Zero), ∀(n, (n ∈ N) ==> (Pred(n) ==> Pred(Succ(n))))) |-
      ∀(n, (n ∈ N) ==> Pred(n))
  ) {
    val H0 = Pred(Zero)
    val Hstep = ∀(n, (n ∈ N) ==> (Pred(n) ==> Pred(Succ(n))))

    val baseAtEmpty = have((H0, Hstep) |- Pred(∅)) subproof {
      val hyp0 = have((H0, Hstep) |- H0) by Hypothesis
      val zeroEq = have(Zero === ∅) by Tautology.from(Zero.definition)
      have(thesis) by Congruence.from(hyp0, zeroEq)
    }

    val stepAtSucc =
      have((H0, Hstep) |- ∀(n, (n ∈ N) ==> (Pred(n) ==> Pred(successor(n))))) subproof {
        val hypStep = have((H0, Hstep) |- Hstep) by Hypothesis
        val stepAtN = have((H0, Hstep) |- (n ∈ N) ==> (Pred(n) ==> Pred(Succ(n)))) by
          InstantiateForall(n)(hypStep)
        have((H0, Hstep) |- (n ∈ N) ==> (Pred(n) ==> Pred(successor(n)))) subproof {
          assume(n ∈ N)
          assume(Pred(n))
          val predSucc = have((H0, Hstep, n ∈ N, Pred(n)) |- Pred(Succ(n))) by
            Tautology.from(stepAtN)
          val succEq = have(Succ(n) === successor(n)) by Tautology
            .from(Succ.definition of (x := n))
          have((H0, Hstep, n ∈ N, Pred(n)) |- Pred(successor(n))) by
            Congruence.from(predSucc, succEq)
        }
        thenHave(thesis) by RightForall
      }

    have((H0, Hstep) |- ∀(n, (n ∈ N) ==> Pred(n))) by Tautology
      .from(natInduction of (P := Pred), baseAtEmpty, stepAtSucc)
    thenHave(thesis) by Restate
  }

  val succMembership = Theorem((k ∈ Succ(n)) <=> (k ∈ n) \/ (k === n)) {
    val succDef = have(Succ(n) === successor(n)) by
      Tautology.from(Succ.definition of (x := n))
    val memSucc = have(k ∈ Succ(n) <=> (k ∈ n) \/ (k === n)) by Tautology.from(
      have(k ∈ Succ(n) <=> k ∈ successor(n)) by Congruence.from(succDef),
      have(k ∈ successor(n) <=> (k ∈ n) \/ (k === n)) by Tautology.from(
        have(k ∈ successor(n) <=> k ∈ (n ∪ Singleton.singleton(n))) by
          Congruence.from(successor.definition of (x := n)),
        have(
          k ∈ (n ∪ Singleton.singleton(n)) <=> (k ∈ n) \/ (k ∈ Singleton.singleton(n))
        ) by
          Tautology
            .from(Union.membership of (x := n, y := Singleton.singleton(n), z := k)),
        have(k ∈ Singleton.singleton(n) <=> (k === n)) by
          Tautology.from(Singleton.membership of (x := n, y := k))
      )
    )
    have(thesis) by Restate.from(memSucc)
  }

  val nInSucc = Theorem(n ∈ Succ(n)) {
    val mem = have(n ∈ Succ(n) <=> (n ∈ n) \/ (n === n)) by
      Restate.from(succMembership of (k := n, n := n))
    val refl = have(n === n) by Restate
    have(thesis) by Tautology.from(mem, refl)
  }

  val NTransitive = Theorem(TransitiveSet.transitiveSet(N)) {
    have((x ∈ y) /\ (y ∈ N) ==> (x ∈ N)) by Tautology
      .from(subsetIsNat of (x := x, y := y))
    thenHave(∀(x, ∀(y, ((x ∈ y) /\ (y ∈ N)) ==> (x ∈ N)))) by Generalize
    have(thesis) by Tautology
      .from(TransitiveSet.transitiveSet.definition of (A := N), lastStep)
  }

  val elementsTransitive = Theorem((n ∈ N) |- TransitiveSet.transitiveSet(n)) {
    val ordN = have(n ∈ N |- ordinal(n)) by Restate.from(elementIsOrdinal)
    have(thesis) by Tautology.from(ordN, ordinal.definition of (α := n))
  }

  val succNeZero = Lemma((n ∈ N) |- (Succ(n) =/= Zero)) {
    assume(n ∈ N)
    val succNeEmpty = have(Succ(n) =/= ∅) by Congruence
      .from(zeroIsNotSucc of (n := n), Succ.definition of (x := n))
    val zeroEq = have(Zero === ∅) by Tautology.from(Zero.definition)
    have(thesis) by Congruence.from(succNeEmpty, zeroEq)
  }

  val comparability = Theorem((m ∈ N, n ∈ N) |- (m === n) \/ (m ∈ n) \/ (n ∈ m)) {
    val mOrd = have(m ∈ N |- ordinal(m)) by Restate.from(elementIsOrdinal of (n := m))
    val nOrd = have(n ∈ N |- ordinal(n)) by Restate.from(elementIsOrdinal of (n := n))
    have(thesis) by Tautology.from(mOrd, nOrd, Ordinal.comparability of (α := m, β := n))
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
        .from(have(z ∈ N) by Tautology, elementIsOrdinal of (n := z))
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

  val isWellOrder = Theorem(WellOrder.wellOrder(N)(NatMem)) {
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
