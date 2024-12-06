package Topology

import lisa.maths.topology.Topology.*
import lisa.maths.settheory.SetTheory.*
import lisa.automation.kernel.CommonTactics.*
import lisa.maths.settheory.functions.Functionals.*
import lisa.automation.settheory.SetTheoryTactics.UniqueComprehension
import lisa.automation.settheory.SetTheoryTactics.TheConditional

object Instances extends lisa.Main {
  import lisa.maths.settheory.SetTheory.*
  // var defs
  private val x, z, X, T = variable
  private val S, A, B, a, b, c, Y = variable

  val discreteTopology = DEF(X, T) --> (T === powerSet(X))
  val indiscreteTopology = DEF(X, T) --> ∅ ∈ T /\ X ∈ T /\ forall(S, in(S, T) ==> ((S === X) \/ (S === ∅)))

  val discreteIsTopology = Theorem(
    discreteTopology(X, T) ==> topology(X, T)
  ) {
    sorry
  }

  private val f, y, s = variable
  inline def directImageFormula = y ∈ s <=> (y ∈ functionRange(f) /\ ∃(x, (app(f, x) === y) /\ x ∈ A))

  val directImageUniqueness = Theorem(
    (functional(f), subset(A, functionDomain(f))) |- ∃!(s, forall(y, directImageFormula))
  ) {
    have(∃!(s, forall(y, directImageFormula))) by UniqueComprehension(functionRange(f), lambda(y, ∃(x, (app(f, x) === y) /\ x ∈ A)))
    thenHave(thesis) by Weakening
  }

  val directImage = DEF(f, A) --> TheConditional(s, forall(y, directImageFormula))(directImageUniqueness)

  val directImageSetUnion = Theorem(
    functional(f) /\
      subset(A, functionDomain(f)) /\
      subset(B, functionDomain(f))
      |- setUnion(directImage(f, A), directImage(f, B)) === directImage(f, setUnion(A, B))
  ) {
    assume(
      functional(f) /\
        subset(A, functionDomain(f)) /\
        subset(B, functionDomain(f))
    )

    val subsetAorB = have(subset(setUnion(A, B), functionDomain(f))) by Tautology.from(unionOfTwoSubsets of (a := A, b := B, c := functionDomain(f)))

    have(forall(z, z ∈ directImage(f, A) <=> (z ∈ functionRange(f) /\ ∃(x, (app(f, x) === z) /\ x ∈ A)))) by InstantiateForall(directImage(f, A))(directImage.definition)
    val defA = thenHave(z ∈ directImage(f, A) <=> (z ∈ functionRange(f) /\ ∃(x, (app(f, x) === z) /\ x ∈ A))) by InstantiateForall(z)
    have(forall(z, z ∈ directImage(f, B) <=> (z ∈ functionRange(f) /\ ∃(x, (app(f, x) === z) /\ x ∈ B)))) by InstantiateForall(directImage(f, B))(directImage.definition of (A := B))
    val defB = thenHave(z ∈ directImage(f, B) <=> (z ∈ functionRange(f) /\ ∃(x, (app(f, x) === z) /\ x ∈ B))) by InstantiateForall(z)
    have(
      subset(setUnion(A, B), functionDomain(f)) |-
        forall(
          z,
          z ∈ directImage(f, setUnion(A, B)) <=>
            (z ∈ functionRange(f) /\ ∃(x, (app(f, x) === z) /\ x ∈ setUnion(A, B)))
        )
    ) by InstantiateForall(directImage(f, setUnion(A, B)))(directImage.definition of (A := setUnion(A, B)))
    thenHave(
      subset(setUnion(A, B), functionDomain(f)) |-
        z ∈ directImage(f, setUnion(A, B)) <=>
        (z ∈ functionRange(f) /\ ∃(x, (app(f, x) === z) /\ x ∈ setUnion(A, B)))
    ) by InstantiateForall(z)
    val defAorB = have(
      z ∈ directImage(f, setUnion(A, B)) <=>
        (z ∈ functionRange(f) /\ ∃(x, (app(f, x) === z) /\ x ∈ setUnion(A, B)))
    ) by Tautology.from(lastStep, subsetAorB)

    val forward = have(z ∈ setUnion(directImage(f, A), directImage(f, B)) ==> z ∈ directImage(f, setUnion(A, B))) subproof {
      val firstPart = have(z ∈ setUnion(directImage(f, A), directImage(f, B)) |- (z ∈ directImage(f, A)) \/ (z ∈ directImage(f, B))) by Tautology.from(
        setUnionMembership of (x := directImage(f, A), y := directImage(f, B))
      )
      assume(z ∈ setUnion(directImage(f, A), directImage(f, B)))
      have(z ∈ functionRange(f) /\ ((∃(x, (app(f, x) === z) /\ x ∈ A)) \/ ∃(x, (app(f, x) === z) /\ x ∈ B))) by Tautology.from(
        defA,
        defB,
        firstPart
      )
      val partialResult = thenHave(z ∈ functionRange(f) /\ (∃(x, (app(f, x) === z) /\ ((x ∈ A) \/ (x ∈ B))))) by Tautology
      have(
        (z ∈ functionRange(f), (app(f, x) === z) /\ ((x ∈ A) \/ (x ∈ B)))
          |-
            (app(f, x) === z) /\ x ∈ setUnion(A, B)
      ) by Tautology.from(setUnionMembership of (x := A, y := B, z := x), defAorB)
      thenHave((z ∈ functionRange(f), (app(f, x) === z) /\ ((x ∈ A) \/ (x ∈ B))) |- exists(x, (app(f, x) === z) /\ x ∈ setUnion(A, B))) by RightExists
      have((z ∈ functionRange(f), (app(f, x) === z) /\ ((x ∈ A) \/ (x ∈ B))) |- z ∈ directImage(f, setUnion(A, B))) by Tautology.from(lastStep, defAorB)
      thenHave((z ∈ functionRange(f), exists(x, (app(f, x) === z) /\ ((x ∈ A) \/ (x ∈ B)))) |- z ∈ directImage(f, setUnion(A, B))) by LeftExists
      have(z ∈ directImage(f, setUnion(A, B))) by Tautology.from(lastStep, partialResult)
    }
    val backward = have(z ∈ directImage(f, setUnion(A, B)) ==> z ∈ setUnion(directImage(f, A), directImage(f, B))) subproof {
      val initial = have(
        z ∈ directImage(f, setUnion(A, B)) |-
          (z ∈ functionRange(f) /\ ∃(x, (app(f, x) === z) /\ x ∈ setUnion(A, B)))
      ) by Tautology.from(defAorB)
      val intermediate = have(
        z ∈ functionRange(f) /\ (app(f, x) === z) /\ x ∈ setUnion(A, B) |-
          (z ∈ functionRange(f) /\ (app(f, x) === z) /\ x ∈ A)
          \/ (z ∈ functionRange(f) /\ (app(f, x) === z) /\ x ∈ B)
      ) by Tautology.from(setUnionMembership of (x := A, y := B, z := x))

      assume(z ∈ directImage(f, setUnion(A, B)))
      have(z ∈ functionRange(f) /\ exists(x, (app(f, x) === z) /\ x ∈ setUnion(A, B))) by Tautology.from(defAorB)
      have((app(f, x) === z) /\ x ∈ A |- (app(f, x) === z) /\ x ∈ A) by Tautology
      val existsA = thenHave(
        (app(f, x) === z) /\ x ∈ A |-
          exists(x, (app(f, x) === z) /\ x ∈ A)
      ) by RightExists
      have((app(f, x) === z) /\ x ∈ B |- (app(f, x) === z) /\ x ∈ B) by Tautology
      val existsB = thenHave(
        (app(f, x) === z) /\ x ∈ B |-
          exists(x, (app(f, x) === z) /\ x ∈ B)
      ) by RightExists
      have(
        z ∈ functionRange(f) /\ (app(f, x) === z) /\ x ∈ setUnion(A, B) |-
          (z ∈ directImage(f, A)) \/ (z ∈ directImage(f, B))
      ) by Tautology.from(intermediate, existsA, existsB, defA, defB)
      have(
        (z ∈ functionRange(f), (app(f, x) === z) /\ x ∈ setUnion(A, B)) |-
          z ∈ setUnion(directImage(f, A), directImage(f, B))
      ) by Tautology.from(lastStep, setUnionMembership of (x := directImage(f, A), y := directImage(f, B), z := z))
      thenHave(
        (z ∈ functionRange(f), exists(x, (app(f, x) === z) /\ x ∈ setUnion(A, B))) |-
          z ∈ setUnion(directImage(f, A), directImage(f, B))
      ) by LeftExists
      have(z ∈ setUnion(directImage(f, A), directImage(f, B))) by Tautology.from(lastStep, initial)
    }
    have(z ∈ directImage(f, setUnion(A, B)) <=> z ∈ setUnion(directImage(f, A), directImage(f, B))) by RightIff(forward, backward)
    thenHave(∀(z, z ∈ directImage(f, setUnion(A, B)) <=> z ∈ setUnion(directImage(f, A), directImage(f, B)))) by RightForall
    andThen(Substitution.applySubst(extensionalityAxiom of (x := directImage(f, setUnion(A, B)), y := setUnion(directImage(f, A), directImage(f, B)))))
  }

  /*inline def directImageUnionFormula = y ∈ s <=> y ∈ functionRange(f) /\ ∃(A, y ∈ directImage(f, A))
  val directImageUnionUniqueness = Theorem(
    functional(f) |- ∃!(s, ∀(y, directImageUnionFormula))
  ) {
    have(∃!(s, ∀(y, directImageUnionFormula))) by UniqueComprehension(functionRange(f), lambda(y, ∃(A, y ∈ directImage(f, A))))
    thenHave(thesis) by Weakening
  }

  val directImageUnion = DEF(f, A) --> TheConditional(s, forall(z, z ∈ s <=> ∃(A, z ∈ directImage(f, A))))(directImageUnionUniqueness)

  val directImageUnionThm = Theorem(
    functional(f) /\ forall(A, A ∈ T ==> subset(A, functionDomain(f))) |-
      union(directImage(f, T)) === directImage(f, union(A))
  ) {
    sorry
  }*/

  inline def inverseImageFormula = x ∈ s <=> (x ∈ functionDomain(f) /\ app(f, x) ∈ B)

  val inverseImageUniqueness = Theorem(
    (functional(f), subset(B, functionRange(f))) |- ∃!(s, forall(x, inverseImageFormula))
  ) {
    have(∃!(s, forall(x, inverseImageFormula))) by UniqueComprehension(functionDomain(f), lambda(x, app(f, x) ∈ B))
    thenHave(thesis) by Weakening
  }

  val inverseImage = DEF(f, B) --> TheConditional(s, forall(x, inverseImageFormula))(inverseImageUniqueness)

  val inverseImageUnion = Theorem(
    functional(f) /\
      subset(A, functionRange(f)) /\
      subset(B, functionRange(f))
      |- setUnion(inverseImage(f, A), inverseImage(f, B)) === inverseImage(f, setUnion(A, B))
  ) {
    assume(
      functional(f) /\
        subset(A, functionRange(f)) /\
        subset(B, functionRange(f))
    )

    val subsetAorB = have(subset(setUnion(A, B), functionDomain(f))) by Tautology.from(unionOfTwoSubsets of (a := A, b := B, c := functionDomain(f)))

    have(forall(z, z ∈ directImage(f, A) <=> (z ∈ functionRange(f) /\ ∃(x, (app(f, x) === z) /\ x ∈ A)))) by InstantiateForall(directImage(f, A))(directImage.definition)
    val defA = thenHave(z ∈ directImage(f, A) <=> (z ∈ functionRange(f) /\ ∃(x, (app(f, x) === z) /\ x ∈ A))) by InstantiateForall(z)
    have(forall(z, z ∈ directImage(f, B) <=> (z ∈ functionRange(f) /\ ∃(x, (app(f, x) === z) /\ x ∈ B)))) by InstantiateForall(directImage(f, B))(directImage.definition of (A := B))
    val defB = thenHave(z ∈ directImage(f, B) <=> (z ∈ functionRange(f) /\ ∃(x, (app(f, x) === z) /\ x ∈ B))) by InstantiateForall(z)

    val forward = have(z ∈ setUnion(inverseImage(f, A), inverseImage(f, B)) ==> z ∈ inverseImage(f, setUnion(A, B))) subproof {
      have(z ∈ setUnion(inverseImage(f, A), inverseImage(f, B)) |- (z ∈ inverseImage(f, A)) \/ (z ∈ inverseImage(f, B))) by Tautology.from(
        setUnionMembership of (x := inverseImage(f, A), y := inverseImage(f, B))
      )
      // have(z ∈ inverseImage(f, A) |- app(f, z) ∈ B) by Tautology.from(inverseImage.definition of (z := x))
      sorry
    }
    val backward = have(z ∈ inverseImage(f, setUnion(A, B)) ==> z ∈ setUnion(inverseImage(f, A), inverseImage(f, B))) subproof {
      sorry
    }
    have(z ∈ inverseImage(f, setUnion(A, B)) <=> z ∈ setUnion(inverseImage(f, A), inverseImage(f, B))) by RightIff(forward, backward)
    thenHave(∀(z, z ∈ inverseImage(f, setUnion(A, B)) <=> z ∈ setUnion(inverseImage(f, A), inverseImage(f, B)))) by RightForall
    andThen(Substitution.applySubst(extensionalityAxiom of (x := inverseImage(f, setUnion(A, B)), y := setUnion(inverseImage(f, A), inverseImage(f, B)))))
  }

  val indiscreteIsTopology = Theorem(
    indiscreteTopology(X, T) ==> topology(X, T)
  ) {
    sorry
  }
}
