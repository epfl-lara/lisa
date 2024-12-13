package lisa.maths.topology

import lisa.automation.settheory.SetTheoryTactics.*
import lisa.maths.Quantifiers.*

import lisa.automation.kernel.CommonTactics.Definition

import lisa.maths.topology.Topology.*
import lisa.maths.settheory.*
import lisa.maths.settheory.SetTheory.*
import lisa.maths.settheory.SetTheoryBasics.*
import lisa.automation.kernel.CommonTactics.*
import lisa.maths.settheory.functions.Functionals.*
import lisa.automation.settheory.SetTheoryTactics.UniqueComprehension
import lisa.automation.settheory.SetTheoryTactics.TheConditional

object Instances extends lisa.Main {
  import lisa.maths.settheory.SetTheory.*
  // var defs
  private val x, y, z, a, b, c, t, p, f, r, s = variable
  private val X, T, T1, T2 = variable
  private val S, A, B, Y, o, O, O2, O3 = variable

  val discreteTopology = DEF(X, T) --> nonEmpty(X) /\ (T === powerSet(X))

  val discreteIsTopology = Theorem(
    discreteTopology(X, T) |- topology(X, T)
  ) {
    assume(discreteTopology(X, T))
    val discreteDef = have(nonEmpty(X) /\ (T === powerSet(X))) by Tautology.from(discreteTopology.definition)
    val ext = have(forall(z, in(z, T) <=> in(z, powerSet(X)))) by Tautology.from(extensionalityAxiom of (x := T, y := powerSet(X)), discreteDef)

    val isSub = have(setOfSubsets(X, T)) by Tautology.from(equalityBySubset of (x := T, y := powerSet(X)), discreteDef, setOfSubsets.definition)
    val contEx = have(containsExtremes(X, T)) subproof {
      val a1 = have(in(∅, T) <=> in(∅, powerSet(X))) by InstantiateForall(∅)(ext)
      val a2 = have(∅ ∈ powerSet(X)) by Tautology.from(powerAxiom of (x := ∅, y := X), emptySetIsASubset of (x := X))
      val hasEmpty = have(∅ ∈ T) by Tautology.from(a1, a2)

      have(in(X, T) <=> in(X, powerSet(X))) by InstantiateForall(X)(ext)
      have(X ∈ T) by Tautology.from(lastStep, elemInItsPowerSet of (x := X))
      have(thesis) by Tautology.from(lastStep, hasEmpty, containsExtremes.definition)
    }
    val contUn = have(containsUnion(T)) subproof {
      have((Y ⊆ T) |- (union(Y) ∈ T)) subproof {
        assume(Y ⊆ T)
        have(Y ⊆ powerSet(X)) by Tautology.from(discreteDef, equalityBySubset of (x := T, y := powerSet(X)), subsetTransitivity of (a := Y, b := T, c := powerSet(X)))
        have(union(Y) ∈ powerSet(X)) by Tautology.from(lastStep, subsetClosedUnion of (x := Y, y := X), powerAxiom of (x := union(Y), y := X))
        have(thesis) by Tautology.from(lastStep, discreteDef, replaceEqualityContainsRight of (x := T, y := powerSet(X), z := union(Y)))
      }
      thenHave((Y ⊆ T) ==> (union(Y) ∈ T)) by Tautology
      thenHave(forall(Y, (Y ⊆ T) ==> (union(Y) ∈ T))) by RightForall
      have(thesis) by Tautology.from(lastStep, containsUnion.definition)
    }
    val contInt = have(containsIntersection(T)) subproof {
      have((A ∈ T, B ∈ T) |- (A ∩ B ∈ T)) subproof {
        assume((A ∈ T), (B ∈ T))
        val first = have(A ⊆ X) by Tautology.from(discreteDef, replaceEqualityContainsRight of (x := T, y := powerSet(X), z := A), powerAxiom of (x := A, y := X))
        val second = have(B ⊆ X) by Tautology.from(discreteDef, replaceEqualityContainsRight of (x := T, y := powerSet(X), z := B), powerAxiom of (x := B, y := X))
        have(A ∩ B ∈ powerSet(X)) by Tautology.from(first, second, subsetClosedIntersection of (x := A, y := B, z := X), powerAxiom of (x := A ∩ B, y := X))
        have(thesis) by Tautology.from(lastStep, discreteDef, replaceEqualityContainsRight of (x := T, y := powerSet(X), z := A ∩ B))
      }
      have((A ∈ T /\ B ∈ T) ==> (A ∩ B ∈ T)) by Tautology.from(lastStep, containsIntersection.definition)
      thenHave(forall(B, (A ∈ T /\ B ∈ T) ==> (A ∩ B ∈ T))) by RightForall
      thenHave(forall(A, forall(B, (A ∈ T /\ B ∈ T) ==> (A ∩ B ∈ T)))) by RightForall
      have(thesis) by Tautology.from(lastStep, containsIntersection.definition)
    }

    have(thesis) by Tautology.from(discreteDef, isSub, contEx, contUn, contInt, topology.definition)
  }

  val indiscreteTopology = DEF(X, T) --> nonEmpty(X) /\ (T === unorderedPair(∅, X))

  inline def directImageFormula = y ∈ s <=> (y ∈ Y /\ ∃(x, (app(f, x) === y) /\ x ∈ A))

  val directImageUniqueness = Theorem(
    (functionFrom(f, X, Y), subset(A, X)) |- ∃!(s, forall(y, directImageFormula))
  ) {
    have(∃!(s, forall(y, directImageFormula))) by UniqueComprehension(Y, lambda(y, ∃(x, (app(f, x) === y) /\ x ∈ A)))
    thenHave(thesis) by Weakening
  }

  val directImage = DEF(f, X, Y, A) --> TheConditional(s, forall(y, directImageFormula))(directImageUniqueness)

  val directImageMembership = Theorem((functionFrom(f, X, Y), subset(A, X)) |- y ∈ directImage(f, X, Y, A) <=> (y ∈ Y /\ ∃(x, (app(f, x) === y) /\ x ∈ A))) {
    assume(functionFrom(f, X, Y) /\ subset(A, X))
    have(forall(z, z ∈ directImage(f, X, Y, A) <=> (z ∈ Y /\ ∃(x, (app(f, x) === z) /\ x ∈ A)))) by InstantiateForall(directImage(f, X, Y, A))(directImage.definition)
    thenHave(thesis) by InstantiateForall(y)
  }

  val directImageSetUnion = Theorem(
    functionFrom(f, X, Y) /\
      subset(A, X) /\
      subset(B, X)
      |- setUnion(directImage(f, X, Y, A), directImage(f, X, Y, B)) === directImage(f, X, Y, setUnion(A, B))
  ) {
    assume(
      functionFrom(f, X, Y) /\
        subset(A, X) /\
        subset(B, X)
    )

    val subsetAorB = have(subset(setUnion(A, B), X)) by Tautology.from(unionOfTwoSubsets of (a := A, b := B, c := X))

    have(forall(z, z ∈ directImage(f, X, Y, A) <=> (z ∈ Y /\ ∃(x, (app(f, x) === z) /\ x ∈ A)))) by InstantiateForall(directImage(f, X, Y, A))(directImage.definition)
    val defA = thenHave(z ∈ directImage(f, X, Y, A) <=> (z ∈ Y /\ ∃(x, (app(f, x) === z) /\ x ∈ A))) by InstantiateForall(z)
    have(forall(z, z ∈ directImage(f, X, Y, B) <=> (z ∈ Y /\ ∃(x, (app(f, x) === z) /\ x ∈ B)))) by InstantiateForall(directImage(f, X, Y, B))(directImage.definition of (A := B))
    val defB = thenHave(z ∈ directImage(f, X, Y, B) <=> (z ∈ Y /\ ∃(x, (app(f, x) === z) /\ x ∈ B))) by InstantiateForall(z)
    have(
      subset(setUnion(A, B), X) |-
        forall(
          z,
          z ∈ directImage(f, X, Y, setUnion(A, B)) <=>
            (z ∈ Y /\ ∃(x, (app(f, x) === z) /\ x ∈ setUnion(A, B)))
        )
    ) by InstantiateForall(directImage(f, X, Y, setUnion(A, B)))(directImage.definition of (A := setUnion(A, B)))
    thenHave(
      subset(setUnion(A, B), X) |-
        z ∈ directImage(f, X, Y, setUnion(A, B)) <=>
        (z ∈ Y /\ ∃(x, (app(f, x) === z) /\ x ∈ setUnion(A, B)))
    ) by InstantiateForall(z)
    val defAorB = have(
      z ∈ directImage(f, X, Y, setUnion(A, B)) <=>
        (z ∈ Y /\ ∃(x, (app(f, x) === z) /\ x ∈ setUnion(A, B)))
    ) by Tautology.from(lastStep, subsetAorB)

    val forward = have(z ∈ setUnion(directImage(f, X, Y, A), directImage(f, X, Y, B)) ==> z ∈ directImage(f, X, Y, setUnion(A, B))) subproof {
      val firstPart = have(z ∈ setUnion(directImage(f, X, Y, A), directImage(f, X, Y, B)) |- (z ∈ directImage(f, X, Y, A)) \/ (z ∈ directImage(f, X, Y, B))) by Tautology.from(
        setUnionMembership of (x := directImage(f, X, Y, A), y := directImage(f, X, Y, B))
      )
      assume(z ∈ setUnion(directImage(f, X, Y, A), directImage(f, X, Y, B)))
      have(z ∈ Y /\ ((∃(x, (app(f, x) === z) /\ x ∈ A)) \/ ∃(x, (app(f, x) === z) /\ x ∈ B))) by Tautology.from(
        defA,
        defB,
        firstPart
      )
      val partialResult = thenHave(z ∈ Y /\ (∃(x, (app(f, x) === z) /\ ((x ∈ A) \/ (x ∈ B))))) by Tautology
      have(
        (z ∈ Y, (app(f, x) === z) /\ ((x ∈ A) \/ (x ∈ B)))
          |-
            (app(f, x) === z) /\ x ∈ setUnion(A, B)
      ) by Tautology.from(setUnionMembership of (x := A, y := B, z := x), defAorB)
      thenHave((z ∈ Y, (app(f, x) === z) /\ ((x ∈ A) \/ (x ∈ B))) |- ∃(x, (app(f, x) === z) /\ x ∈ setUnion(A, B))) by RightExists
      have((z ∈ Y, (app(f, x) === z) /\ ((x ∈ A) \/ (x ∈ B))) |- z ∈ directImage(f, X, Y, setUnion(A, B))) by Tautology.from(lastStep, defAorB)
      thenHave((z ∈ Y, ∃(x, (app(f, x) === z) /\ ((x ∈ A) \/ (x ∈ B)))) |- z ∈ directImage(f, X, Y, setUnion(A, B))) by LeftExists
      have(z ∈ directImage(f, X, Y, setUnion(A, B))) by Tautology.from(lastStep, partialResult)
    }
    val backward = have(z ∈ directImage(f, X, Y, setUnion(A, B)) ==> z ∈ setUnion(directImage(f, X, Y, A), directImage(f, X, Y, B))) subproof {
      val intermediate = have(
        z ∈ Y /\ (app(f, x) === z) /\ x ∈ setUnion(A, B) |-
          (z ∈ Y /\ (app(f, x) === z) /\ x ∈ A)
          \/ (z ∈ Y /\ (app(f, x) === z) /\ x ∈ B)
      ) by Tautology.from(setUnionMembership of (x := A, y := B, z := x))

      assume(z ∈ directImage(f, X, Y, setUnion(A, B)))
      have(z ∈ Y /\ ∃(x, (app(f, x) === z) /\ x ∈ setUnion(A, B))) by Tautology.from(defAorB)
      have((app(f, x) === z) /\ x ∈ A |- (app(f, x) === z) /\ x ∈ A) by Tautology
      val existsA = thenHave(
        (app(f, x) === z) /\ x ∈ A |-
          ∃(x, (app(f, x) === z) /\ x ∈ A)
      ) by RightExists
      have((app(f, x) === z) /\ x ∈ B |- (app(f, x) === z) /\ x ∈ B) by Tautology
      val existsB = thenHave(
        (app(f, x) === z) /\ x ∈ B |-
          ∃(x, (app(f, x) === z) /\ x ∈ B)
      ) by RightExists
      have(
        z ∈ Y /\ (app(f, x) === z) /\ x ∈ setUnion(A, B) |-
          (z ∈ directImage(f, X, Y, A)) \/ (z ∈ directImage(f, X, Y, B))
      ) by Tautology.from(intermediate, existsA, existsB, defA, defB)
      have(
        (z ∈ Y, (app(f, x) === z) /\ x ∈ setUnion(A, B)) |-
          z ∈ setUnion(directImage(f, X, Y, A), directImage(f, X, Y, B))
      ) by Tautology.from(lastStep, setUnionMembership of (x := directImage(f, X, Y, A), y := directImage(f, X, Y, B), z := z))
      thenHave(
        (z ∈ Y, ∃(x, (app(f, x) === z) /\ x ∈ setUnion(A, B))) |-
          z ∈ setUnion(directImage(f, X, Y, A), directImage(f, X, Y, B))
      ) by LeftExists
      have(z ∈ setUnion(directImage(f, X, Y, A), directImage(f, X, Y, B))) by Tautology.from(lastStep, defAorB)
    }
    have(z ∈ directImage(f, X, Y, setUnion(A, B)) <=> z ∈ setUnion(directImage(f, X, Y, A), directImage(f, X, Y, B))) by RightIff(forward, backward)
    thenHave(∀(z, z ∈ directImage(f, X, Y, setUnion(A, B)) <=> z ∈ setUnion(directImage(f, X, Y, A), directImage(f, X, Y, B)))) by RightForall
    andThen(Substitution.applySubst(extensionalityAxiom of (x := directImage(f, X, Y, setUnion(A, B)), y := setUnion(directImage(f, X, Y, A), directImage(f, X, Y, B)))))
  }

  /*inline def directImageUnionFormula = y ∈ s <=> y ∈ Y /\ ∃(A, y ∈ directImage(f, A))
  val directImageUnionUniqueness = Theorem(
    functional(f) |- ∃!(s, ∀(y, directImageUnionFormula))
  ) {
    have(∃!(s, ∀(y, directImageUnionFormula))) by UniqueComprehension(Y, lambda(y, ∃(A, y ∈ directImage(f, A))))
    thenHave(thesis) by Weakening
  }

  val directImageUnion = DEF(f, A) --> TheConditional(s, forall(z, z ∈ s <=> ∃(A, z ∈ directImage(f, A))))(directImageUnionUniqueness)

  val directImageUnionThm = Theorem(
    functional(f) /\ forall(A, A ∈ T ==> subset(A, X)) |-
      union(directImage(f, T)) === directImage(f, union(A))
  ) {
    sorry
  }*/

  inline def preimageFormula = x ∈ s <=> (x ∈ X /\ app(f, x) ∈ B)

  val preimageUniqueness = Theorem(
    (functionFrom(f, X, Y), subset(B, Y)) |- ∃!(s, forall(x, preimageFormula))
  ) {
    have(∃!(s, forall(x, preimageFormula))) by UniqueComprehension(X, lambda(x, app(f, x) ∈ B))
    thenHave(thesis) by Weakening
  }

  val preimage = DEF(f, X, Y, B) --> TheConditional(s, forall(x, preimageFormula))(preimageUniqueness)

  val preimageMembership = Theorem((functionFrom(f, X, Y), subset(B, Y)) |- x ∈ preimage(f, X, Y, B) <=> (x ∈ X /\ app(f, x) ∈ B)) {
    assume(functionFrom(f, X, Y) /\ subset(B, Y))
    have(forall(x, x ∈ preimage(f, X, Y, B) <=> (x ∈ X /\ app(f, x) ∈ B))) by InstantiateForall(preimage(f, X, Y, B))(preimage.definition)
    thenHave(thesis) by InstantiateForall(x)
  }

  val preimageSubset = Theorem(
    (functionFrom(f, X, Y), subset(A, Y)) |- preimage(f, X, Y, A) ⊆ X
  ) {
    assume(functionFrom(f, X, Y) /\ subset(A, Y))
    have(in(z, preimage(f, X, Y, A)) ==> in(z, X)) by Tautology.from(preimageMembership of (B := A, x := z))
    thenHave(forall(z, in(z, preimage(f, X, Y, A)) ==> in(z, X))) by RightForall
    have(thesis) by Tautology.from(lastStep, subsetAxiom of (x := preimage(f, X, Y, A), y := X))
  }

  val preimageY = Theorem(
    functionFrom(f, X, Y) |- preimage(f, X, Y, Y) === X
  ) {
    assume(functionFrom(f, X, Y))
    val first = have(preimage(f, X, Y, Y) ⊆ X) by Tautology.from(subsetReflexivity of (x := Y), preimageSubset of (A := Y))

    have(in(z, X) ==> in(z, preimage(f, X, Y, Y))) subproof {
      assume(in(z, X))
      sorry
    }
    thenHave(forall(z, in(z, X) ==> in(z, preimage(f, X, Y, Y)))) by RightForall
    sorry
    // have(thesis) by Tautology.from(lastStep, subsetAxiom of (x := X, y := preimage(f, X, Y, Y)))
  }

  inline def preimagesFormula = x ∈ s <=> (x ∈ powerSet(X) /\ ∃(a, a ∈ A /\ (x === preimage(f, X, Y, a))))

  val preimagesUniqueness = Theorem(
    (functionFrom(f, X, Y), A ⊆ powerSet(Y)) |- ∃!(s, forall(x, preimagesFormula))
  ) {
    have(∃!(s, forall(x, preimagesFormula))) by UniqueComprehension(powerSet(X), lambda(x, ∃(a, a ∈ A /\ (x === preimage(f, X, Y, a)))))
    thenHave(thesis) by Weakening
  }

  val preimages = DEF(f, X, Y, A) --> TheConditional(s, forall(x, preimagesFormula))(preimagesUniqueness)

  val preimagesMembership = Theorem((functionFrom(f, X, Y), A ⊆ powerSet(Y)) |- x ∈ preimages(f, X, Y, A) <=> (x ∈ powerSet(X) /\ ∃(a, a ∈ A /\ (x === preimage(f, X, Y, a))))) {
    assume(functionFrom(f, X, Y) /\ A ⊆ powerSet(Y))
    have(forall(x, x ∈ preimages(f, X, Y, A) <=> (x ∈ powerSet(X) /\ ∃(a, a ∈ A /\ (x === preimage(f, X, Y, a)))))) by InstantiateForall(preimages(f, X, Y, A))(preimages.definition)
    thenHave(thesis) by InstantiateForall(x)
  }

  inline def directImagesFormula = y ∈ s <=> (y ∈ powerSet(Y) /\ ∃(a, a ∈ A /\ (y === directImage(f, X, Y, a))))

  val directImagesUniqueness = Theorem(
    (functionFrom(f, X, Y), A ⊆ powerSet(X)) |- ∃!(s, forall(y, directImagesFormula))
  ) {
    have(∃!(s, forall(y, directImagesFormula))) by UniqueComprehension(powerSet(Y), lambda(y, ∃(a, a ∈ A /\ (y === directImage(f, X, Y, a)))))
    thenHave(thesis) by Weakening
  }

  val directImages = DEF(f, X, Y, A) --> TheConditional(s, forall(y, directImagesFormula))(directImagesUniqueness)

  val directImagesMembership = Theorem((functionFrom(f, X, Y), A ⊆ powerSet(X)) |- y ∈ directImages(f, X, Y, A) <=> (y ∈ powerSet(Y) /\ ∃(a, a ∈ A /\ (y === directImage(f, X, Y, a))))) {
    assume(functionFrom(f, X, Y) /\ A ⊆ powerSet(X))
    have(forall(y, y ∈ directImages(f, X, Y, A) <=> (y ∈ powerSet(Y) /\ ∃(a, a ∈ A /\ (y === directImage(f, X, Y, a)))))) by InstantiateForall(directImages(f, X, Y, A))(directImages.definition)
    thenHave(thesis) by InstantiateForall(y)
  }

  val preimageSetUnion = Theorem(
    functionFrom(f, X, Y) /\
      subset(A, Y) /\
      subset(B, Y)
      |- setUnion(preimage(f, X, Y, A), preimage(f, X, Y, B)) === preimage(f, X, Y, setUnion(A, B))
  ) {
    assume(
      functionFrom(f, X, Y) /\
        subset(A, Y) /\
        subset(B, Y)
    )

    val subsetAorB = have(subset(setUnion(A, B), Y)) by Tautology.from(unionOfTwoSubsets of (a := A, b := B, c := Y))

    have(forall(z, z ∈ preimage(f, X, Y, A) <=> (z ∈ X /\ app(f, z) ∈ A))) by InstantiateForall(preimage(f, X, Y, A))(preimage.definition of (B := A))
    val defA = thenHave(z ∈ preimage(f, X, Y, A) <=> (z ∈ X /\ app(f, z) ∈ A)) by InstantiateForall(z)
    have(forall(z, z ∈ preimage(f, X, Y, B) <=> (z ∈ X /\ app(f, z) ∈ B))) by InstantiateForall(preimage(f, X, Y, B))(preimage.definition)
    val defB = thenHave(z ∈ preimage(f, X, Y, B) <=> (z ∈ X /\ app(f, z) ∈ B)) by InstantiateForall(z)
    have(
      subset(setUnion(A, B), Y) |-
        forall(
          z,
          z ∈ preimage(f, X, Y, setUnion(A, B)) <=>
            (z ∈ X /\ app(f, z) ∈ setUnion(A, B))
        )
    ) by InstantiateForall(preimage(f, X, Y, setUnion(A, B)))(preimage.definition of (B := setUnion(A, B)))
    thenHave(
      subset(setUnion(A, B), Y) |-
        z ∈ preimage(f, X, Y, setUnion(A, B)) <=> (z ∈ X /\ app(f, z) ∈ setUnion(A, B))
    ) by InstantiateForall(z)
    val defAorB = have(
      z ∈ preimage(f, X, Y, setUnion(A, B)) <=> (z ∈ X /\ app(f, z) ∈ setUnion(A, B))
    ) by Tautology.from(lastStep, subsetAorB)

    val forward = have(z ∈ setUnion(preimage(f, X, Y, A), preimage(f, X, Y, B)) ==> z ∈ preimage(f, X, Y, setUnion(A, B))) subproof {
      val firstPart = have(z ∈ setUnion(preimage(f, X, Y, A), preimage(f, X, Y, B)) |- (z ∈ preimage(f, X, Y, A)) \/ (z ∈ preimage(f, X, Y, B))) by Tautology.from(
        setUnionMembership of (x := preimage(f, X, Y, A), y := preimage(f, X, Y, B))
      )
      assume(z ∈ setUnion(preimage(f, X, Y, A), preimage(f, X, Y, B)))
      have(z ∈ X /\ ((app(f, z) ∈ A) \/ (app(f, z) ∈ B))) by Tautology.from(
        defA,
        defB,
        firstPart
      )
      val partialResult = have(z ∈ X /\ (app(f, z) ∈ setUnion(A, B))) by Tautology.from(
        lastStep,
        setUnionMembership of (x := A, y := B, z := app(f, z))
      )
      have(thesis) by Tautology.from(defAorB, lastStep)
    }
    val backward = have(z ∈ preimage(f, X, Y, setUnion(A, B)) ==> z ∈ setUnion(preimage(f, X, Y, A), preimage(f, X, Y, B))) subproof {
      assume(z ∈ preimage(f, X, Y, setUnion(A, B)))
      have((z ∈ preimage(f, X, Y, A)) \/ (z ∈ preimage(f, X, Y, B))) by Tautology.from(
        defAorB,
        setUnionMembership of (x := A, y := B, z := app(f, z)),
        defA,
        defB
      )
      have(thesis) by Tautology.from(
        lastStep,
        setUnionMembership of (x := preimage(f, X, Y, A), y := preimage(f, X, Y, B), z := z)
      )
    }
    have(z ∈ preimage(f, X, Y, setUnion(A, B)) <=> z ∈ setUnion(preimage(f, X, Y, A), preimage(f, X, Y, B))) by RightIff(forward, backward)
    thenHave(∀(z, z ∈ preimage(f, X, Y, setUnion(A, B)) <=> z ∈ setUnion(preimage(f, X, Y, A), preimage(f, X, Y, B)))) by RightForall
    andThen(Substitution.applySubst(extensionalityAxiom of (x := preimage(f, X, Y, setUnion(A, B)), y := setUnion(preimage(f, X, Y, A), preimage(f, X, Y, B)))))
  }

  val preimageUnionThm = Theorem(
    (functionFrom(f, X, Y), B ⊆ powerSet(Y)) |-
      preimage(f, X, Y, union(B)) === union(preimages(f, X, Y, B))
  ) {
    sorry
  }

  // Couldn't import surjectivity from FunctionProperties without an error, so here it is
  val surjective = DEF(f, x, y) --> functionFrom(f, x, y) /\ ∀(b, in(b, y) ==> ∃(a, in(pair(a, b), f)))

  /**
   * Theorem --- if a function is [[surjective]], its range is equal to its codomain.
   */
  val surjectiveImpliesRangeIsCodomain = Theorem(
    surjective(f, x, y) |- (y === functionRange(f))
  ) {
    have(surjective(f, x, y) |- ∀(b, in(b, y) ==> ∃(a, in(pair(a, b), f)))) by Tautology.from(surjective.definition)
    val surjDef = thenHave(surjective(f, x, y) |- in(b, y) ==> ∃(a, in(pair(a, b), f))) by InstantiateForall(b)
    have(∀(t, in(t, functionRange(f)) <=> (∃(a, in(pair(a, t), f))))) by InstantiateForall(functionRange(f))(functionRange.definition of (r -> f))
    val rangeDef = thenHave(in(b, functionRange(f)) <=> (∃(a, in(pair(a, b), f)))) by InstantiateForall(b)

    have(surjective(f, x, y) |- in(b, y) ==> in(b, functionRange(f))) by Tautology.from(surjDef, rangeDef)
    thenHave(surjective(f, x, y) |- ∀(b, in(b, y) ==> in(b, functionRange(f)))) by RightForall
    val surjsub = andThen(Substitution.applySubst(subsetAxiom of (x -> y, y -> functionRange(f))))

    have((surjective(f, x, y), functionFrom(f, x, y)) |- subset(y, functionRange(f)) /\ subset(functionRange(f), y)) by RightAnd(surjsub, functionImpliesRangeSubsetOfCodomain)
    val funceq = andThen(Substitution.applySubst(subsetEqualitySymmetry of (x -> y, y -> functionRange(f))))

    val surjfunc = have(surjective(f, x, y) |- functionFrom(f, x, y)) by Tautology.from(surjective.definition)

    have(thesis) by Cut(surjfunc, funceq)
  }

  val preimageDifference = Theorem(
    (functionFrom(f, X, Y), subset(A, Y))
      |- setDifference(X, preimage(f, X, Y, A)) === preimage(f, X, Y, setDifference(Y, A))
  ) {
    assume(functionFrom(f, X, Y), subset(A, Y))

    have(forall(t, t ∈ setDifference(Y, A) <=> (in(t, Y) /\ !in(t, A)))) by InstantiateForall(setDifference(Y, A))(setDifference.definition of (x := Y, y := A))
    val defDiffY = thenHave(z ∈ setDifference(Y, A) <=> (in(z, Y) /\ !in(z, A))) by InstantiateForall(z)

    val forward = have(x ∈ setDifference(X, preimage(f, X, Y, A)) ==> x ∈ preimage(f, X, Y, setDifference(Y, A))) subproof {
      assume(x ∈ setDifference(X, preimage(f, X, Y, A)))
      sorry
    }

    val backward = have(x ∈ preimage(f, X, Y, setDifference(Y, A)) ==> x ∈ setDifference(X, preimage(f, X, Y, A))) subproof {
      assume(x ∈ preimage(f, X, Y, setDifference(Y, A)))
      sorry
    }

    have(x ∈ setDifference(X, preimage(f, X, Y, A)) <=> x ∈ preimage(f, X, Y, setDifference(Y, A))) by RightIff(forward, backward)
    thenHave(∀(x, x ∈ setDifference(X, preimage(f, X, Y, A)) <=> x ∈ preimage(f, X, Y, setDifference(Y, A)))) by RightForall
    andThen(Substitution.applySubst(extensionalityAxiom of (x := setDifference(X, preimage(f, X, Y, A)), y := preimage(f, X, Y, setDifference(Y, A)))))
  }

  val directImageEmptySet = Theorem(
    (functionFrom(f, X, Y))
      |- directImage(f, X, Y, emptySet) === emptySet
  ) {
    assume(functionFrom(f, X, Y))

    have(subset(emptySet, X) |- forall(z, z ∈ directImage(f, X, Y, emptySet) <=> (z ∈ Y /\ ∃(x, (app(f, x) === z) /\ x ∈ emptySet)))) by InstantiateForall(directImage(f, X, Y, emptySet))(
      directImage.definition of (A := emptySet)
    )
    thenHave(subset(emptySet, X) |- y ∈ directImage(f, X, Y, emptySet) <=> (y ∈ Y /\ ∃(x, (app(f, x) === y) /\ x ∈ emptySet))) by InstantiateForall(y)
    val defA = have(y ∈ directImage(f, X, Y, emptySet) <=> (y ∈ Y /\ ∃(x, (app(f, x) === y) /\ x ∈ emptySet))) by Tautology.from(lastStep, emptySetIsASubset of (x := X))

    val noElements = have(!in(y, directImage(f, X, Y, emptySet))) subproof {
      assume(in(y, directImage(f, X, Y, emptySet)))
      have((app(f, x) === y) /\ x ∈ emptySet |- x ∈ emptySet) by Tautology
      have((app(f, x) === y) /\ x ∈ emptySet |- False) by Tautology.from(lastStep, emptySetAxiom)
      thenHave(∃(x, (app(f, x) === y) /\ x ∈ emptySet) |- False) by LeftExists
      have(False) by Tautology.from(lastStep, defA)
    }
    thenHave(∀(y, !in(y, directImage(f, X, Y, emptySet)))) by RightForall

    have(thesis) by Tautology.from(lastStep, setWithNoElementsIsEmpty of (x := directImage(f, X, Y, emptySet)))
  }

  val directImageSubset = Theorem(
    (functionFrom(f, X, Y), subset(A, X))
      |- directImage(f, X, Y, A) ⊆ functionRange(f)
  ) {
    assume(functionFrom(f, X, Y), subset(A, X))

    have(forall(y, y ∈ relationRange(f) <=> ∃(x, in(pair(x, y), f)))) by InstantiateForall(relationRange(f))(relationRange.definition of (r := f))
    val defRange = thenHave(z ∈ relationRange(f) <=> ∃(x, in(pair(x, z), f))) by InstantiateForall(z)

    have(forall(z, z ∈ directImage(f, X, Y, A) <=> (z ∈ Y /\ ∃(x, (app(f, x) === z) /\ x ∈ A)))) by InstantiateForall(directImage(f, X, Y, A))(directImage.definition)
    val defA = thenHave(z ∈ directImage(f, X, Y, A) <=> (z ∈ Y /\ ∃(x, (app(f, x) === z) /\ x ∈ A))) by InstantiateForall(z)

    have(z ∈ directImage(f, X, Y, A) ==> z ∈ functionRange(f)) subproof {
      assume(z ∈ directImage(f, X, Y, A))
      have(∃(x, (app(f, x) === z) /\ x ∈ A)) by Tautology.from(defA)
      have(x ∈ A /\ (app(f, x) === z) |- pair(x, z) ∈ f) by Tautology.from(
        pairInFunctionIsApp of (a := x, b := z),
        functionFromImpliesFunctional of (x := X, y := Y),
        subsetTactic of (x := A, y := X, z := x),
        functionFromImpliesDomainEq of (x := X, y := Y),
        replaceEqualityContainsRight of (x := functionDomain(f), y := X, z := x)
      )
      thenHave(x ∈ A /\ (app(f, x) === z) |- ∃(x, pair(x, z) ∈ f)) by RightExists
      have(x ∈ A /\ (app(f, x) === z) |- z ∈ relationRange(f)) by Tautology.from(lastStep, defRange)
      thenHave(∃(x, x ∈ A /\ (app(f, x) === z)) |- z ∈ relationRange(f)) by LeftExists
      have(∃(x, x ∈ A /\ (app(f, x) === z)) |- z ∈ relationRange(f) /\ z ∈ Y) by Tautology.from(
        lastStep,
        functionImpliesRangeSubsetOfCodomain of (x := X, y := Y),
        subsetTactic of (x := relationRange(f), y := Y)
      )
      have(thesis) by Tautology.from(lastStep, defA)
    }

    thenHave(forall(z, z ∈ directImage(f, X, Y, A) ==> z ∈ functionRange(f))) by RightForall
    have(thesis) by Tautology.from(subsetAxiom of (x := directImage(f, X, Y, A), y := functionRange(f)), lastStep)
  }

  val directImageX = Theorem(
    functionFrom(f, X, Y)
      |- directImage(f, X, Y, X) === functionRange(f)
  ) {
    assume(functionFrom(f, X, Y))

    have(subset(X, X) |- forall(z, z ∈ directImage(f, X, Y, X) <=> (z ∈ Y /\ ∃(x, (app(f, x) === z) /\ x ∈ X)))) by InstantiateForall(directImage(f, X, Y, X))(directImage.definition of (A := X))
    thenHave(subset(X, X) |- z ∈ directImage(f, X, Y, X) <=> (z ∈ Y /\ ∃(x, (app(f, x) === z) /\ x ∈ X))) by InstantiateForall(z)
    val defIm = have(z ∈ directImage(f, X, Y, X) <=> (z ∈ Y /\ ∃(x, (app(f, x) === z) /\ x ∈ X))) by Tautology.from(
      lastStep,
      subsetReflexivity of (x := X)
    )

    val forward = have(z ∈ directImage(f, X, Y, X) ==> z ∈ functionRange(f)) by Tautology.from(
      directImageSubset of (A := X),
      subsetReflexivity of (x := X),
      subsetTactic of (x := directImage(f, X, Y, X), y := functionRange(f))
    )

    val backward = have(z ∈ functionRange(f) ==> z ∈ directImage(f, X, Y, X)) subproof {
      assume(z ∈ functionRange(f))

      have(subset(functionRange(f), Y)) by Tautology.from(functionImpliesRangeSubsetOfCodomain of (x := X, y := Y))
      val zInY = have(z ∈ Y) by Tautology.from(lastStep, subsetTactic of (x := functionRange(f), y := Y))

      have(x ∈ functionDomain(f) /\ (app(f, x) === z) |- x ∈ X /\ (app(f, x) === z)) by Tautology.from(
        functionFromImpliesDomainEq of (x := X, y := Y),
        replaceEqualityContainsRight of (x := functionDomain(f), y := X, z := x)
      )
      thenHave(x ∈ functionDomain(f) /\ (app(f, x) === z) |- ∃(x, (app(f, x) === z) /\ x ∈ X)) by RightExists
      have(x ∈ functionDomain(f) /\ (app(f, x) === z) |- z ∈ directImage(f, X, Y, X)) by Tautology.from(
        lastStep,
        defIm,
        zInY
      )
      thenHave(∃(x, x ∈ functionDomain(f) /\ (app(f, x) === z)) |- z ∈ directImage(f, X, Y, X)) by LeftExists

      have(thesis) by Tautology.from(
        lastStep,
        functionRangeMembership of (y := z),
        functionFromImpliesFunctional of (x := X, y := Y)
      )
    }

    have(z ∈ directImage(f, X, Y, X) <=> z ∈ functionRange(f)) by RightIff(forward, backward)
    thenHave(∀(z, z ∈ directImage(f, X, Y, X) <=> z ∈ functionRange(f))) by RightForall
    andThen(Substitution.applySubst(extensionalityAxiom of (x := directImage(f, X, Y, X), y := functionRange(f))))
  }

  val applyDirectImage = Theorem(
    A === B |- directImage(f, X, Y, A) === directImage(f, X, Y, B)
  ) {
    have(((A === B), in(z, directImage(f, X, Y, A))) |- in(z, directImage(f, X, Y, B))) subproof {
      have(((A === B), in(z, directImage(f, X, Y, A))) |- in(z, directImage(f, X, Y, A))) by Tautology
      thenHave(thesis) by RightSubstEq.withParametersSimple(List((A, B)), lambda(x, in(z, directImage(f, X, Y, x))))
    }
    have(A === B |- in(z, directImage(f, X, Y, A)) <=> in(z, directImage(f, X, Y, B))) by Tautology.from(lastStep, lastStep of (A := B, B := A))
    thenHave(A === B |- forall(z, in(z, directImage(f, X, Y, A)) <=> in(z, directImage(f, X, Y, B)))) by RightForall
    have(thesis) by Tautology.from(lastStep, extensionalityAxiom of (x := directImage(f, X, Y, A), y := directImage(f, X, Y, B)))
  }

  val directImagePreimage = Theorem(
    (functionFrom(f, X, Y), subset(A, Y))
      |- directImage(f, X, Y, preimage(f, X, Y, A)) ⊆ A
  ) {
    assume(functionFrom(f, X, Y), subset(A, Y))
    have(subset(preimage(f, X, Y, A), X) |- forall(z, z ∈ directImage(f, X, Y, preimage(f, X, Y, A)) <=> (z ∈ Y /\ ∃(x, (app(f, x) === z) /\ x ∈ preimage(f, X, Y, A))))) by InstantiateForall(
      directImage(f, X, Y, preimage(f, X, Y, A))
    )(directImage.definition of (A := preimage(f, X, Y, A)))
    thenHave(subset(preimage(f, X, Y, A), X) |- z ∈ directImage(f, X, Y, preimage(f, X, Y, A)) <=> (z ∈ Y /\ ∃(x, (app(f, x) === z) /\ x ∈ preimage(f, X, Y, A)))) by InstantiateForall(z)
    val imageMember = have(z ∈ directImage(f, X, Y, preimage(f, X, Y, A)) <=> (z ∈ Y /\ ∃(x, (app(f, x) === z) /\ x ∈ preimage(f, X, Y, A)))) by Tautology.from(lastStep, preimageSubset)

    have(in(z, directImage(f, X, Y, preimage(f, X, Y, A))) ==> in(z, A)) subproof {
      assume(in(z, directImage(f, X, Y, preimage(f, X, Y, A))))
      have(((app(f, x) === z), x ∈ preimage(f, X, Y, A)) |- (app(f, x) === z) /\ (x ∈ X /\ app(f, x) ∈ A)) by Tautology.from(preimageMembership of (B := A))
      have(((app(f, x) === z) /\ x ∈ preimage(f, X, Y, A)) |- in(z, A)) by Tautology.from(lastStep, replaceEqualityContainsLeft of (x := app(f, x), y := z, z := A))
      thenHave(exists(x, (app(f, x) === z) /\ x ∈ preimage(f, X, Y, A)) |- in(z, A)) by LeftExists
      have(thesis) by Tautology.from(lastStep, imageMember)
    }
    thenHave(forall(z, in(z, directImage(f, X, Y, preimage(f, X, Y, A))) ==> in(z, A))) by RightForall
    have(thesis) by Tautology.from(lastStep, subsetAxiom of (x := directImage(f, X, Y, preimage(f, X, Y, A)), y := A))
  }

  val directImagePreimageSurjective = Theorem(
    (functionFrom(f, X, Y), surjective(f, X, Y), subset(A, Y))
      |- directImage(f, X, Y, preimage(f, X, Y, A)) === A
  ) {
    assume(functionFrom(f, X, Y), surjective(f, X, Y), subset(A, Y))

    val forward = have(x ∈ directImage(f, X, Y, preimage(f, X, Y, A)) ==> x ∈ A) by Tautology.from(
      subsetTactic of (x := directImage(f, X, Y, preimage(f, X, Y, A)), y := A, z := x),
      directImagePreimage
    )

    val backward = have(x ∈ A ==> x ∈ directImage(f, X, Y, preimage(f, X, Y, A))) subproof {
      assume(x ∈ A)
      sorry
    }

    have(x ∈ directImage(f, X, Y, preimage(f, X, Y, A)) <=> x ∈ A) by RightIff(forward, backward)
    thenHave(∀(x, x ∈ directImage(f, X, Y, preimage(f, X, Y, A)) <=> x ∈ A)) by RightForall
    andThen(Substitution.applySubst(extensionalityAxiom of (x := directImage(f, X, Y, preimage(f, X, Y, A)), y := A)))
  }

  val imageSurjective = Theorem(
    (functionFrom(f, X, Y), surjective(f, X, Y)) |- directImage(f, X, Y, X) === Y
  ) {
    // Should be fairly easy using surjectiveImpliesRangeIsCodomain and directImageX
    sorry
  }

  val indiscreteIsTopology = Theorem(
    indiscreteTopology(X, T) ==> topology(X, T)
  ) {
    assume(indiscreteTopology(X, T))
    val indiscreteDef = have(nonEmpty(X) /\ (T === unorderedPair(∅, X))) by Tautology.from(indiscreteTopology.definition)
    val emptySubs = have(∅ ∈ powerSet(X)) by Tautology.from(emptySetIsASubset of (x := X), powerAxiom of (x := emptySet, y := X))
    val fullSubs = have(X ∈ powerSet(X)) by Tautology.from(elemInItsPowerSet of (x := X))

    val isSub = have(setOfSubsets(X, T)) subproof {
      have(in(unorderedPair(∅, X), powerSet(powerSet(X)))) by Tautology.from(emptySubs, fullSubs, unorderedPairInPowerSet of (x := powerSet(X), a := emptySet, b := X))
      have(unorderedPair(∅, X) ⊆ powerSet(X)) by Tautology.from(lastStep, powerAxiom of (x := unorderedPair(∅, X), y := powerSet(X)))
      have(thesis) by Tautology.from(lastStep, indiscreteDef, replaceEqualitySubsetLeft of (x := unorderedPair(∅, X), y := T, z := powerSet(X)), setOfSubsets.definition)
    }

    val contEx = have(containsExtremes(X, T)) subproof {
      val a = have(X ∈ T) by Tautology.from(pairAxiom of (x := emptySet, y := X, z := X), indiscreteDef, replaceEqualityContainsRight of (x := T, y := unorderedPair(∅, X), z := X))
      val b = have(∅ ∈ T) by Tautology.from(
        pairAxiom of (x := emptySet, y := X, z := emptySet),
        indiscreteDef,
        replaceEqualityContainsRight of (x := T, y := unorderedPair(∅, X), z := emptySet)
      )
      have(thesis) by Tautology.from(a, b, containsExtremes.definition)
    }

    val contUn = have(containsUnion(T)) subproof {
      have((Y ⊆ T) |- union(Y) ∈ T) subproof {
        assume(Y ⊆ T)
        have(Y ⊆ unorderedPair(∅, X)) by Tautology.from(indiscreteDef, replaceEqualitySubsetRight of (x := T, y := unorderedPair(∅, X), z := Y))
        have(forall(z, in(z, Y) ==> in(z, unorderedPair(∅, X)))) by Tautology.from(lastStep, subsetAxiom of (x := Y, y := unorderedPair(∅, X)))
        thenHave(in(z, Y) ==> in(z, unorderedPair(∅, X))) by InstantiateForall(z)
        have(in(z, Y) |- ((z === ∅) \/ (z === X))) by Tautology.from(lastStep, pairAxiom of (x := emptySet, y := X))
        thenHave((in(z, Y) /\ in(a, z)) |- (((z === ∅) \/ (z === X)) /\ in(a, z))) by Tautology
        thenHave((in(z, Y) /\ in(a, z)) |- ((((z === ∅) /\ in(a, z))) \/ ((z === X) /\ in(a, z)))) by Tautology
        have((in(z, Y) /\ in(a, z)) |- (in(a, ∅) \/ (in(a, X) /\ (z === X)))) by Tautology.from(
          lastStep,
          replaceEqualityContainsRight of (x := z, y := emptySet, z := a),
          replaceEqualityContainsRight of (x := z, y := X, z := a)
        )
        have((in(z, Y) /\ in(a, z)) |- (in(a, X) /\ (z === X) /\ in(z, Y))) by Tautology.from(lastStep, emptySetAxiom of (x := a))
        have((in(z, Y) /\ in(a, z)) |- (in(a, X) /\ in(X, Y))) by Tautology.from(lastStep, replaceEqualityContainsLeft of (x := z, y := X, z := Y))
        thenHave(∃(z, in(z, Y) /\ in(a, z)) |- (in(a, X) /\ in(X, Y))) by LeftExists
        val before = have(in(a, union(Y)) ==> (in(a, X) /\ in(X, Y))) by Tautology.from(lastStep, unionAxiom of (z := a, x := Y, y := z), emptySetAxiom of (x := a))
        thenHave(in(a, union(Y)) ==> in(a, X)) by Tautology
        val base = thenHave(forall(a, in(a, union(Y)) ==> in(a, X))) by RightForall
        val cond1 = have(forall(a, !in(a, union(Y))) |- union(Y) === ∅) by Tautology.from(setWithNoElementsIsEmpty of (y := a, x := union(Y)))
        val cond2 = have(∃(a, in(a, union(Y))) |- union(Y) === X) subproof {
          val unionGrow = have(in(a, union(Y)) |- (X ⊆ union(Y))) by Tautology.from(before, unionDoesntShrink of (x := X, y := Y))
          have(in(a, union(Y)) |- (union(Y) === X)) by Tautology.from(base, unionGrow, subsetAxiom of (x := union(Y), y := X, z := a), equalityBySubset of (x := union(Y), y := X))
          thenHave(thesis) by LeftExists
        }
        have((union(Y) === ∅) \/ (union(Y) === X)) by Tautology.from(base, cond1, cond2)
        have(union(Y) ∈ unorderedPair(∅, X)) by Tautology.from(lastStep, pairAxiom of (x := emptySet, y := X, z := union(Y)))
        have(thesis) by Tautology.from(lastStep, indiscreteDef, replaceEqualityContainsRight of (x := unorderedPair(∅, X), y := T, z := union(Y)))
      }
      thenHave((Y ⊆ T) ==> (union(Y) ∈ T)) by Tautology
      thenHave(forall(Y, (Y ⊆ T) ==> (union(Y) ∈ T))) by RightForall
      have(thesis) by Tautology.from(lastStep, containsUnion.definition)
    }

    val contInt = have(containsIntersection(T)) subproof {
      have((A ∈ T /\ B ∈ T) |- (A ∩ B ∈ T)) subproof {
        assume((A ∈ T /\ B ∈ T))
        have(A ∈ unorderedPair(∅, X) /\ B ∈ unorderedPair(∅, X)) by Tautology.from(
          indiscreteDef,
          replaceEqualityContainsRight of (x := T, y := unorderedPair(∅, X), z := A),
          replaceEqualityContainsRight of (x := T, y := unorderedPair(∅, X), z := B)
        )
        val allPossibilities =
          have(((A === ∅) \/ (A === X)) /\ ((B === ∅) \/ (B === X))) by Tautology.from(lastStep, pairAxiom of (x := emptySet, y := X, z := A), pairAxiom of (x := emptySet, y := X, z := B))
        val aEmpty = have((A === ∅) |- (A ∩ B) === ∅) subproof {
          assume(A === emptySet)
          have(in(t, setIntersection(A, B)) <=> (in(t, A) /\ in(t, B))) by Tautology.from(setIntersectionMembership of (x := A, y := B))
          have(!in(t, setIntersection(A, B))) by Tautology.from(lastStep, replaceEqualityContainsRight of (x := emptySet, y := A, z := t), emptySetAxiom of (x := t))
          thenHave(forall(t, !in(t, setIntersection(A, B)))) by RightForall
          have(thesis) by Tautology.from(lastStep, setWithNoElementsIsEmpty of (y := t, x := setIntersection(A, B)))
        }
        val oneEmpty = have(((A === ∅) \/ (B === ∅)) |- ((A ∩ B) === ∅)) by Tautology.from(
          aEmpty,
          aEmpty of (A := B, B := A),
          setIntersectionCommutativity of (x := A, y := B),
          equalityTransitivity of (x := setIntersection(A, B), y := setIntersection(B, A), z := emptySet)
        )
        val bothFull = have((A === X, B === X) |- A ∩ B === X) subproof {
          assume(((A === X) /\ (B === X)))
          have(in(t, setIntersection(A, B)) <=> (in(t, A) /\ in(t, B))) by Tautology.from(setIntersectionMembership of (x := A, y := B))
          have(in(t, setIntersection(A, B)) <=> in(t, X)) by Tautology.from(
            lastStep,
            replaceEqualityContainsRight of (x := X, y := A, z := t),
            replaceEqualityContainsRight of (x := X, y := B, z := t)
          )
          thenHave(forall(t, in(t, setIntersection(A, B)) <=> in(t, X))) by RightForall
          have(thesis) by Tautology.from(lastStep, extensionalityAxiom of (x := setIntersection(A, B), y := X, z := t))
        }
        have((A ∩ B === ∅) \/ (A ∩ B === X)) by Tautology.from(allPossibilities, oneEmpty, bothFull)
        have(in(A ∩ B, unorderedPair(∅, X))) by Tautology.from(lastStep, pairAxiom of (z := setIntersection(A, B), x := emptySet, y := X))
        have(thesis) by Tautology.from(lastStep, indiscreteDef, replaceEqualityContainsRight of (x := unorderedPair(∅, X), y := T, z := setIntersection(A, B)))
      }
      thenHave((A ∈ T /\ B ∈ T) ==> A ∩ B ∈ T) by Tautology
      thenHave(forall(B, (A ∈ T /\ B ∈ T) ==> A ∩ B ∈ T)) by RightForall
      thenHave(forall(A, forall(B, (A ∈ T /\ B ∈ T) ==> A ∩ B ∈ T))) by RightForall
      have(thesis) by Tautology.from(lastStep, containsIntersection.definition)
    }

    have(thesis) by Tautology.from(indiscreteDef, isSub, contEx, contUn, contInt, topology.definition)
  }

  val singletonSetsUniquenes = Theorem(
    ∃!(z, ∀(t, in(t, z) <=> ∃(x, in(x, S) /\ (t === singleton(x)))))
  ) {
    val implicationProof = have(∃(x, in(x, S) /\ (t === singleton(x))) ==> in(t, union(cartesianProduct(S, S)))) subproof { sorry }
    have(() |- existsOne(z, forall(t, in(t, z) <=> ∃(x, in(x, S) /\ (t === singleton(x)))))) by UniqueComprehension.fromOriginalSet(
      union(cartesianProduct(S, S)),
      lambda(t, ∃(x, in(x, S) /\ (t === singleton(x)))),
      implicationProof
    )
  }
  val singletonSets = DEF(S) --> The(z, ∀(t, in(t, z) <=> ∃(x, in(x, S) /\ (t === singleton(x)))))(singletonSetsUniquenes)

  val singletonSetsMembershipRaw = Theorem(
    in(t, singletonSets(S)) <=> ∃(x, ((t === singleton(x)) /\ in(x, S)))
  ) {
    have(∀(t, in(t, singletonSets(S)) <=> ∃(x, in(x, S) /\ (t === singleton(x))))) by InstantiateForall(singletonSets(S))(singletonSets.definition)
    thenHave(thesis) by InstantiateForall(t)
  }

  val singletonSetsMembership = Theorem(
    in(x, S) <=> in(singleton(x), singletonSets(S))
  ) {
    val memb = have(in(t, singletonSets(S)) <=> ∃(x, ((t === singleton(x)) /\ in(x, S)))) by Tautology.from(singletonSetsMembershipRaw)
    have(in(x, S) |- in(singleton(x), singletonSets(S))) subproof {
      assume(in(x, S))
      have(t === singleton(x) |- ((t === singleton(x)) /\ in(x, S))) by Tautology
      thenHave(t === singleton(x) |- ∃(x, ((t === singleton(x)) /\ in(x, S)))) by RightExists
      sorry
      /*have((t === singleton(x)) ==> in(t, singletonSets(S))) by Tautology.from(lastStep, memb)
      thenHave(forall(t, (t === singleton(x)) ==> in(t, singletonSets(S)))) by RightForall
      thenHave((singleton(x) === singleton(x)) ==> in(singleton(x), singletonSets(S))) by InstantiateForall(singleton(x))
      have(thesis) by Tautology.from(lastStep)*/
    }
    have(in(singleton(x), singletonSets(S)) |- in(x, S)) subproof {
      assume(in(singleton(x), singletonSets(S)))

      val removeExists = have((∃(y, in(y, S) /\ (t === singleton(y))), t === singleton(x)) |- in(x, S)) subproof {
        /*have((in(y, S), t === singleton(x), t === singleton(y)) |- (in(y, S), t === singleton(x), t === singleton(y)))
        thenHave((in(y, S) /\ (t === singleton(x)) /\ (t === singleton(y))) |- (in(x, S))) by Tautology.from(
          singletonExtensionality,
          equalityTransitivity of (x := singleton(x), y := t, z := singleton(y)),
          replaceEqualityContainsLeft of (z := S)
        )
        thenHave(∃(y, in(y, S) /\ (t === singleton(x)) /\ (t === singleton(y))) |- (in(x, S))) by LeftExists
        have(∃(y, in(y, S) /\ (t === singleton(y))) /\ (t === singleton(x)) |- (in(x, S))) by Tautology.from(
          lastStep,
          existentialConjunctionWithClosedFormula of (x := y, p := (t === singleton(x)))
        )
        thenHave(thesis) by Tautology*/
        sorry
      }
      have((t === singleton(x), in(t, singletonSets(S))) |- (t === singleton(x), ∃(x, ((t === singleton(x)) /\ in(x, S))))) by Tautology.from(singletonSetsMembershipRaw of (x := y))
      sorry
      /* have((t === singleton(x), in(t, singletonSets(S))) |- in(x, S)) by Tautology.from(lastStep, removeExists)
      have(in(singleton(x), singletonSets(S)) |- in(x, S)) by Tautology.from(lastStep, replaceEqualityContainsLeft of (x := t, y := singleton(x), z := singletonSets(S)))*/
    }
    sorry
  }

  val ifContainsSingletonIsDiscrete = Theorem(
    (topology(X, T), ∀(x, x ∈ X ==> singleton(x) ∈ T)) |- discreteTopology(X, T)
  ) {
    assume(∀(x, x ∈ X ==> singleton(x) ∈ T), topology(X, T))
    val topo = have(nonEmpty(X) /\ setOfSubsets(X, T) /\ containsExtremes(X, T) /\ containsUnion(T) /\ containsIntersection(T)) by Tautology.from(topology.definition)
    have(∀(x, x ∈ X ==> singleton(x) ∈ T)) by Tautology
    val singleDef = thenHave((x ∈ X) ==> (singleton(x) ∈ T)) by InstantiateForall(x)
    have(T === powerSet(X)) subproof {
      // show T subs powerSet(X) (by def of topology)
      val left = have(T ⊆ powerSet(X)) by Tautology.from(topo, setOfSubsets.definition)
      // show powerSet(X) subs T

      // For any S ⊆ X we have S = U{x} -> S ∈ T by unionDef
      have((S ⊆ X) |- S ∈ T) subproof {
        assume(S ⊆ X)
        // prove union(cartesianProduct(S, S)) ⊆ T
        // -> S = union(union(cartesianProduct(S, S))) in T
        have(forall(z, in(z, S) ==> in(z, X))) by Tautology.from(subsetAxiom of (x := S, y := X))
        thenHave(in(z, S) ==> in(z, X)) by InstantiateForall(z)
        have(in(z, S) ==> in(singleton(z), T)) by Tautology.from(lastStep, singleDef of (x := z))
        // have(in(z, S) /\ forall(a, in(z, S) <=> in(singleton(z), V)) |- in(singleton(z), V))
        // have(in(z, S) ==> in(singleton(z), T)) by Tautology.from(sorry)
        // have(in(singleton(z), singleton(S)) ==> in(singleton(z), T))
        // have(singleton(S) ⊆ T)
        // have(union(singleton(S)) ∈ T)
        // have(S ∈ T)
        sorry
      }
      have(in(S, powerSet(X)) ==> in(S, T)) by Tautology.from(lastStep, powerAxiom of (x := S, y := X))
      thenHave(forall(S, in(S, powerSet(X)) ==> in(S, T))) by RightForall
      val right = have(powerSet(X) ⊆ T) by Tautology.from(lastStep, subsetAxiom of (x := powerSet(X), y := T, z := S))

      have(thesis) by Tautology.from(left, right, equalityBySubset of (x := powerSet(X), y := T))
    }
    have(discreteTopology(X, T)) by Tautology.from(lastStep, topo, discreteTopology.definition)
  }

  // -------------------
  // Mappings
  // -------------------
  val mapping = DEF(f, X, T1, Y, T2) -->
    (functionFrom(f, X, Y) /\ topology(X, T1) /\ topology(Y, T2))

  // -------------------
  // Continuity
  // -------------------
  val continuous = DEF(f, X, T1, Y, T2) -->
    (mapping(f, X, T1, Y, T2) /\ forall(O, O ∈ T2 ==> preimage(f, X, Y, O) ∈ T1))

  // -------------------
  // Connectedness
  // -------------------
  val clopen = DEF(X, T, A) --> (
    topology(X, T) /\
      A ∈ T /\ setDifference(X, A) ∈ T
  )

  val connectedTop = DEF(X, T) --> (
    topology(X, T) /\
      forall(A, clopen(X, T, A) ==> ((A === emptySet) \/ (A === X)))
  )

  // -------------------
  // Intermediate value theorem
  // -------------------
  val intermediateValueThm = Theorem((connectedTop(X, T1), continuous(f, X, T1, Y, T2), surjective(f, X, Y)) |- connectedTop(Y, T2)) {
    assume(connectedTop(X, T1), continuous(f, X, T1, Y, T2), surjective(f, X, Y))
    val xIsTop = have(topology(X, T1)) by Tautology.from(continuous.definition, mapping.definition)
    val yIsTop = have(topology(Y, T2)) by Tautology.from(continuous.definition, mapping.definition)

    val xIsConnected = have(forall(A, clopen(X, T1, A) ==> ((A === emptySet) \/ (A === X)))) by Tautology.from(connectedTop.definition of (T := T1))
    val isContinuous = have(forall(O, O ∈ T2 ==> preimage(f, X, Y, O) ∈ T1)) by Tautology.from(continuous.definition)

    val fIsFunction = have(functionFrom(f, X, Y)) by Tautology.from(continuous.definition, mapping.definition)

    have(clopen(Y, T2, A) ==> ((A === emptySet) \/ (A === Y))) subproof {
      assume(clopen(Y, T2, A))

      val aIsSubset = have(A ⊆ Y) subproof {
        have(A ∈ T2) by Tautology.from(clopen.definition of (X := Y, T := T2))
        have(A ∈ powerSet(Y)) by Tautology.from(
          lastStep,
          yIsTop,
          topology.definition of (X := Y, T := T2),
          setOfSubsets.definition of (X := Y, T := T2),
          subsetTactic of (x := T2, y := powerSet(Y), z := A)
        )
        have(thesis) by Tautology.from(lastStep, powerAxiom of (x := A, y := Y))
      }

      val preimageA = have(A ∈ T2 ==> preimage(f, X, Y, A) ∈ T1) by InstantiateForall(A)(isContinuous)
      val yIsClopen = have(A ∈ T2 /\ setDifference(Y, A) ∈ T2) by Tautology.from(clopen.definition of (X := Y, T := T2))
      val part1 = have(preimage(f, X, Y, A) ∈ T1) by Tautology.from(yIsClopen, preimageA)
      val preimageYA = have(setDifference(Y, A) ∈ T2 ==> preimage(f, X, Y, setDifference(Y, A)) ∈ T1) by InstantiateForall(setDifference(Y, A))(isContinuous)
      have(preimage(f, X, Y, setDifference(Y, A)) ∈ T1) by Tautology.from(yIsClopen, preimageYA)
      val part2 = have(setDifference(X, preimage(f, X, Y, A)) ∈ T1) by Tautology.from(
        lastStep,
        aIsSubset,
        fIsFunction,
        preimageDifference,
        replaceEqualityContainsLeft of (x := setDifference(X, preimage(f, X, Y, A)), y := preimage(f, X, Y, setDifference(Y, A)), z := T1)
      )

      // So f^-1(A) is clopen
      val inverseIsClopen = have(clopen(X, T1, preimage(f, X, Y, A))) by Tautology.from(
        xIsTop,
        part1,
        part2,
        clopen.definition of (T := T1, A := preimage(f, X, Y, A))
      )

      // Hence (f^-1(A) === emptySet) \/ (preimage(f, X, Y, A) === X) by connectedness of X
      have(clopen(X, T1, preimage(f, X, Y, A)) ==> (preimage(f, X, Y, A) === emptySet) \/ (preimage(f, X, Y, A) === X)) by InstantiateForall(preimage(f, X, Y, A))(xIsConnected)
      val preImageIsConnected = have((preimage(f, X, Y, A) === emptySet) \/ (preimage(f, X, Y, A) === X)) by Tautology.from(
        lastStep,
        inverseIsClopen
      )

      // Use the fact that f(emptyset)=emptyset, f(f^-1(A)) = A (by surjectivity), f(X) = Y (by surjectivity) to conclude
      val firstCase = have(preimage(f, X, Y, A) === emptySet |- A === emptySet) subproof {
        assume(preimage(f, X, Y, A) === emptySet)
        have(thesis) by Tautology.from(
          lastStep,
          fIsFunction,
          aIsSubset,
          applyDirectImage of (A := preimage(f, X, Y, A), B := emptySet),
          directImagePreimageSurjective,
          directImageEmptySet,
          equalityTransitivity of (x := directImage(f, X, Y, preimage(f, X, Y, A)), y := directImage(f, X, Y, emptySet), z := emptySet),
          equalitySymmetry of (x := directImage(f, X, Y, preimage(f, X, Y, A)), y := A),
          equalityTransitivity of (x := A, y := directImage(f, X, Y, preimage(f, X, Y, A)), z := emptySet)
        )
      }

      val secondCase = have(preimage(f, X, Y, A) === X |- A === Y) subproof {
        assume(preimage(f, X, Y, A) === X)
        have(thesis) by Tautology.from(
          lastStep,
          fIsFunction,
          aIsSubset,
          applyDirectImage of (A := preimage(f, X, Y, A), B := X),
          directImagePreimageSurjective,
          directImageX,
          surjectiveImpliesRangeIsCodomain of (x := X, y := Y),
          equalitySymmetry of (x := Y, y := functionRange(f)),
          equalityTransitivity of (x := directImage(f, X, Y, X), y := functionRange(f), z := Y),
          equalityTransitivity of (x := directImage(f, X, Y, preimage(f, X, Y, A)), y := directImage(f, X, Y, X), z := Y),
          equalitySymmetry of (x := directImage(f, X, Y, preimage(f, X, Y, A)), y := A),
          equalityTransitivity of (x := A, y := directImage(f, X, Y, preimage(f, X, Y, A)), z := Y)
        )
      }

      have(thesis) by Tautology.from(preImageIsConnected, firstCase, secondCase)
    }

    val allClopen = thenHave(forall(A, clopen(Y, T2, A) ==> ((A === emptySet) \/ (A === Y)))) by RightForall
    have(connectedTop(Y, T2)) by Tautology.from(allClopen, yIsTop, connectedTop.definition of (X := Y, T := T2))
  }

  // -------------------
  // Compactness
  // -------------------

  val cover = DEF(X, O) -->
    forall(o, in(o, O) ==> subset(o, X)) /\
    subset(X, union(O))

  val openCover = DEF(X, T, O) -->
    cover(X, O) /\ subset(O, T)

  val finite = DEF(X) --> (X === emptySet) // TODO

  val compact = DEF(X, T) -->
    topology(X, T) /\
    forall(
      O,
      openCover(X, T, O) ==>
        ∃(
          O2, // Another subcovering
          subset(O2, O) /\ cover(X, O2) /\ finite(O2)
        )
    )

  val coverDirectImage = Theorem(
    (functionFrom(f, X, Y), A ⊆ powerSet(X), cover(X, A)) |- cover(directImage(f, X, Y, X), directImages(f, X, Y, A))
  ) {
    assume(functionFrom(f, X, Y), A ⊆ powerSet(X), cover(X, A))

    sorry
  }

  /* Any subset of an open cover is an open cover */
  val subsetOpenCover = Theorem(
    (openCover(X, T, O), subset(O2, O), cover(X, O2)) |- openCover(X, T, O2)
  ) {
    assume(openCover(X, T, O), O2 ⊆ O, cover(X, O2))

    have(thesis) by Tautology.from(
      openCover.definition of (O := O2),
      openCover.definition,
      subsetTransitivity of (a := O2, b := O, c := T)
    )
  }

  /* The preimages of some set in P(Y) are in P(X) */
  val preimagesInPowerSet = Theorem(
    (functionFrom(f, X, Y), A ⊆ powerSet(Y)) |- preimages(f, X, Y, A) ⊆ powerSet(X)
  ) {
    assume(functionFrom(f, X, Y), A ⊆ powerSet(Y))

    have(x ∈ preimages(f, X, Y, A) ==> x ∈ powerSet(X)) by Tautology.from(
      preimagesMembership of (A := A, x := x)
    )
    thenHave(forall(x, x ∈ preimages(f, X, Y, A) ==> x ∈ powerSet(X))) by RightForall
    have(thesis) by Tautology.from(lastStep, subsetAxiom of (x := preimages(f, X, Y, A), y := powerSet(X)))
  }

  /* The set of direct images is finite */
  val directImageFinite = Theorem(
    (functionFrom(f, X, Y), A ⊆ powerSet(X), finite(A)) |- finite(directImages(f, X, Y, A))
  ) {
    assume(functionFrom(f, X, Y), A ⊆ powerSet(X), finite(A))
    // TODO: Needs to have a notion of finiteness to complete the proof
    // Normally it should just be because there is a bijection between directImages(f, X, Y, A) and A, and A is finite
    sorry
  }

  val heineBorelThm = Theorem((compact(X, T1), continuous(f, X, T1, Y, T2), surjective(f, X, Y)) |- compact(Y, T2)) {
    assume(compact(X, T1), continuous(f, X, T1, Y, T2), surjective(f, X, Y))

    val xIsTop = have(topology(X, T1)) by Tautology.from(continuous.definition, mapping.definition)
    val yIsTop = have(topology(Y, T2)) by Tautology.from(continuous.definition, mapping.definition)

    val xIsCompact = have(forall(O, openCover(X, T1, O) ==> ∃(O2, subset(O2, O) /\ cover(X, O2) /\ finite(O2)))) by Tautology.from(
      compact.definition of (T := T1)
    )
    val isContinuous = have(forall(O, O ∈ T2 ==> preimage(f, X, Y, O) ∈ T1)) by Tautology.from(continuous.definition)

    val fIsFunction = have(functionFrom(f, X, Y)) by Tautology.from(continuous.definition, mapping.definition)

    have(openCover(Y, T2, O) |- ∃(O2, subset(O2, O) /\ cover(Y, O2) /\ finite(O2))) subproof {
      assume(openCover(Y, T2, O))

      have(forall(O, (O ⊆ T2) ==> (union(O) ∈ T2))) by Tautology.from(
        containsUnion.definition of (T := T2),
        yIsTop,
        topology.definition of (X := Y, T := T2)
      )
      thenHave(O ⊆ T2 ==> (union(O) ∈ T2)) by InstantiateForall(O)
      val unionInT2 = have(union(O) ∈ T2) by Tautology.from(
        openCover.definition of (X := Y, T := T2),
        lastStep
      )

      val oInPowerSet = have(O ⊆ powerSet(Y)) by Tautology.from(
        openCover.definition of (X := Y, T := T2),
        yIsTop,
        topology.definition of (X := Y, T := T2),
        setOfSubsets.definition of (X := Y, T := T2),
        subsetTransitivity of (a := O, b := T2, c := powerSet(Y))
      )
      val unionOSubsetY = have(union(O) ⊆ Y) by Tautology.from(
        oInPowerSet,
        subsetClosedUnion of (x := O, y := Y)
      )

      // We have an open cover of X, that's preimages(f, X, Y, O)
      val isOpenCover = have(openCover(X, T1, preimages(f, X, Y, O))) subproof {
        // Firstly, it's a cover
        val isCover = have(cover(X, preimages(f, X, Y, O))) subproof {
          have(o ∈ preimages(f, X, Y, O) ==> o ⊆ X) subproof {
            assume(o ∈ preimages(f, X, Y, O))
            have(o ∈ powerSet(X)) by Tautology.from(
              preimagesMembership of (A := O, x := o),
              fIsFunction,
              oInPowerSet
            )
            have(o ⊆ X) by Tautology.from(lastStep, powerAxiom of (x := o, y := X))
          }
          val firstPart = thenHave(∀(o, o ∈ preimages(f, X, Y, O) ==> o ⊆ X)) by RightForall

          // The covering part
          have(x ∈ X ==> x ∈ union(preimages(f, X, Y, O))) subproof {
            assume(x ∈ X)
            // Function application
            have(app(f, x) ∈ Y) by Tautology.from(
              fIsFunction,
              lastStep,
              functionFromApplication of (x := X, y := Y, a := x),
              functionFrom.definition of (x := X, y := Y)
            )
            // Since Y is covered by O
            have(app(f, x) ∈ union(O)) by Tautology.from(
              lastStep,
              openCover.definition of (X := Y, T := T2),
              cover.definition of (X := Y),
              subsetTactic of (x := Y, y := union(O), z := app(f, x))
            )
            // That's the definition of being in the preimage!
            have(x ∈ preimage(f, X, Y, union(O))) by Tautology.from(
              lastStep,
              preimageMembership of (B := union(O)),
              fIsFunction,
              unionOSubsetY
            )
            // use that preimage(f, X, Y, union(O)) ⊆ union(preimages(f, X, Y, O))
            have(x ∈ union(preimages(f, X, Y, O))) by Tautology.from(
              lastStep,
              preimageUnionThm of (B := O),
              replaceEqualityContainsRight of (x := preimage(f, X, Y, union(O)), y := union(preimages(f, X, Y, O)), z := x),
              fIsFunction,
              oInPowerSet
            )
          }
          thenHave(forall(x, x ∈ X ==> x ∈ union(preimages(f, X, Y, O)))) by RightForall
          val secondPart = have(subset(X, union(preimages(f, X, Y, O)))) by Tautology.from(
            lastStep,
            subsetAxiom of (x := X, y := union(preimages(f, X, Y, O)))
          )

          have(thesis) by Tautology.from(firstPart, secondPart, cover.definition of (O := preimages(f, X, Y, O)))
        }

        // Also, its elements are open
        have(z ∈ preimages(f, X, Y, O) ==> z ∈ T1) subproof {
          assume(z ∈ preimages(f, X, Y, O))
          val existsa = have(∃(a, a ∈ O /\ (z === preimage(f, X, Y, a)))) by Tautology.from(
            lastStep,
            preimagesMembership of (A := O, x := z),
            fIsFunction,
            oInPowerSet
          )
          have(a ∈ O /\ (z === preimage(f, X, Y, a)) |- z ∈ T1) subproof {
            assume(a ∈ O /\ (z === preimage(f, X, Y, a)))
            val aInT2 = have(a ∈ T2) by Tautology.from(
              openCover.definition of (X := Y, T := T2),
              subsetTactic of (x := O, y := T2, z := a)
            )
            have(a ∈ T2 ==> preimage(f, X, Y, a) ∈ T1) by InstantiateForall(a)(isContinuous)
            have(preimage(f, X, Y, a) ∈ T1) by Tautology.from(
              aInT2,
              lastStep
            )
            have(z ∈ T1) by Tautology.from(lastStep, replaceEqualityContainsLeft of (x := z, y := preimage(f, X, Y, a), z := T1))
          }
          thenHave(∃(a, a ∈ O /\ (z === preimage(f, X, Y, a))) |- z ∈ T1) by LeftExists
          have(thesis) by Tautology.from(existsa, lastStep)
        }
        thenHave(forall(z, z ∈ preimages(f, X, Y, O) ==> z ∈ T1)) by RightForall
        val isOpenSubset = have(preimages(f, X, Y, O) ⊆ T1) by Tautology.from(
          subsetAxiom of (x := preimages(f, X, Y, O), y := T1),
          lastStep
        )

        have(thesis) by Tautology.from(openCover.definition of (T := T1, O := preimages(f, X, Y, O)), isCover, isOpenSubset)
      }

      // Whence the existence of a finite subcover O3
      have(openCover(X, T1, preimages(f, X, Y, O)) ==> ∃(O3, subset(O3, preimages(f, X, Y, O)) /\ cover(X, O3) /\ finite(O3))) by InstantiateForall(preimages(f, X, Y, O))(
        xIsCompact
      )
      val existsO3 = have(∃(O3, subset(O3, preimages(f, X, Y, O)) /\ cover(X, O3) /\ finite(O3))) by Tautology.from(lastStep, isOpenCover)

      have(
        O3 ⊆ preimages(f, X, Y, O) /\ cover(X, O3) /\ finite(O3)
          |-
          subset(directImages(f, X, Y, O3), O) /\ cover(Y, directImages(f, X, Y, O3)) /\ finite(directImages(f, X, Y, O3))
      ) subproof {
        assume(O3 ⊆ preimages(f, X, Y, O), cover(X, O3), finite(O3))

        val o3InPowerSet = have(O3 ⊆ powerSet(X)) subproof {
          have(preimages(f, X, Y, O) ⊆ powerSet(X)) by Tautology.from(
            fIsFunction,
            oInPowerSet,
            preimagesInPowerSet of (A := O)
          )
          have(thesis) by Tautology.from(lastStep, subsetTransitivity of (a := O3, b := preimages(f, X, Y, O), c := powerSet(X)))
        }

        // So it's a subset
        have(z ∈ directImages(f, X, Y, O3) ==> z ∈ O) subproof {
          assume(z ∈ directImages(f, X, Y, O3))

          have(z ∈ powerSet(Y) /\ ∃(a, a ∈ O3 /\ (z === directImage(f, X, Y, a)))) by Tautology.from(
            directImagesMembership of (A := O3, y := z),
            fIsFunction,
            o3InPowerSet
          )

          have(a ∈ O3 /\ (z === directImage(f, X, Y, a)) |- z ∈ O) subproof {
            assume(a ∈ O3, z === directImage(f, X, Y, a))
            val aInPreimages = have(a ∈ preimages(f, X, Y, O)) by Tautology.from(
              lastStep,
              subsetTactic of (x := O3, y := preimages(f, X, Y, O), z := a)
            )
            have(b ∈ O /\ (a === preimage(f, X, Y, b)) |- directImage(f, X, Y, a) ∈ O) subproof {
              assume(b ∈ O, a === preimage(f, X, Y, b))
              have(b ⊆ Y) by Tautology.from(
                oInPowerSet,
                subsetTactic of (z := b, x := O, y := powerSet(Y)),
                powerAxiom of (x := b, y := Y)
              )
              val statement = have(directImage(f, X, Y, preimage(f, X, Y, b)) === b) by Tautology.from(
                lastStep,
                directImagePreimageSurjective of (A := b),
                fIsFunction
              )
              thenHave(directImage(f, X, Y, a) === b) by RightSubstEq.withParametersSimple(List((a, preimage(f, X, Y, b))), lambda(x, directImage(f, X, Y, x) === b))
              have(thesis) by Tautology.from(lastStep, replaceEqualityContainsLeft of (x := directImage(f, X, Y, a), y := b, z := O))
            }
            thenHave(exists(b, b ∈ O /\ (a === preimage(f, X, Y, b))) |- directImage(f, X, Y, a) ∈ O) by LeftExists
            // use that (functionFrom(f, X, Y), O ⊆ powerSet(Y)) |- a ∈ preimages(f, X, Y, O) ==> (∃(b, b ∈ O /\ (a === preimage(f, X, Y, b)))))
            have(directImage(f, X, Y, a) ∈ O) by Tautology.from(lastStep, aInPreimages, preimagesMembership of (A := O, x := a), fIsFunction, oInPowerSet)
            // Conclude since z === directImage(f, X, Y, a)
            have(z ∈ O) by Tautology.from(lastStep, replaceEqualityContainsLeft of (x := z, y := directImage(f, X, Y, a), z := O))
          }

          thenHave(∃(a, a ∈ O3 /\ (z === directImage(f, X, Y, a))) |- z ∈ O) by LeftExists

          // Since z is in directImages, then we precisely have ∃(a, a ∈ O3 /\ (z === directImage(f, X, Y, a))) by `directImagesMembership`
          have(thesis) by Tautology.from(lastStep, directImagesMembership of (A := O3, y := z), fIsFunction, o3InPowerSet)
        }
        thenHave(forall(z, z ∈ directImages(f, X, Y, O3) ==> z ∈ O)) by RightForall
        val isSubset = have(directImages(f, X, Y, O3) ⊆ O) by Tautology.from(lastStep, subsetAxiom of (x := directImages(f, X, Y, O3), y := O))

        // That is also covering Y
        // We use that f is surjective to get that directImage(f, X, Y, X) = Y
        val replacement = have(directImage(f, X, Y, X) === Y) by Tautology.from(imageSurjective, fIsFunction)
        val coveringStatement = have(cover(directImage(f, X, Y, X), directImages(f, X, Y, O3))) by Tautology.from(
          coverDirectImage of (A := O3),
          fIsFunction,
          o3InPowerSet
        )
        have(
          ((directImage(f, X, Y, X) === Y), cover(directImage(f, X, Y, X), directImages(f, X, Y, O3)))
            |- cover(Y, directImages(f, X, Y, O3))
        ) subproof {
          have(
            ((directImage(f, X, Y, X) === Y), cover(directImage(f, X, Y, X), directImages(f, X, Y, O3)))
              |- cover(directImage(f, X, Y, X), directImages(f, X, Y, O3))
          ) by Tautology
          thenHave(thesis) by RightSubstEq.withParametersSimple(List((directImage(f, X, Y, X), Y)), lambda(x, cover(x, directImages(f, X, Y, O3))))
        }
        val covering = have(cover(Y, directImages(f, X, Y, O3))) by Tautology.from(lastStep, coveringStatement, replacement)

        // Finally it's finite since O3 is
        val finiteCover = have(finite(directImages(f, X, Y, O3))) by Tautology.from(
          directImageFinite of (A := O3),
          fIsFunction,
          o3InPowerSet
        )

        have(thesis) by Tautology.from(isSubset, finiteCover, covering)
      }

      have(
        subset(O3, preimages(f, X, Y, O)) /\ cover(X, O3) /\ finite(O3)
          |-
          ∃(O2, subset(O2, O) /\ cover(Y, O2) /\ finite(O2))
      ) subproof {
        sorry
      }

      // Concluding
      thenHave(∃(O3, subset(O3, preimages(f, X, Y, O)) /\ cover(X, O3) /\ finite(O3)) |- ∃(O2, subset(O2, O) /\ cover(Y, O2) /\ finite(O2))) by LeftExists
      have(thesis) by Tautology.from(lastStep, existsO3)
    }
    thenHave(openCover(Y, T2, O) ==> ∃(O2, subset(O2, O) /\ cover(Y, O2) /\ finite(O2))) by Tautology
    val yIsCompact = thenHave(forall(O, openCover(Y, T2, O) ==> ∃(O2, subset(O2, O) /\ cover(Y, O2) /\ finite(O2)))) by RightForall

    have(thesis) by Tautology.from(yIsCompact, yIsTop, compact.definition of (X := Y, T := T2))
  }
}
