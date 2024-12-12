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

  inline def unionPreimageFormula = x ∈ s <=> (x ∈ X /\ app(f, x) ∈ union(A))

  val unionPreimageUniqueness = Theorem(
    (functionFrom(f, X, Y), A ⊆ powerSet(Y)) |- ∃!(s, forall(x, unionPreimageFormula))
  ) {
    have(∃!(s, forall(x, unionPreimageFormula))) by UniqueComprehension(X, lambda(x, app(f, x) ∈ union(A)))
    thenHave(thesis) by Weakening
  }

  val unionPreimage = DEF(f, X, Y, A) --> TheConditional(s, forall(x, unionPreimageFormula))(unionPreimageUniqueness)

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
    (functionFrom(f, X, Y), A ⊆ powerSet(Y)) |-
      preimage(f, X, Y, union(A)) === unionPreimage(f, X, Y, A)
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
    sorry
  }

  val directImagePreimage = Theorem(
    (functionFrom(f, X, Y), subset(A, Y))
      |- directImage(f, X, Y, preimage(f, X, Y, A)) ⊆ A
  ) {
    assume(functionFrom(f, X, Y), subset(A, Y))
    sorry
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

  val preimageSubset = Theorem(
    (functionFrom(f, X, Y), subset(A, Y)) |- preimage(f, X, Y, A) ⊆ X
  ) {
    sorry
  }

  val preimageY = Theorem(
    functionFrom(f, X, Y) |- preimage(f, X, Y, Y) === X
  ) {
    sorry
  }

  val imageSurjective = Theorem(
    (functionFrom(f, X, Y), surjective(f, X, Y)) |- directImage(f, X, Y, X) === Y
  ) {
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
          subset(O2, O) /\
            openCover(X, T, O2) /\
            finite(O2)
        )
    )

  val heineBorelThm = Theorem((compact(X, T1), continuous(f, X, T1, Y, T2), surjective(f, X, Y)) |- compact(Y, T2)) {
    assume(compact(X, T1), continuous(f, X, T1, Y, T2), surjective(f, X, Y))

    val xIsTop = have(topology(X, T1)) by Tautology.from(continuous.definition, mapping.definition)
    val yIsTop = have(topology(Y, T2)) by Tautology.from(continuous.definition, mapping.definition)

    val xIsCompact = have(forall(O, openCover(X, T1, O) ==> ∃(O2, subset(O2, O) /\ openCover(X, T1, O2) /\ finite(O2)))) by Tautology.from(
      compact.definition of (T := T1)
    )
    val isContinuous = have(forall(O, O ∈ T2 ==> preimage(f, X, Y, O) ∈ T1)) by Tautology.from(continuous.definition)

    val fIsFunction = have(functionFrom(f, X, Y)) by Tautology.from(continuous.definition, mapping.definition)

    have(openCover(Y, T2, O) |- ∃(O2, subset(O2, O) /\ openCover(Y, T2, O2) /\ finite(O2))) subproof {
      assume(openCover(Y, T2, O))

      // have(cover(Y, O)) by Tautology.from(cover.definition of (X := Y, O := O))
      // have(O ⊆ T2 ==> (union(O) ∈ T2)) by InstantiateForall(containsUnion.definition of (T := T2))(O)
      /*val unionInT2 = have(union(O) ∈ T2) by Tautology.from(
        openCover.definition of (X := Y, T := T2),
        containsUnion.definition of (T := T2),
        lastStep
      )*/

      // We have an open cover of X, that's unionPreimage(f, X, Y, O)
      val isOpenCover = have(openCover(X, T1, unionPreimage(f, X, Y, O))) subproof {
        val isCover = have(cover(X, unionPreimage(f, X, Y, O))) subproof {
          sorry
        }
        have(z ∈ unionPreimage(f, X, Y, O) ==> z ∈ T1) subproof {
          assume(z ∈ unionPreimage(f, X, Y, O))

          sorry
        } /*Tautology.from(
          // preimageSubset of (f := f, X := X, Y := Y, A := union(O)),
          // preimageUnionThm of (f := f, X := X, Y := Y, O := O)
          sorry
        )*/
        thenHave(forall(z, z ∈ unionPreimage(f, X, Y, O) ==> z ∈ T1)) by RightForall
        val isSubset = have(unionPreimage(f, X, Y, O) ⊆ T1) by Tautology.from(
          subsetAxiom of (x := unionPreimage(f, X, Y, O), y := T1),
          lastStep
        )
        have(thesis) by Tautology.from(openCover.definition of (T := T1, O := unionPreimage(f, X, Y, O)), isCover, isSubset)
      }

      // Whence the existence of a finite subcover O3
      have(openCover(X, T1, unionPreimage(f, X, Y, O)) ==> ∃(O3, subset(O3, unionPreimage(f, X, Y, O)) /\ openCover(X, T1, O3) /\ finite(O3))) by InstantiateForall(unionPreimage(f, X, Y, O))(
        xIsCompact
      )
      val existsO3 = have(∃(O3, subset(O3, unionPreimage(f, X, Y, O)) /\ openCover(X, T1, O3) /\ finite(O3))) by Tautology.from(lastStep, isOpenCover)

      have(subset(O3, unionPreimage(f, X, Y, O)) /\ openCover(X, T1, O3) /\ finite(O3) |- ∃(O2, subset(O2, O) /\ openCover(Y, T2, O2) /\ finite(O2))) subproof {
        assume(subset(O3, unionPreimage(f, X, Y, O)), openCover(X, T1, O3), finite(O3))
        sorry
      }

      // Concluding
      thenHave(∃(O3, subset(O3, unionPreimage(f, X, Y, O)) /\ openCover(X, T1, O3) /\ finite(O3)) |- ∃(O2, subset(O2, O) /\ openCover(Y, T2, O2) /\ finite(O2))) by LeftExists
      have(thesis) by Tautology.from(lastStep, existsO3)
    }
    thenHave(openCover(Y, T2, O) ==> ∃(O2, subset(O2, O) /\ openCover(Y, T2, O2) /\ finite(O2))) by Tautology
    val yIsCompact = thenHave(forall(O, openCover(Y, T2, O) ==> ∃(O2, subset(O2, O) /\ openCover(Y, T2, O2) /\ finite(O2)))) by RightForall

    have(thesis) by Tautology.from(yIsCompact, yIsTop, compact.definition of (X := Y, T := T2))
  }
}
