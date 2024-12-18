package lisa.maths.settheory.functions

import lisa.automation.kernel.CommonTactics.Definition
import lisa.automation.settheory.SetTheoryTactics.*
import lisa.maths.Quantifiers.*
import lisa.maths.settheory.SetTheoryBasics.*
import lisa.automation.kernel.CommonTactics.*
import lisa.maths.settheory.functions.Functionals.*
import lisa.automation.settheory.SetTheoryTactics.UniqueComprehension
import lisa.automation.settheory.SetTheoryTactics.TheConditional
import lisa.maths.settheory.SetTheory.*

object DirectPreimages extends lisa.Main {

  // var defs
  private val x, y, z, a, b, c, t, p, f, r, s = variable
  private val X, T, T1, T2 = variable
  private val S, A, B, Y, o, O, O2, O3 = variable

  /**
   * Don't know why, but I need to paste it directly here otherwise we have a matcherror null error (from FunctionProperties)
   */
  val surjective = DEF(f, x, y) --> functionFrom(f, x, y) /\ ∀(b, in(b, y) ==> ∃(a, in(pair(a, b), f)))

  /* Also copied the theorem (from FunctionProperties) */
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

    have(in(z, X) ==> in(z, preimage(f, X, Y, Y))) by Tautology.from(
      functionFromApplication of (x := X, y := Y, a := z),
      functionFrom.definition of (x := X, y := Y),
      preimageMembership of (x := z, B := Y),
      subsetReflexivity of (x := Y)
    )
    thenHave(forall(z, in(z, X) ==> in(z, preimage(f, X, Y, Y)))) by RightForall
    val second = have(X ⊆ preimage(f, X, Y, Y)) by Tautology.from(lastStep, subsetAxiom of (x := X, y := preimage(f, X, Y, Y)))
    have(thesis) by Tautology.from(first, second, equalityBySubset of (x := X, y := preimage(f, X, Y, Y)))
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

  val preimageDifference = Theorem(
    (functionFrom(f, X, Y), subset(A, Y))
      |- setDifference(X, preimage(f, X, Y, A)) === preimage(f, X, Y, setDifference(Y, A))
  ) {
    assume(functionFrom(f, X, Y), subset(A, Y))

    have(forall(t, t ∈ setDifference(Y, A) <=> (in(t, Y) /\ !in(t, A)))) by InstantiateForall(setDifference(Y, A))(setDifference.definition of (x := Y, y := A))
    val defDiffY = thenHave(z ∈ setDifference(Y, A) <=> (in(z, Y) /\ !in(z, A))) by InstantiateForall(z)

    val forward = have(x ∈ setDifference(X, preimage(f, X, Y, A)) ==> x ∈ preimage(f, X, Y, setDifference(Y, A))) subproof {
      assume(x ∈ setDifference(X, preimage(f, X, Y, A)))

      have(in(x, X) /\ !in(x, preimage(f, X, Y, A))) by Tautology.from(setDifferenceMembership of (t := x, x := X, y := preimage(f, X, Y, A)))
      have(in(x, X) /\ !in(app(f, x), A)) by Tautology.from(lastStep, preimageMembership of (B := A))
      // (x ∈ X /\ app(f, x) ∈ setDifference(Y, A))
      have(in(x, X) /\ in(app(f, x), setDifference(Y, A))) by Tautology.from(
        lastStep,
        functionFromApplication of (x := X, y := Y, a := x),
        functionFrom.definition of (x := X, y := Y),
        setDifferenceMembership of (t := app(f, x), x := Y, y := A)
      )
      have(thesis) by Tautology.from(lastStep, differenceShrinks of (x := Y, y := A), preimageMembership of (B := setDifference(Y, A)))
    }

    val backward = have(x ∈ preimage(f, X, Y, setDifference(Y, A)) ==> x ∈ setDifference(X, preimage(f, X, Y, A))) subproof {
      assume(x ∈ preimage(f, X, Y, setDifference(Y, A)))
      have(x ∈ X /\ app(f, x) ∈ Y /\ !(app(f, x) ∈ A)) by Tautology.from(
        preimageMembership of (B := setDifference(Y, A)),
        setDifferenceMembership of (t := app(f, x), x := Y, y := A),
        differenceShrinks of (x := Y, y := A)
      )
      have(thesis) by Tautology.from(lastStep, preimageMembership of (B := A, t := x), setDifferenceMembership of (t := x, x := X, y := preimage(f, X, Y, A)))
    }

    have(x ∈ setDifference(X, preimage(f, X, Y, A)) <=> x ∈ preimage(f, X, Y, setDifference(Y, A))) by RightIff(forward, backward)
    thenHave(∀(x, x ∈ setDifference(X, preimage(f, X, Y, A)) <=> x ∈ preimage(f, X, Y, setDifference(Y, A)))) by RightForall
    andThen(Substitution.applySubst(extensionalityAxiom of (x := setDifference(X, preimage(f, X, Y, A)), y := preimage(f, X, Y, setDifference(Y, A)))))
  }

  val preimageUnionThm = Theorem(
    (functionFrom(f, X, Y), B ⊆ powerSet(Y)) |-
      preimage(f, X, Y, union(B)) === union(preimages(f, X, Y, B))
  ) {
    sorry
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

    val backward = have(y ∈ A ==> y ∈ directImage(f, X, Y, preimage(f, X, Y, A))) subproof {
      assume(y ∈ A)
      have(x ∈ functionDomain(f) /\ (app(f, x) === y) |- (app(f, x) === y) /\ x ∈ preimage(f, X, Y, A)) by Tautology.from(
        functionFromImpliesDomainEq of (x := X, y := Y),
        replaceEqualityContainsRight of (x := functionDomain(f), y := X, z := x),
        replaceEqualityContainsLeft of (x := app(f, x), z := A),
        preimageMembership of (B := A)
      )
      thenHave(x ∈ functionDomain(f) /\ (app(f, x) === y) |- ∃(x, (app(f, x) === y) /\ x ∈ preimage(f, X, Y, A))) by RightExists
      have(x ∈ functionDomain(f) /\ (app(f, x) === y) |- y ∈ directImage(f, X, Y, preimage(f, X, Y, A))) by Tautology.from(
        lastStep,
        subsetTactic of (x := A, y := Y, z := y),
        directImageMembership of (A := preimage(f, X, Y, A)),
        preimageSubset
      )
      thenHave(∃(x, x ∈ functionDomain(f) /\ (app(f, x) === y)) |- y ∈ directImage(f, X, Y, preimage(f, X, Y, A))) by LeftExists
      have(thesis) by Tautology.from(
        lastStep,
        functionRangeMembership,
        subsetTactic of (x := A, y := Y, z := y),
        surjectiveImpliesRangeIsCodomain of (x := X, y := Y),
        replaceEqualityContainsRight of (x := Y, y := functionRange(f), z := y),
        functionFromImpliesFunctional of (x := X, y := Y)
      )
    }

    have(x ∈ directImage(f, X, Y, preimage(f, X, Y, A)) <=> x ∈ A) by RightIff(forward, backward of (y := x))
    thenHave(∀(x, x ∈ directImage(f, X, Y, preimage(f, X, Y, A)) <=> x ∈ A)) by RightForall
    andThen(Substitution.applySubst(extensionalityAxiom of (x := directImage(f, X, Y, preimage(f, X, Y, A)), y := A)))
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

  val imageSurjective = Theorem(
    (functionFrom(f, X, Y), surjective(f, X, Y)) |- directImage(f, X, Y, X) === Y
  ) {
    have(thesis) by Tautology.from(
      surjectiveImpliesRangeIsCodomain of (x := X, y := Y),
      directImageX,
      equalityTransitivity of (x := Y, y := functionRange(f), z := directImage(f, X, Y, X))
    )
  }
}
