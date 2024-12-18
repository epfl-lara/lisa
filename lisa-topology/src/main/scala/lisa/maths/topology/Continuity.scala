package lisa.maths.topology

import lisa.automation.settheory.SetTheoryTactics.*
import lisa.maths.Quantifiers.*

import lisa.automation.kernel.CommonTactics.Definition

import lisa.maths.topology.Topology.*
import lisa.maths.settheory.*
import lisa.maths.settheory.SetTheory.*
import lisa.maths.settheory.SetTheoryBasics.*
import lisa.automation.kernel.CommonTactics.*
import lisa.automation.settheory.SetTheoryTactics.UniqueComprehension
import lisa.automation.settheory.SetTheoryTactics.TheConditional
import lisa.maths.settheory.functions.Functionals.*
import lisa.maths.settheory.functions.DirectPreimages.*

object Continuity extends lisa.Main {
  // var defs
  private val x, y, z, a, b, c, t, p, f, r, s = variable
  private val X, T, T1, T2 = variable
  private val S, A, B, Y, o, O, O2, O3 = variable

  // -------------------
  // Mappings
  // -------------------
  /*
   * A mapping is a function between topological spaces
   */
  val mapping = DEF(f, X, T1, Y, T2) -->
    (functionFrom(f, X, Y) /\ topology(X, T1) /\ topology(Y, T2))

  // -------------------
  // Continuity
  // -------------------
  /**
   * A function f is continuous if the preimage of any open set in the codomain is open in the domain
   */
  val continuous = DEF(f, X, T1, Y, T2) -->
    (mapping(f, X, T1, Y, T2) /\ ∀(O, O ∈ T2 ==> preimage(f, X, Y, O) ∈ T1))

  // -------------------
  // Connectedness
  // -------------------
  /*
   * A set A is clopen if it is both open and closed
   */
  val clopen = DEF(X, T, A) --> (
    topology(X, T) /\
      A ∈ T /\ setDifference(X, A) ∈ T
  )

  /**
   * A topological space is connected if the only clopen sets are the empty set and the whole space
   */
  val connectedTop = DEF(X, T) --> (
    topology(X, T) /\
      ∀(A, clopen(X, T, A) ==> ((A === emptySet) \/ (A === X)))
  )

  /**
   * Intermediate value theorem
   *
   * The image of a connected space by a continuous, surjective mapping is a connected space
   */
  val intermediateValueThm = Theorem((connectedTop(X, T1), continuous(f, X, T1, Y, T2), surjective(f, X, Y)) |- connectedTop(Y, T2)) {
    assume(connectedTop(X, T1), continuous(f, X, T1, Y, T2), surjective(f, X, Y))
    val xIsTop = have(topology(X, T1)) by Tautology.from(continuous.definition, mapping.definition)
    val yIsTop = have(topology(Y, T2)) by Tautology.from(continuous.definition, mapping.definition)

    val xIsConnected = have(∀(A, clopen(X, T1, A) ==> ((A === emptySet) \/ (A === X)))) by Tautology.from(connectedTop.definition of (T := T1))
    val isContinuous = have(∀(O, O ∈ T2 ==> preimage(f, X, Y, O) ∈ T1)) by Tautology.from(continuous.definition)

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

    val allClopen = thenHave(∀(A, clopen(Y, T2, A) ==> ((A === emptySet) \/ (A === Y)))) by RightForall
    have(connectedTop(Y, T2)) by Tautology.from(allClopen, yIsTop, connectedTop.definition of (X := Y, T := T2))
  }
}
