package lisa.maths.topology

import lisa.automation.settheory.SetTheoryTactics.*
import lisa.maths.Quantifiers.*

import lisa.automation.kernel.CommonTactics.Definition

import lisa.maths.topology.Topology.*
import lisa.maths.topology.Continuity.*
import lisa.maths.settheory.*
import lisa.maths.settheory.SetTheory.*
import lisa.maths.settheory.SetTheoryBasics.*
import lisa.automation.kernel.CommonTactics.*
import lisa.automation.settheory.SetTheoryTactics.UniqueComprehension
import lisa.automation.settheory.SetTheoryTactics.TheConditional
import lisa.maths.settheory.functions.Functionals.*
import lisa.maths.settheory.functions.DirectPreimages.*

object Compactness extends lisa.Main {
  // var defs
  private val x, y, z, a, b, c, t, p, f, r, s = variable
  private val X, T, T1, T2 = variable
  private val S, A, B, Y, o, O, O2, O3 = variable

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

      thenHave(
        subset(O3, preimages(f, X, Y, O)) /\ cover(X, O3) /\ finite(O3)
          |-
          ∃(O2, subset(O2, O) /\ cover(Y, O2) /\ finite(O2))
      ) by RightExists

      // Concluding
      thenHave(∃(O3, subset(O3, preimages(f, X, Y, O)) /\ cover(X, O3) /\ finite(O3)) |- ∃(O2, subset(O2, O) /\ cover(Y, O2) /\ finite(O2))) by LeftExists
      have(thesis) by Tautology.from(lastStep, existsO3)
    }
    thenHave(openCover(Y, T2, O) ==> ∃(O2, subset(O2, O) /\ cover(Y, O2) /\ finite(O2))) by Tautology
    val yIsCompact = thenHave(forall(O, openCover(Y, T2, O) ==> ∃(O2, subset(O2, O) /\ cover(Y, O2) /\ finite(O2)))) by RightForall

    have(thesis) by Tautology.from(yIsCompact, yIsTop, compact.definition of (X := Y, T := T2))
  }
}
