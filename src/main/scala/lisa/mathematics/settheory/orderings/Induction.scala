package lisa.mathematics
package settheory
package orderings

import lisa.automation.kernel.OLPropositionalSolver.Tautology
import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.settheory.SetTheoryTactics.*
import lisa.kernel.proof.SequentCalculus as SC
import lisa.mathematics.fol.Quantifiers.*
import lisa.mathematics.settheory.SetTheory.*
import lisa.mathematics.settheory.orderings.InclusionOrders.*
import lisa.mathematics.settheory.orderings.Ordinals.*
import lisa.mathematics.settheory.orderings.PartialOrders.*
import lisa.mathematics.settheory.orderings.Segments.*
import lisa.mathematics.settheory.orderings.WellOrders.*
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib
import lisa.prooflib.Substitution
import lisa.utils.FOLPrinter

object Induction extends lisa.Main {

  // var defs
  private val w = variable
  private val x = variable
  private val y = variable
  private val z = variable
  private val h = formulaVariable
  private val t = variable
  private val a = variable
  private val b = variable
  private val c = variable
  private val d = variable

  // relation and function symbols
  private val r = variable
  private val p = variable
  private val q = variable
  private val f = variable
  private val g = variable
  private val F = function(1)
  private val G = function(2)

  private val P = predicate(1)
  private val Q = predicate(1)
  private val schemPred = predicate(1)

  /**
   * Theorem --- Well Ordered Induction on a Subclass
   *
   * If `p` is a strict well-ordering, and `Q` is a subclass of the base set of
   * `p`, called `A`, then
   *
   *     `\forall x \in A. (A |^ x) \subseteq Q ==> x \in Q |- A = Q`
   *
   * i.e., if `Q` is a subclass of `A`, and the property `Q` passes to `x` from
   * its initial segment, then `A` is `Q`.
   */
  val wellOrderedInductionSubclass = Theorem(
    {
      val A = firstInPair(p)
      (
        wellOrder(p),
        forall(x, Q(x) ==> in(x, A)),
        forall(x, in(x, A) ==> (forall(y, in(y, initialSegment(p, x)) ==> Q(y)) ==> Q(x)))
      )
        |- forall(x, Q(x) <=> in(x, A))
    }
  ) {
    // renaming
    val A = firstInPair(p)
    val `<p` = secondInPair(p)

    // proof assumptions
    assume(
      wellOrder(p),
      forall(x, Q(x) ==> in(x, A)),
      forall(x, in(x, A) ==> (forall(y, in(y, initialSegment(p, x)) ==> Q(y)) ==> Q(x)))
    )

    // assume, towards a contradiction
    val contra = !forall(x, Q(x) <=> in(x, A))
    assume(contra)

    val contraDis = have(exists(x, (Q(x) /\ !in(x, A)) \/ (!Q(x) /\ in(x, A)))) by Restate

    val lhs = have(Q(x) /\ !in(x, A) |- ()) subproof {
      have(Q(x) ==> in(x, A)) by InstantiateForall
      thenHave(thesis) by Tautology
    }

    val rhs = have(!Q(x) /\ in(x, A) |- ()) subproof {
      val zDef = forall(t, in(t, z) <=> (in(t, A) /\ !Q(t)))

      // z exists by comprehension
      val zExists = have(exists(z, zDef)) subproof {
        have(existsOne(z, zDef)) by UniqueComprehension(A, lambda(Seq(t, x), !Q(t)))
        have(thesis) by Cut(lastStep, existsOneImpliesExists of P -> lambda(z, zDef))
      }

      // z is a subset of A
      val zSubset = have(zDef |- subset(z, A)) subproof {
        have(zDef |- in(t, z) <=> (in(t, A) /\ !Q(t))) by InstantiateForall
        thenHave(zDef |- in(t, z) ==> in(t, A)) by Weakening
        thenHave(zDef |- forall(t, in(t, z) ==> in(t, A))) by RightForall
        have(thesis) by Tautology.from(lastStep, subsetAxiom of (x -> z, y -> A))
      }

      // there exists a least element y in z
      val yDef = in(y, z) /\ forall(w, (!Q(w) /\ in(w, A)) ==> (in(pair(y, w), `<p`) \/ (y === w)))
      val yExists = have((zDef, !Q(x) /\ in(x, A)) |- exists(y, yDef)) subproof {
        assume(zDef, !Q(x) /\ in(x, A))
        have(in(x, z) <=> (in(x, A) /\ !Q(x))) by InstantiateForall
        thenHave(in(x, z)) by Tautology
        val zNonEmpty = have(!(z === emptySet())) by Tautology.from(lastStep, setWithElementNonEmpty of (y -> x, x -> z))

        have(forall(b, (subset(b, A) /\ !(b === emptySet())) ==> exists(y, in(y, b) /\ forall(w, in(w, b) ==> (in(pair(y, w), `<p`) \/ (y === w)))))) by Tautology.from(wellOrder.definition)
        thenHave((subset(z, A) /\ !(z === emptySet())) ==> exists(y, in(y, z) /\ forall(w, in(w, z) ==> (in(pair(y, w), `<p`) \/ (y === w))))) by InstantiateForall(z)

        val exY = have(exists(y, in(y, z) /\ forall(w, in(w, z) ==> (in(pair(y, w), `<p`) \/ (y === w))))) by Tautology.from(lastStep, zNonEmpty, zSubset)

        // tiny proof inside quantifiers
        have(in(w, z) <=> (in(w, A) /\ !Q(w))) by InstantiateForall
        thenHave(in(w, z) ==> (in(pair(y, w), `<p`) \/ (y === w)) |- (!Q(w) /\ in(w, A)) ==> (in(pair(y, w), `<p`) \/ (y === w))) by Tautology
        thenHave(forall(w, in(w, z) ==> (in(pair(y, w), `<p`) \/ (y === w))) |- (!Q(w) /\ in(w, A)) ==> (in(pair(y, w), `<p`) \/ (y === w))) by LeftForall
        thenHave(forall(w, in(w, z) ==> (in(pair(y, w), `<p`) \/ (y === w))) |- forall(w, (!Q(w) /\ in(w, A)) ==> (in(pair(y, w), `<p`) \/ (y === w)))) by RightForall
        thenHave(in(y, z) /\ forall(w, in(w, z) ==> (in(pair(y, w), `<p`) \/ (y === w))) |- in(y, z) /\ forall(w, (!Q(w) /\ in(w, A)) ==> (in(pair(y, w), `<p`) \/ (y === w)))) by Tautology
        thenHave(
          in(y, z) /\ forall(w, in(w, z) ==> (in(pair(y, w), `<p`) \/ (y === w))) |- exists(y, in(y, z) /\ forall(w, (!Q(w) /\ in(w, A)) ==> (in(pair(y, w), `<p`) \/ (y === w))))
        ) by RightExists
        thenHave(
          exists(y, in(y, z) /\ forall(w, in(w, z) ==> (in(pair(y, w), `<p`) \/ (y === w)))) |- exists(y, in(y, z) /\ forall(w, (!Q(w) /\ in(w, A)) ==> (in(pair(y, w), `<p`) \/ (y === w))))
        ) by LeftExists

        have(exists(y, in(y, z) /\ forall(w, (!Q(w) /\ in(w, A)) ==> (in(pair(y, w), `<p`) \/ (y === w))))) by Tautology.from(lastStep, exY)
      }

      // elements of the initial segment of A wrt y satisfy Q
      val yInitInQ = have((zDef, yDef) |- forall(w, in(w, initialSegment(p, y)) ==> Q(w))) subproof {
        assume(zDef, yDef)

        // TODO: assumptions annoy instantiations of external imports, so this is done rather verbosely here
        // see https://github.com/epfl-lara/lisa/issues/161
        have(forall(z, (z === initialSegment(p, y)) <=> forall(t, in(t, z) <=> (in(t, A) /\ in(pair(t, y), `<p`))))) by Weakening(initialSegment.definition of (a -> y))
        thenHave(forall(t, in(t, initialSegment(p, y)) <=> (in(t, A) /\ in(pair(t, y), `<p`)))) by InstantiateForall(initialSegment(p, y))
        val wInInit = thenHave((in(w, initialSegment(p, y)) <=> (in(w, A) /\ in(pair(w, y), `<p`)))) by InstantiateForall(w)

        have((in(w, A) /\ in(pair(w, y), `<p`)) |- Q(w)) subproof {
          assume((in(w, A) /\ in(pair(w, y), `<p`)), !Q(w))

          have(forall(w, (!Q(w) /\ in(w, A)) ==> (in(pair(y, w), `<p`) \/ (y === w)))) by Restate
          thenHave((!Q(w) /\ in(w, A)) ==> (in(pair(y, w), `<p`) \/ (y === w))) by InstantiateForall(w)
          val cases = thenHave((in(pair(y, w), `<p`) \/ (y === w))) by Tautology

          val rhs = have(!(y === w)) subproof {
            // well order is anti reflexive
            assume(y === w)
            have(in(pair(w, y), `<p`)) by Restate
            val ww = thenHave(in(pair(w, w), `<p`)) by Substitution.ApplyRules(y === w)

            have(∀(y, in(y, A) ==> !in(pair(y, y), `<p`))) subproof {
              have(antiReflexive(`<p`, A)) by Tautology.from(wellOrder.definition, totalOrder.definition, partialOrder.definition)
              have(thesis) by Tautology.from(lastStep, antiReflexive.definition of (r -> `<p`, x -> A))
            }

            thenHave(in(w, A) ==> !in(pair(w, w), `<p`)) by InstantiateForall(w)
            have(thesis) by Tautology.from(lastStep, ww)
          }

          val lhs = have(!in(pair(y, w), `<p`)) subproof {
            // well order is anti-symmetric
            assume(in(pair(y, w), `<p`))
            val yw = have(in(pair(y, w), `<p`) /\ in(pair(w, y), `<p`)) by Restate

            have(∀(y, ∀(w, (in(pair(y, w), `<p`) /\ in(pair(w, y), `<p`)) ==> (y === w)))) subproof {
              have(antiSymmetric(`<p`, A)) by Tautology.from(wellOrder.definition, totalOrder.definition, partialOrder.definition)
              have(thesis) by Tautology.from(lastStep, antiSymmetric.definition of (r -> `<p`, x -> A))
            }

            thenHave((in(pair(y, w), `<p`) /\ in(pair(w, y), `<p`)) ==> (y === w)) by InstantiateForall(y, w)
            have(thesis) by Tautology.from(lastStep, yw, rhs)
          }

          have(thesis) by Tautology.from(lhs, rhs, cases)
        }

        have(in(w, initialSegment(p, y)) ==> Q(w)) by Tautology.from(lastStep, wInInit)
        thenHave(thesis) by RightForall
      }

      // but if the initial segment of y is a subset of Q, then y is in Q
      val yInQ = have((zDef, yDef, in(y, A)) |- Q(y)) subproof {
        have(in(y, A) ==> (forall(w, in(w, initialSegment(p, y)) ==> Q(w)) ==> Q(y))) by InstantiateForall
        thenHave((in(y, A), (forall(w, in(w, initialSegment(p, y)) ==> Q(w)))) |- Q(y)) by Restate
        have(thesis) by Cut(yInitInQ, lastStep)
      }

      // however, we know y is in z, so !Q(y), hence contradiction
      have((zDef, yDef) |- ()) subproof {
        assume(zDef, yDef)
        val ynotQ = have(in(y, z) <=> (in(y, A) /\ !Q(y))) by InstantiateForall
        have(in(y, z)) by Restate
        have(thesis) by Tautology.from(lastStep, ynotQ, yInQ)
      }

      thenHave((zDef, exists(y, yDef)) |- ()) by LeftExists
      have((zDef, !Q(x) /\ in(x, A)) |- ()) by Cut(yExists, lastStep)
      thenHave((exists(z, zDef), !Q(x) /\ in(x, A)) |- ()) by LeftExists
      have(thesis) by Cut(zExists, lastStep)
    }

    have(((Q(x) /\ !in(x, A)) \/ (!Q(x) /\ in(x, A))) |- ()) by Tautology.from(lhs, rhs)
    thenHave(exists(x, (Q(x) /\ !in(x, A)) \/ (!Q(x) /\ in(x, A))) |- ()) by LeftExists

    have(thesis) by Tautology.from(lastStep, contraDis)
  }

  /**
   * Theorem --- Well Ordered Induction
   *
   * If `p` is a strict well-ordering, `Q` is a class, and `A` the base set of
   * `p`, then
   *
   *     `∀ x ∈ A. (A |^ x) ⊆ Q ==> x ∈ Q |- ∀ x ∈ A. x ∈ Q`
   *
   * i.e., if the property `Q` passes to `x` from its initial segment, then `Q`
   * holds for every element of `A`.
   */
  val wellOrderedInduction = Theorem(
    {
      val A = firstInPair(p)
      (
        wellOrder(p),
        forall(x, in(x, A) ==> (forall(y, in(y, initialSegment(p, x)) ==> Q(y)) ==> Q(x)))
      )
        |- forall(x, in(x, A) ==> Q(x))
    }
  ) {
    val A = firstInPair(p)
    val `<p` = secondInPair(p)

    assume(
      wellOrder(p),
      forall(x, in(x, A) ==> (forall(y, in(y, initialSegment(p, x)) ==> Q(y)) ==> Q(x)))
    )

    // make a subclass out of Q by intersecting with A
    def prop(x: Term): Formula = Q(x) /\ in(x, A)

    have(prop(x) ==> in(x, A)) by Restate
    val subclassProp = thenHave(forall(x, prop(x) ==> in(x, A))) by Restate

    have(forall(x, in(x, A) ==> (forall(y, in(y, initialSegment(p, x)) ==> prop(y)) ==> prop(x)))) subproof {
      have(in(x, A) ==> (forall(y, in(y, initialSegment(p, x)) ==> Q(y)) ==> Q(x))) by InstantiateForall
      val fy = thenHave(in(x, A) |- (forall(y, in(y, initialSegment(p, x)) ==> Q(y)) ==> Q(x))) by Restate
      // have(forall(y, in(y, initialSegment(p, x)) ==> Q(y)) |- (in(y, initialSegment(p, x)) ==> Q(y))) by InstantiateForall
      // val inst = have(in(x, A) |- (in(y, initialSegment(p, x)) ==> Q(y)) ==> Q(x)) by Tautology.from(lastStep, fy)

      have(in(y, initialSegment(p, x)) |- in(y, A)) subproof {
        have(forall(z, (z === initialSegment(p, x)) <=> forall(t, in(t, z) <=> (in(t, A) /\ in(pair(t, x), `<p`))))) by Weakening(initialSegment.definition of (a -> x))
        thenHave(forall(t, in(t, initialSegment(p, x)) <=> (in(t, A) /\ in(pair(t, x), `<p`)))) by InstantiateForall(initialSegment(p, x))
        thenHave((in(y, initialSegment(p, x)) <=> (in(y, A) /\ in(pair(y, x), `<p`)))) by InstantiateForall(y)
        thenHave(thesis) by Tautology
      }

      have((in(y, initialSegment(p, x)) ==> Q(y)) <=> (in(y, initialSegment(p, x)) ==> prop(y))) by Tautology.from(lastStep)
      thenHave(forall(y, (in(y, initialSegment(p, x)) ==> Q(y)) <=> (in(y, initialSegment(p, x)) ==> prop(y)))) by RightForall
      have(forall(y, in(y, initialSegment(p, x)) ==> Q(y)) <=> forall(y, in(y, initialSegment(p, x)) ==> prop(y))) by Cut(
        lastStep,
        universalEquivalenceDistribution of (P -> lambda(y, in(y, initialSegment(p, x)) ==> Q(y)), Q -> lambda(y, in(y, initialSegment(p, x)) ==> prop(y)))
      )

      have(in(x, A) |- forall(y, in(y, initialSegment(p, x)) ==> prop(y)) ==> prop(x)) by Tautology.from(lastStep, fy)
      thenHave(in(x, A) ==> (forall(y, in(y, initialSegment(p, x)) ==> prop(y)) ==> prop(x))) by Restate
      thenHave(thesis) by RightForall
    }

    have(forall(x, in(x, A) <=> prop(x))) by Tautology.from(lastStep, subclassProp, wellOrderedInductionSubclass of Q -> lambda(x, prop(x)))
    thenHave(in(x, A) <=> prop(x)) by InstantiateForall(x)
    thenHave(in(x, A) ==> Q(x)) by Tautology
    thenHave(thesis) by RightForall
  }

  val transfiniteInduction = Theorem(
    forall(x, ordinal(x) ==> (forall(y, in(y, x) ==> Q(y)) ==> Q(x))) |- forall(x, ordinal(x) ==> Q(x))
  ) {

    assume(forall(x, ordinal(x) ==> (forall(y, in(y, x) ==> Q(y)) ==> Q(x))))
    assume(exists(x, ordinal(x) /\ !Q(x))) // negated conclusion

    // we assume the negated conjecture and derive a contradiction

    // prop := On \ Q
    def prop(x: Term) = ordinal(x) /\ !Q(x)

    // there is a minimal element in prop
    val yDef = prop(y) /\ forall(x, prop(x) ==> in(y, x))

    have(prop(x) ==> ordinal(x)) by Restate
    thenHave(forall(x, prop(x) ==> ordinal(x)))
    val yExists = have(exists(y, yDef)) by Tautology.from(lastStep, ordinalSubclassHasMinimalElement of (P -> lambda(x, prop(x))))

    // so everything less than y is not in prop
    val fz = have(yDef |- forall(z, in(z, y) ==> !prop(z))) subproof {
      assume(yDef)

      // assume z \in y
      // but \forall x. prop(x) ==> y \in x
      // so prop(z) ==> y \in z
      have(forall(x, prop(x) ==> in(y, x))) by Restate
      thenHave(prop(z) ==> in(y, z)) by InstantiateForall(z)

      // but inclusion is anti symmetric (regularity)
      have(in(z, y) |- !prop(z)) by Tautology.from(lastStep, inclusionAntiSymmetric of (x -> z, y -> y))
      thenHave(in(z, y) ==> !prop(z)) by Restate
      thenHave(thesis) by RightForall
    }

    // but by assumption, this must mean Q(y)
    have(yDef |- Q(y)) subproof {
      assume(yDef)
      have(forall(z, in(z, y) ==> !prop(z))) by Restate.from(fz)
      thenHave(in(z, y) ==> !prop(z)) by InstantiateForall(z)
      have(in(z, y) ==> Q(z)) by Tautology.from(lastStep, elementsOfOrdinalsAreOrdinals of (b -> z, a -> y))
      val zy = thenHave(forall(z, in(z, y) ==> Q(z))) by RightForall
      have(ordinal(y) ==> (forall(z, in(z, y) ==> Q(z)) ==> Q(y))) by InstantiateForall
      have(thesis) by Tautology.from(zy, lastStep)
    }

    // contradiction
    thenHave(yDef |- ()) by Tautology
    thenHave(exists(y, yDef) |- ()) by LeftExists
    have(() |- ()) by Cut(yExists, lastStep)
    thenHave(thesis) by Restate
  }

  val minimalOrdinalCounterexample = Theorem(
    exists(x, ordinal(x) /\ !Q(x)) |- exists(x, ordinal(x) /\ !Q(x) /\ forall(y, in(y, x) ==> Q(y)))
  ) {
    have(thesis) by Restate.from(transfiniteInduction)
  }
}
