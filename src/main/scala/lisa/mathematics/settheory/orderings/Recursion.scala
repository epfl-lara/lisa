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
import lisa.mathematics.settheory.orderings.Induction.*
import lisa.mathematics.settheory.orderings.Ordinals.*
import lisa.mathematics.settheory.orderings.PartialOrders.*
import lisa.mathematics.settheory.orderings.Segments.*
import lisa.mathematics.settheory.orderings.WellOrders.*
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib
import lisa.prooflib.Substitution
import lisa.utils.FOLPrinter

/**
 * This file is dedicated to proving the well-ordered and transfinite recursion
 * theorems. Auxiliary lemmas are sections of the recursion proof separated out
 * for readability and faster compilation.
 */
object Recursion extends lisa.Main {

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
  private val t1 = variable
  private val t2 = variable

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

  // Recursion related definitions:
  val p1 = firstInPair(p)
  val p2 = secondInPair(p)

  /**
   * Lemma --- the well order `p` under consideration is a partial order
   */
  val pIsAPartialOrder = Lemma(
    wellOrder(p) |- partialOrder(p)
  ) {
    have(thesis) by Tautology.from(wellOrder.definition, totalOrder.definition)
  }

  /**
   * Lemma --- the well order `p` under consideration is a total order
   */
  val pIsATotalOrder = Lemma(
    wellOrder(p) |- totalOrder(p)
  ) {
    have(thesis) by Tautology.from(wellOrder.definition)
  }

  // Well-Ordered Recursion

  // superficial abbreviations
  def fun(g: Term, t: Term): Formula = (functionalOver(g, initialSegment(p, t)) /\ forall(a, in(a, initialSegment(p, t)) ==> (app(g, a) === F(orderedRestriction(g, a, p)))))
  def prop(t: Term): Formula = in(t, p1) /\ existsOne(g, fun(g, t))

  // Lemmas:

  /**
   * Theorem --- Unique Recursive Function
   *
   * If a theorem as defined by [[wellOrderedRecursion]] exists, it is unique
   */
  val uniqueRecursiveFunction = Lemma(
    wellOrder(p) /\ exists(g, fun(g, t)) /\ in(t, p1) |- existsOne(g, fun(g, t))
  ) {
    assume(wellOrder(p))
    assume(in(t, p1))

    // pt is a well order over t, which is needed for induction
    val pt = pair(initialSegment(p, t), initialSegmentOrder(p, t))
    val ptWO = have(wellOrder(pt)) by Weakening(initialSegmentWellOrdered of a -> t)

    // suppose there exist two such distinct functions g1 and g2
    val g1 = variable
    val g2 = variable

    // expansion of ordered restriction
    val ordResDef = have(orderedRestriction(g, z, p) === restrictedFunction(g, initialSegment(p, z))) subproof {
      have(forall(b, (b === orderedRestriction(g, z, p)) <=> (b === restrictedFunction(g, initialSegment(p, z))))) by Weakening(orderedRestriction.definition of (f -> g, a -> z))
      thenHave(thesis) by InstantiateForall(orderedRestriction(g, z, p))
    }

    // if g1 and g2 agree on the initial segment of an element < z, they must agree on z
    val initToz = have(
      fun(g1, t) /\ fun(g2, t) /\ !(g1 === g2) /\ in(z, initialSegment(p, t)) /\ forall(
        b,
        in(b, initialSegment(pt, z)) ==> (app(g1, b) === app(g2, b))
      ) |- (app(g1, z) === app(g2, z))
    ) subproof {
      assume(fun(g1, t))
      assume(fun(g2, t))
      assume(!(g1 === g2))
      assume(in(z, initialSegment(p, t)))
      assume(forall(b, in(b, initialSegment(pt, z)) ==> (app(g1, b) === app(g2, b))))

      // the ordered restriction of g1 has domain initialSegment(p, z)
      // it is functional, too
      val restrictionIsFunction = have(fun(g, t) |- functionalOver(orderedRestriction(g, z, p), initialSegment(p, z))) subproof {
        assume(fun(g, t))

        // g_z has dom <z \cup dom g
        val domrestriction = have(functionalOver(orderedRestriction(g, z, p), setIntersection(initialSegment(p, z), relationDomain(g)))) subproof {
          have(functionalOver(restrictedFunction(g, initialSegment(p, z)), setIntersection(initialSegment(p, z), relationDomain(g)))) by Tautology.from(
            restrictedFunctionIsFunctionalOver of (f -> g, x -> initialSegment(p, z)),
            functionalOver.definition of (f -> g, x -> initialSegment(p, t))
          )
          thenHave(thesis) by Substitution.ApplyRules(ordResDef)
        }

        // but dom g is <t
        val domgz = have(functionalOver(orderedRestriction(g, z, p), setIntersection(initialSegment(p, z), initialSegment(p, t)))) subproof {
          have(functionalOver(g, initialSegment(p, t))) by Tautology
          have(relationDomain(g) === initialSegment(p, t)) by Tautology.from(lastStep, functionalOverImpliesDomain of (f -> g, x -> initialSegment(p, t)))

          have(thesis) by Substitution.ApplyRules(lastStep)(domrestriction)
        }

        // <z \subseteq <t
        have(subset(initialSegment(p, z), initialSegment(p, t))) subproof {
          have(forall(z, (z === initialSegment(p, t)) <=> forall(b, in(b, z) <=> (in(b, p1) /\ in(pair(b, t), p2))))) by Weakening(initialSegment.definition of a -> t)
          thenHave(forall(b, in(b, initialSegment(p, t)) <=> (in(b, p1) /\ in(pair(b, t), p2)))) by InstantiateForall(initialSegment(p, t))
          thenHave(in(z, initialSegment(p, t)) <=> (in(z, p1) /\ in(pair(z, t), p2))) by InstantiateForall(z)
          val zLTt = thenHave(in(pair(z, t), p2)) by Tautology

          have(partialOrder(p)) by Tautology.from(wellOrder.definition, totalOrder.definition)

          have(thesis) by Tautology.from(lastStep, zLTt, initialSegmentsSubset of (x -> z, y -> t), pIsAPartialOrder)
        }

        // so dom g = <z
        have(setIntersection(initialSegment(p, z), initialSegment(p, t)) === initialSegment(p, z)) by Tautology.from(
          lastStep,
          intersectionOfSubsets of (x -> initialSegment(p, z), y -> initialSegment(p, t))
        )

        have(thesis) by Substitution.ApplyRules(lastStep)(domgz)
      }

      // the double initial segment is redundant
      val initPTEqual = have(initialSegment(pt, z) === initialSegment(p, z)) subproof {

        // expand defs
        have(forall(z, (z === initialSegment(x, y)) <=> forall(t, in(t, z) <=> (in(t, firstInPair(x)) /\ in(pair(t, y), secondInPair(x)))))) by Weakening(
          initialSegment.definition of (p -> x, a -> y)
        )
        thenHave(forall(t, in(t, initialSegment(x, y)) <=> (in(t, firstInPair(x)) /\ in(pair(t, y), secondInPair(x))))) by InstantiateForall(initialSegment(x, y))
        val initXY = thenHave(in(c, initialSegment(x, y)) <=> (in(c, firstInPair(x)) /\ in(pair(c, y), secondInPair(x)))) by InstantiateForall(c)

        // forward
        val fwd = have(in(b, initialSegment(pt, z)) |- in(b, initialSegment(p, z))) subproof {
          assume(in(b, initialSegment(pt, z)))

          have(in(b, firstInPair(pt))) by Tautology.from(initXY of (x -> pt, y -> z, c -> b))
          val bpt = thenHave(in(b, initialSegment(p, t))) by Substitution.ApplyRules(firstInPairReduction of (x -> initialSegment(p, t), y -> initialSegmentOrder(p, t)))
          have(in(b, initialSegment(p, t)) ==> in(b, p1)) by Tautology.from(initXY of (x -> p, y -> t, c -> b))
          val bInP1 = have(in(b, p1)) by Tautology.from(lastStep, bpt)

          val bzInP2 = have(in(pair(b, z), p2)) subproof {
            have(in(z, initialSegment(p, t))) by Restate
            val zt = have(in(pair(z, t), p2)) by Tautology.from(lastStep, initXY of (x -> p, y -> t, c -> z))

            have(in(pair(b, z), secondInPair(pt))) by Tautology.from(initXY of (x -> pt, y -> z, c -> b))
            val bzpt = thenHave(in(pair(b, z), initialSegmentOrder(p, t))) by Substitution.ApplyRules(secondInPairReduction of (x -> initialSegment(p, t), y -> initialSegmentOrder(p, t)))

            have(thesis) subproof {
              have(
                forall(
                  z,
                  (z === initialSegmentOrder(p, t)) <=> forall(a, in(a, z) <=> (in(a, secondInPair(p)) /\ (in(firstInPair(a), initialSegment(p, t)) /\ in(secondInPair(a), initialSegment(p, t)))))
                )
              ) by Weakening(initialSegmentOrder.definition of a -> t)
              thenHave(
                forall(a, in(a, initialSegmentOrder(p, t)) <=> (in(a, secondInPair(p)) /\ (in(firstInPair(a), initialSegment(p, t)) /\ in(secondInPair(a), initialSegment(p, t)))))
              ) by InstantiateForall(initialSegmentOrder(p, t))
              thenHave(
                in(pair(b, z), initialSegmentOrder(p, t)) <=> (in(pair(b, z), secondInPair(p)) /\ (in(firstInPair(pair(b, z)), initialSegment(p, t)) /\ in(
                  secondInPair(pair(b, z)),
                  initialSegment(p, t)
                )))
              ) by InstantiateForall(pair(b, z))
              have(thesis) by Tautology.from(lastStep, bzpt)
            }
          }

          have(thesis) by Tautology.from(bInP1, bzInP2, initXY of (x -> p, y -> z, c -> b))
        }

        // backward
        val bwd = have(in(b, initialSegment(p, z)) |- in(b, initialSegment(pt, z))) subproof {
          assume(in(b, initialSegment(p, z)))

          val bpt = have(in(b, initialSegment(p, t))) subproof {
            val bInP1 = have(in(b, p1)) by Tautology.from(initXY of (x -> p, y -> z, c -> b))

            val bz = have(in(pair(b, z), p2)) by Tautology.from(initXY of (x -> p, y -> z, c -> b))
            val zt = have(in(pair(z, t), p2)) by Tautology.from(initXY of (x -> p, y -> t, c -> z))

            have(forall(w, forall(y, forall(z, (in(pair(w, y), p2) /\ in(pair(y, z), p2)) ==> in(pair(w, z), p2))))) by Weakening(wellOrderTransitivity)
            thenHave((in(pair(b, z), p2) /\ in(pair(z, t), p2)) ==> in(pair(b, t), p2)) by InstantiateForall(b, z, t)

            have(in(pair(b, t), p2)) by Tautology.from(lastStep, bz, zt)
            have(thesis) by Tautology.from(lastStep, bInP1, initXY of (x -> p, y -> t, c -> b))
          }

          val bzInP2 = have(in(pair(b, z), initialSegmentOrder(p, t))) subproof {
            have(
              forall(
                z,
                (z === initialSegmentOrder(p, t)) <=> forall(a, in(a, z) <=> (in(a, secondInPair(p)) /\ (in(firstInPair(a), initialSegment(p, t)) /\ in(secondInPair(a), initialSegment(p, t)))))
              )
            ) by Weakening(initialSegmentOrder.definition of a -> t)
            thenHave(
              forall(a, in(a, initialSegmentOrder(p, t)) <=> (in(a, secondInPair(p)) /\ (in(firstInPair(a), initialSegment(p, t)) /\ in(secondInPair(a), initialSegment(p, t)))))
            ) by InstantiateForall(initialSegmentOrder(p, t))
            thenHave(
              in(pair(b, z), initialSegmentOrder(p, t)) <=> (in(pair(b, z), secondInPair(p)) /\ (in(firstInPair(pair(b, z)), initialSegment(p, t)) /\ in(
                secondInPair(pair(b, z)),
                initialSegment(p, t)
              )))
            ) by InstantiateForall(pair(b, z))
            val ordDef = thenHave(in(pair(b, z), initialSegmentOrder(p, t)) <=> (in(pair(b, z), secondInPair(p)) /\ (in(b, initialSegment(p, t)) /\ in(z, initialSegment(p, t))))) by Substitution
              .ApplyRules(firstInPairReduction of (x -> b, y -> z), secondInPairReduction of (x -> b, y -> z))

            val bz = have(in(pair(b, z), p2)) by Tautology.from(initXY of (x -> p, y -> z, c -> b))
            have(thesis) by Tautology.from(ordDef, bz, bpt)
          }

          have(in(b, initialSegment(pt, z)) <=> (in(b, initialSegment(p, t)) /\ in(pair(b, z), initialSegmentOrder(p, t)))) by Substitution.ApplyRules(
            firstInPairReduction of (x -> initialSegment(p, t), y -> initialSegmentOrder(p, t)),
            secondInPairReduction of (x -> initialSegment(p, t), y -> initialSegmentOrder(p, t))
          )(initXY of (x -> pt, y -> z, c -> b))
          have(thesis) by Tautology.from(lastStep, bpt, bzInP2)
        }

        // combine
        have(in(b, initialSegment(p, z)) <=> in(b, initialSegment(pt, z))) by Tautology.from(fwd, bwd)
        thenHave(forall(b, in(b, initialSegment(p, z)) <=> in(b, initialSegment(pt, z)))) by RightForall
        have(thesis) by Tautology.from(lastStep, extensionalityAxiom of (x -> initialSegment(p, z), y -> initialSegment(pt, z)))
      }

      // on the restricted domain, app(orderedRestriction(g, z, p), b) = app(g, b)
      val ordApp = have(forall(b, in(b, initialSegment(pt, z)) ==> (app(orderedRestriction(g, z, p), b) === app(g, b)))) subproof {
        // b < z ==> g_z(b) = g(b)
        val bToApp = have(in(b, initialSegment(p, z)) ==> (app(orderedRestriction(g, z, p), b) === app(g, b))) subproof {
          have(in(b, initialSegment(p, z)) ==> (app(restrictedFunction(g, initialSegment(p, z)), b) === app(g, b))) by Tautology.from(
            restrictedFunctionApplication of (f -> g, x -> initialSegment(p, z), y -> b)
          )
          thenHave(thesis) by Substitution.ApplyRules(ordResDef)
        }

        // b <_t z ==> b < z
        val btTobz = have(in(b, initialSegment(pt, z)) ==> in(b, initialSegment(p, z))) subproof {
          have(in(b, initialSegment(pt, z)) ==> in(b, initialSegment(pt, z))) by Restate
          thenHave(thesis) by Substitution.ApplyRules(initPTEqual)
        }

        // so b <_t z ==> g_z(b) = g(b)
        have(in(b, initialSegment(pt, z)) ==> (app(orderedRestriction(g, z, p), b) === app(g, b))) by Tautology.from(bToApp, btTobz)

        // quantify
        thenHave(thesis) by RightForall
      }

      // for every element in the restricted domain, g1_z(b)  = g2_z(b)
      val eqOnDom = have(forall(b, in(b, initialSegment(pt, z)) ==> (app(orderedRestriction(g1, z, p), b) === app(orderedRestriction(g2, z, p), b)))) subproof {
        val unquantified = have(in(b, initialSegment(pt, z)) |- (app(orderedRestriction(g1, z, p), b) === app(orderedRestriction(g2, z, p), b))) subproof {
          assume(in(b, initialSegment(pt, z)))

          val instOrd = have((app(orderedRestriction(g, z, p), b) === app(g, b))) by InstantiateForall(b)(ordApp)

          val eqTg2zg1 = equalityTransitivity of (x -> app(orderedRestriction(g2, z, p), b), z -> app(orderedRestriction(g1, z, p), b), y -> app(g1, b))
          val eqTg1g2 = equalityTransitivity of (x -> app(orderedRestriction(g2, z, p), b), y -> app(g2, b), z -> app(g1, b))

          have(in(b, initialSegment(pt, z)) ==> (app(g1, b) === app(g2, b))) by InstantiateForall
          thenHave(app(g1, b) === app(g2, b)) by Tautology
          have(thesis) by Tautology.from(lastStep, instOrd of g -> g1, instOrd of g -> g2, eqTg2zg1, eqTg1g2)
        }

        thenHave(in(b, initialSegment(pt, z)) ==> (app(orderedRestriction(g1, z, p), b) === app(orderedRestriction(g2, z, p), b))) by Restate
        thenHave(thesis) by RightForall
      }

      // but then g1_z = g2_z
      val orderedRestrictionsEqual = have(orderedRestriction(g1, z, p) === orderedRestriction(g2, z, p)) subproof {
        have(fun(g, t) |- functionalOver(orderedRestriction(g, z, p), initialSegment(p, z))) by Restate.from(restrictionIsFunction)

        // but initialSegment pt z = initialSegment p z
        val fung = thenHave(fun(g, t) |- functionalOver(orderedRestriction(g, z, p), initialSegment(pt, z))) by Substitution.ApplyRules(initPTEqual)

        have(thesis) by Tautology.from(
          fung of g -> g1,
          fung of g -> g2,
          eqOnDom,
          functionsEqualIfEqualOnDomain of (f -> orderedRestriction(g1, z, p), g -> orderedRestriction(g2, z, p), a -> initialSegment(pt, z))
        )
      }

      // and thus F(g1_z) = F(g2_z)
      val fg1g2eq = have(F(orderedRestriction(g1, z, p)) === F(orderedRestriction(g2, z, p))) subproof {
        have(F(orderedRestriction(g1, z, p)) === F(orderedRestriction(g1, z, p))) by Restate
        thenHave(thesis) by Substitution.ApplyRules(orderedRestrictionsEqual)
      }

      // but then app(g1, z) = F (g1_z) = F(g1_z) = app(g2, z)
      have(thesis) subproof {
        val gzf = have(fun(g, t) |- app(g, z) === F(orderedRestriction(g, z, p))) subproof {
          assume(fun(g, t))
          have(forall(a, in(a, initialSegment(p, t)) ==> (app(g, a) === F(orderedRestriction(g, a, p))))) by Restate
          thenHave(in(z, initialSegment(p, t)) ==> (app(g, z) === F(orderedRestriction(g, z, p)))) by InstantiateForall(z)
          thenHave(thesis) by Tautology
        }

        // g1(z) = F(g1_z)
        val g1f = gzf of g -> g1

        // g2(z) = F(g2_z)
        val g2f = gzf of g -> g2

        // F(g1_z) = F(g2_z)
        // fg1g2eq

        val fg1fg2Tog1 = equalityTransitivity of (x -> F(orderedRestriction(g1, z, p)), y -> F(orderedRestriction(g2, z, p)), z -> app(g2, z))
        val g2fg2Tog1 = equalityTransitivity of (x -> app(g2, z), y -> F(orderedRestriction(g1, z, p)), z -> app(g1, z))

        // g1(z) = g2(z)
        have(thesis) by Tautology.from(fg1fg2Tog1, g2fg2Tog1, g1f, g2f, fg1g2eq)
      }
    }

    // thus, they must agree on the whole domain
    val eqZ = have(fun(g1, t) /\ fun(g2, t) /\ !(g1 === g2) |- forall(z, in(z, initialSegment(p, t)) ==> (app(g1, z) === app(g2, z)))) subproof {
      assume(fun(g1, t) /\ fun(g2, t) /\ !(g1 === g2))
      have(in(z, initialSegment(p, t)) |- forall(b, in(b, initialSegment(pt, z)) ==> (app(g1, b) === app(g2, b))) ==> (app(g1, z) === app(g2, z))) by Weakening(
        initToz
      )
      thenHave(
        in(z, firstInPair(pt)) |- forall(b, in(b, initialSegment(pt, z)) ==> (app(g1, b) === app(g2, b))) ==> (app(g1, z) === app(g2, z))
      ) by Substitution.ApplyRules(firstInPairReduction of (x -> initialSegment(p, t), y -> initialSegmentOrder(p, t)))
      thenHave(
        in(z, firstInPair(pt)) ==> (forall(b, in(b, initialSegment(pt, z)) ==> (app(g1, b) === app(g2, b))) ==> (app(g1, z) === app(g2, z)))
      ) by Restate
      thenHave(
        forall(z, in(z, firstInPair(pt)) ==> (forall(b, in(b, initialSegment(pt, z)) ==> (app(g1, b) === app(g2, b))) ==> (app(g1, z) === app(g2, z))))
      ) by RightForall
      have(
        forall(z, in(z, firstInPair(pt)) ==> (app(g1, z) === app(g2, z)))
      ) by Tautology.from(lastStep, ptWO, wellOrderedInduction of (p -> pt, Q -> lambda(x, app(g1, x) === app(g2, x))))
      thenHave(thesis) by Substitution.ApplyRules(firstInPairReduction of (x -> initialSegment(p, t), y -> initialSegmentOrder(p, t)))
    }

    // so g1 = g2, but this is a contradiction
    val contra = have(fun(g1, t) /\ fun(g2, t) /\ !(g1 === g2) |- ()) subproof {
      assume(fun(g1, t) /\ fun(g2, t) /\ !(g1 === g2))
      have((g1 === g2)) by Tautology.from(eqZ, functionsEqualIfEqualOnDomain of (f -> g1, g -> g2, a -> initialSegment(p, t)))
      thenHave(thesis) by Restate
    }

    // so there exists a unique one, if there exists one at all
    have(!exists(g, fun(g, t)) \/ existsOne(g, fun(g, t))) subproof {
      have(fun(g1, t) /\ fun(g2, t) /\ !(g1 === g2) |- ()) by Restate.from(contra)
      thenHave(exists(g2, fun(g1, t) /\ fun(g2, t) /\ !(g1 === g2)) |- ()) by LeftExists
      thenHave(exists(g1, exists(g2, fun(g1, t) /\ fun(g2, t) /\ !(g1 === g2))) |- ()) by LeftExists
      have(thesis) by Tautology.from(lastStep, atleastTwoExist of (P -> lambda(x, fun(x, t))))
    }

    thenHave(thesis) by Restate
  }

  // EXISTENCE ----------------------------------------

  // if there exists a unique function `g` for the initial segment of some `x`, get the set of these
  val wDef = forall(t, in(t, w) <=> exists(y, in(y, initialSegment(p, x)) /\ fun(t, y)))

  // take its union
  // this is a function `g` for `x` (almost)
  val uw = union(w) // + `(predecessor x, F(U w))` in the successor case

  // properties of w / uw

  val elemsFunctional = Lemma(
    wDef |-
      forall(t, in(t, w) ==> functional(t))
  ) {
    assume(wDef)
    have(in(t, w) |- functional(t)) subproof {
      assume(in(t, w))
      have(in(t, w) <=> exists(y, in(y, initialSegment(p, x)) /\ fun(t, y))) by InstantiateForall
      val exy = thenHave(exists(y, in(y, initialSegment(p, x)) /\ fun(t, y))) by Tautology

      have(exists(y, in(y, initialSegment(p, x)) /\ fun(t, y)) |- functional(t)) subproof {
        have(fun(t, y) |- functional(t)) by Tautology.from(functionalOver.definition of (f -> t, x -> initialSegment(p, y)))
        thenHave((in(y, initialSegment(p, x)) /\ fun(t, y)) |- functional(t)) by Weakening
        thenHave(thesis) by LeftExists
      }

      have(thesis) by Cut(exy, lastStep)
    }
    thenHave(in(t, w) ==> functional(t)) by Restate
    thenHave(thesis) by RightForall
  }

  val elemsSubset = Lemma(
    wellOrder(p) /\ wDef |-
      forall(t1, forall(t2, (in(t1, w) /\ in(t2, w)) ==> (subset(t1, t2) \/ subset(t2, t1))))
  ) {
    assume(wDef, wellOrder(p))

    have(in(t1, w) /\ in(t2, w) |- subset(t1, t2) \/ subset(t2, t1)) subproof {
      assume(in(t1, w))
      assume(in(t2, w))

      // given t1 and t2
      // they must come from y1 and y2

      // if t1 == t2
      // done
      val t1EQt2 = have((t1 === t2) |- subset(t1, t2) \/ subset(t2, t1)) by Weakening(subsetEqualitySymmetry of (x -> t1, y -> t2))

      // if t1 != t2
      val t1NEQt2 = have(!(t1 === t2) |- subset(t1, t2) \/ subset(t2, t1)) subproof {
        assume(!(t1 === t2))
        def ytDef(y: Term, t: Term) = in(y, initialSegment(p, x)) /\ fun(t, y)
        val y1 = variable
        val y2 = variable

        val initMemToP1 = have(in(y, initialSegment(p, a)) |- in(y, p1)) subproof {
          have(forall(y, in(y, initialSegment(p, a)) <=> (in(y, p1) /\ in(pair(y, a), p2)))) by InstantiateForall(initialSegment(p, a))(initialSegment.definition)
          thenHave(in(y, initialSegment(p, a)) <=> (in(y, p1) /\ in(pair(y, a), p2))) by InstantiateForall(y)
          thenHave(thesis) by Tautology
        }

        have(ytDef(y1, t1) /\ ytDef(y2, t2) |- subset(t1, t2) \/ subset(t2, t1)) subproof {
          assume(ytDef(y1, t1))
          assume(ytDef(y2, t2))
          // cases:
          // y1 == y2
          // done by the uniqueness lemma above
          val yeq = have((y1 === y2) |- subset(t1, t2)) subproof {
            assume(y1 === y2)
            have(fun(t1, y1) /\ fun(t2, y2)) by Restate
            thenHave(fun(t1, y1) /\ fun(t2, y1)) by Substitution.ApplyRules(y1 === y2)
            thenHave(fun(t1, y1) /\ fun(t2, y1) /\ !(t1 === t2)) by Tautology
            thenHave(exists(t2, fun(t1, y1) /\ fun(t2, y1) /\ !(t1 === t2))) by RightExists
            thenHave(exists(t1, exists(t2, fun(t1, y1) /\ fun(t2, y1) /\ !(t1 === t2)))) by RightExists
            have(exists(t1, fun(t1, y1)) /\ !existsOne(t1, fun(t1, y1))) by Tautology.from(lastStep, atleastTwoExist of P -> lambda(t1, fun(t1, y1)))
            have(bot()) by Tautology.from(lastStep, uniqueRecursiveFunction of t -> y1, initMemToP1 of (y -> y1, a -> x))
            thenHave(thesis) by Weakening
          }

          // y1 != y2
          // real work to be done here :-
          val neq = have(!(y1 === y2) |- subset(t1, t2) \/ subset(t2, t1)) subproof {
            assume(!(y1 === y2))

            // y1 < y2 or y2 < y1?
            // we prove it in the generic case
            val a1 = variable
            val a2 = variable
            val k1 = variable
            val k2 = variable
            val ltToSubset = have(ytDef(a1, k1) /\ ytDef(a2, k2) /\ in(pair(a1, a2), p2) |- subset(k1, k2)) subproof {
              assume(ytDef(a1, k1))
              assume(ytDef(a2, k2))
              assume(in(pair(a1, a2), p2))
              // fun(k1, a1)
              // fun(k2, a2)
              // a1 < a2
              // we should have k1 \subseteq k2

              // dom k1 \subseteq dom k2
              val domSubset =
                have(subset(initialSegment(p, a1), initialSegment(p, a2))) by Tautology.from(initialSegmentsSubset of (x -> a1, y -> a2), pIsAPartialOrder)

              // suppose there is a minimal n such that k1 n != k2 n
              val n = variable
              val nDef =
                in(n, initialSegment(p, a1)) /\ !(app(k1, n) === app(k2, n)) /\ forall(b, (in(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b))) ==> (in(pair(n, b), p2) \/ (n === b)))

              // if k1 and k2 disagree at all
              val k1k2disagree = exists(n, in(n, initialSegment(p, a1)) /\ !(app(k1, n) === app(k2, n)))

              val nExists = have(k1k2disagree |- exists(n, nDef)) subproof {
                assume(k1k2disagree)

                // B defined by x => x < a1 /\ k1 x != k2 x exists
                val B = variable
                val BDef = forall(x, in(x, B) <=> (in(x, initialSegment(p, a1)) /\ !(app(k1, x) === app(k2, x))))
                val BExists = have(exists(B, BDef)) by Weakening(comprehensionSchema of (z -> initialSegment(p, a1), sPhi -> lambda(Seq(x, z), !(app(k1, x) === app(k2, x)))))

                // B forms a subset of p1
                val subsetB = have(BDef |- subset(B, p1)) subproof {
                  assume(BDef)
                  have(in(y, B) <=> (in(y, initialSegment(p, a1)) /\ !(app(k1, y) === app(k2, y)))) by InstantiateForall
                  have(in(y, B) ==> in(y, p1)) by Tautology.from(lastStep, initMemToP1 of a -> a1)
                  thenHave(forall(y, in(y, B) ==> in(y, p1))) by RightForall
                  have(thesis) by Tautology.from(lastStep, subsetAxiom of (x -> B, y -> p1))
                }

                // B is non-empty
                val nonEmptyB = have(BDef |- !(B === emptySet())) subproof {
                  assume(BDef)
                  have(in(n, B) <=> (in(n, initialSegment(p, a1)) /\ !(app(k1, n) === app(k2, n)))) by InstantiateForall
                  thenHave((in(n, initialSegment(p, a1)) /\ !(app(k1, n) === app(k2, n))) |- in(n, B)) by Weakening
                  have((in(n, initialSegment(p, a1)) /\ !(app(k1, n) === app(k2, n))) |- !(B === emptySet())) by Cut(lastStep, setWithElementNonEmpty of (y -> n, x -> B))
                  thenHave(thesis) by LeftExists
                }

                // so it has a minimal element
                val minimalB = have(BDef |- exists(n, nDef)) subproof {
                  assume(BDef)
                  have(forall(B, (subset(B, p1) /\ !(B === emptySet())) ==> exists(n, in(n, B) /\ forall(b, in(b, B) ==> (in(pair(n, b), p2) \/ (n === b)))))) by Tautology.from(
                    wellOrder.definition
                  )
                  thenHave((subset(B, p1) /\ !(B === emptySet())) ==> exists(n, in(n, B) /\ forall(b, in(b, B) ==> (in(pair(n, b), p2) \/ (n === b))))) by InstantiateForall(B)
                  val exN = have(exists(n, in(n, B) /\ forall(b, in(b, B) ==> (in(pair(n, b), p2) \/ (n === b))))) by Tautology.from(lastStep, nonEmptyB, subsetB)

                  // transform n \in B to n < a1 /\ k1 n != k2 n
                  have(in(b, B) <=> (in(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b)))) by InstantiateForall
                  thenHave(
                    (in(b, B) ==> (in(pair(n, b), p2) \/ (n === b))) <=> ((in(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b))) ==> (in(pair(n, b), p2) \/ (n === b)))
                  ) by Tautology
                  thenHave(
                    forall(b, (in(b, B) ==> (in(pair(n, b), p2) \/ (n === b))) <=> ((in(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b))) ==> (in(pair(n, b), p2) \/ (n === b))))
                  ) by RightForall
                  val bEq = have(
                    forall(b, in(b, B) ==> (in(pair(n, b), p2) \/ (n === b))) <=> forall(
                      b,
                      (in(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b))) ==> (in(pair(n, b), p2) \/ (n === b))
                    )
                  ) by Tautology.from(
                    lastStep,
                    universalEquivalenceDistribution of (P -> lambda(b, in(b, B) ==> (in(pair(n, b), p2) \/ (n === b))), Q -> lambda(
                      b,
                      (in(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b))) ==> (in(pair(n, b), p2) \/ (n === b))
                    ))
                  )

                  have(in(n, B) <=> (in(n, initialSegment(p, a1)) /\ !(app(k1, n) === app(k2, n)))) by InstantiateForall
                  have(
                    (in(n, B) /\ forall(b, in(b, B) ==> (in(pair(n, b), p2) \/ (n === b)))) <=> (in(n, initialSegment(p, a1)) /\ !(app(k1, n) === app(k2, n)) /\ forall(
                      b,
                      (in(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b))) ==> (in(pair(n, b), p2) \/ (n === b))
                    ))
                  ) by Tautology.from(lastStep, bEq)
                  thenHave(
                    forall(
                      n,
                      (in(n, B) /\ forall(b, in(b, B) ==> (in(pair(n, b), p2) \/ (n === b)))) <=> (in(n, initialSegment(p, a1)) /\ !(app(k1, n) === app(k2, n)) /\ forall(
                        b,
                        (in(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b))) ==> (in(pair(n, b), p2) \/ (n === b))
                      ))
                    )
                  ) by RightForall

                  have(thesis) by Tautology.from(
                    lastStep,
                    exN,
                    existentialEquivalenceDistribution of (P -> lambda(n, (in(n, B) /\ forall(b, in(b, B) ==> (in(pair(n, b), p2) \/ (n === b))))), Q -> lambda(
                      n,
                      (in(n, initialSegment(p, a1)) /\ !(app(k1, n) === app(k2, n)) /\ forall(
                        b,
                        (in(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b))) ==> (in(pair(n, b), p2) \/ (n === b))
                      ))
                    ))
                  )
                }

                thenHave(exists(B, BDef) |- exists(n, nDef)) by LeftExists
                have(thesis) by Cut(BExists, lastStep)
              }

              // but k1 n == F(k1 |^ n) and k2 n == F(k2 |^ n)
              val fK1 = have(nDef |- app(k1, n) === F(orderedRestriction(k1, n, p))) subproof {
                // n < a1 ==> k1 n = F(k1 |^ n)
                have(forall(b, in(b, initialSegment(p, a1)) ==> (app(k1, b) === F(orderedRestriction(k1, b, p))))) by Tautology
                thenHave(in(n, initialSegment(p, a1)) ==> (app(k1, n) === F(orderedRestriction(k1, n, p)))) by InstantiateForall(n)

                // we know n < a1, so result
                thenHave(thesis) by Tautology
              }
              val fK2 = have(nDef |- app(k2, n) === F(orderedRestriction(k2, n, p))) subproof {
                // n < a2 ==> k2 n = F(k2 |^ n)
                have(forall(b, in(b, initialSegment(p, a2)) ==> (app(k2, b) === F(orderedRestriction(k2, b, p))))) by Tautology
                val impl = thenHave(in(n, initialSegment(p, a2)) ==> (app(k2, n) === F(orderedRestriction(k2, n, p)))) by InstantiateForall(n)

                // n < a1 and a1 < a2, so n < a2
                have(forall(b, in(b, initialSegment(p, a1)) ==> in(b, initialSegment(p, a2)))) by Tautology.from(
                  domSubset,
                  subsetAxiom of (x -> initialSegment(p, a1), y -> initialSegment(p, a2))
                )
                thenHave(in(n, initialSegment(p, a1)) ==> in(n, initialSegment(p, a2))) by InstantiateForall(n)

                // so result
                have(thesis) by Tautology.from(lastStep, impl)
              }

              // k1 |^ n  == k2 |^ n by minimality of n
              // so F(k1 |^ n) == F(k2 |^ n)
              val ordResEq = have(nDef |- F(orderedRestriction(k1, n, p)) === F(orderedRestriction(k2, n, p))) subproof {
                assume(nDef)

                val k1k2 = have(orderedRestriction(k1, n, p) === orderedRestriction(k2, n, p)) subproof {
                  // suppose not
                  assume(!(orderedRestriction(k1, n, p) === orderedRestriction(k2, n, p)))

                  // there must exist an element where they disagree, say m
                  val m = variable
                  val mDef = in(m, initialSegment(p, n)) /\ !(app(orderedRestriction(k1, n, p), m) === app(orderedRestriction(k2, n, p), m))
                  val mExists = have(exists(m, mDef)) subproof {
                    // k1 |^ n != k2 |^ n by assumption
                    val k1k2unequal = have(!(orderedRestriction(k1, n, p) === orderedRestriction(k2, n, p))) by Restate

                    // they are functions on the same domain
                    val k1k2functional = have(functionalOver(orderedRestriction(k1, n, p), initialSegment(p, n)) /\ functionalOver(orderedRestriction(k2, n, p), initialSegment(p, n))) subproof {
                      // n < a1 by definition
                      val nLTa1 = have(in(n, initialSegment(p, a1))) by Restate

                      // but a1 < a2, so n < a2
                      have(forall(n, in(n, initialSegment(p, a1)) ==> in(n, initialSegment(p, a2)))) by Tautology.from(
                        domSubset,
                        subsetAxiom of (x -> initialSegment(p, a1), y -> initialSegment(p, a2))
                      )
                      thenHave(in(n, initialSegment(p, a1)) ==> in(n, initialSegment(p, a2))) by InstantiateForall(n)
                      val nLTa2 = have(in(n, initialSegment(p, a2))) by Tautology.from(lastStep, nLTa1)

                      // k1 functional over <a1
                      val k1fun = have(functionalOver(k1, initialSegment(p, a1))) by Restate

                      // k2 functional over <a2
                      val k2fun = have(functionalOver(k2, initialSegment(p, a2))) by Restate

                      // so k1 |^ n and k2 |^ n functional over <n
                      val k1n =
                        have(functionalOver(orderedRestriction(k1, n, p), initialSegment(p, n))) by Tautology.from(k1fun, nLTa1, orderedRestrictionFunctionalOverInit of (f -> k1, a -> n, b -> a1))
                      val k2n =
                        have(functionalOver(orderedRestriction(k2, n, p), initialSegment(p, n))) by Tautology.from(k2fun, nLTa2, orderedRestrictionFunctionalOverInit of (f -> k2, a -> n, b -> a2))

                      have(thesis) by Tautology.from(k1n, k2n)
                    }

                    // so there is a violating element
                    have(!forall(m, in(m, initialSegment(p, n)) ==> (app(orderedRestriction(k1, n, p), m) === app(orderedRestriction(k2, n, p), m)))) by Tautology.from(
                      k1k2unequal,
                      k1k2functional,
                      functionsEqualIfEqualOnDomain of (f -> orderedRestriction(k1, n, p), g -> orderedRestriction(k2, n, p), a -> initialSegment(p, n))
                    )
                    thenHave(thesis) by Restate
                  }

                  // we must have m < n
                  val mViolatesRestricted =
                    have(mDef |- in(m, initialSegment(p, a1)) /\ !(app(orderedRestriction(k1, n, p), m) === app(orderedRestriction(k2, n, p), m)) /\ in(pair(m, n), p2)) subproof {
                      assume(mDef)
                      // we have n < a1
                      have(forall(z, (z === initialSegment(p, a)) <=> (forall(t, in(t, z) <=> (in(t, p1) /\ in(pair(t, a), p2)))))) by Weakening(initialSegment.definition)
                      val initSegMembership = thenHave((forall(t, in(t, initialSegment(p, a)) <=> (in(t, p1) /\ in(pair(t, a), p2))))) by InstantiateForall(initialSegment(p, a))

                      have(in(n, initialSegment(p, a1)) <=> (in(n, p1) /\ in(pair(n, a1), p2))) by InstantiateForall(n)(initSegMembership of a -> a1)
                      val nLTa1 = thenHave(in(pair(n, a1), p2)) by Tautology

                      // and m < n
                      have(in(m, initialSegment(p, n)) <=> (in(m, p1) /\ in(pair(m, n), p2))) by InstantiateForall(m)(initSegMembership of a -> n)
                      val mLTn = thenHave(in(m, p1) /\ in(pair(m, n), p2)) by Tautology

                      // by transitivity, m < a1 as well
                      have(forall(w, forall(y, forall(z, (in(pair(w, y), p2) /\ in(pair(y, z), p2)) ==> in(pair(w, z), p2))))) by Weakening(wellOrderTransitivity)
                      thenHave((in(pair(m, n), p2) /\ in(pair(n, a1), p2)) ==> in(pair(m, a1), p2)) by InstantiateForall(m, n, a1)
                      val mLTa1 = have(in(m, p1) /\ in(pair(m, a1), p2)) by Tautology.from(lastStep, nLTa1, mLTn)

                      have(in(m, initialSegment(p, a1)) <=> (in(m, p1) /\ in(pair(m, a1), p2))) by InstantiateForall(m)(initSegMembership of a -> a1)
                      have(thesis) by Tautology.from(lastStep, mLTa1, mLTn)
                    }

                  val mViolates = have(mDef |- in(m, initialSegment(p, a1)) /\ !(app(k1, m) === app(k2, m)) /\ in(pair(m, n), p2)) subproof {
                    assume(mDef)

                    val mInDom1 = have(in(m, relationDomain(k1))) subproof {
                      val domEQ = have(initialSegment(p, a1) === relationDomain(k1)) by Tautology.from(functionalOver.definition of (f -> k1, x -> initialSegment(p, a1)))

                      have(in(m, initialSegment(p, a1))) by Tautology.from(mViolatesRestricted)
                      thenHave(thesis) by Substitution.ApplyRules(domEQ)
                    }

                    val mInDom2 = have(in(m, relationDomain(k2))) subproof {
                      val domEQ = have(initialSegment(p, a2) === relationDomain(k2)) by Tautology.from(functionalOver.definition of (f -> k2, x -> initialSegment(p, a2)))

                      val mLTa1 = have(in(m, initialSegment(p, a1))) by Tautology.from(mViolatesRestricted)
                      have(forall(m, in(m, initialSegment(p, a1)) ==> in(m, initialSegment(p, a2)))) by Tautology.from(
                        subsetAxiom of (x -> initialSegment(p, a1), y -> initialSegment(p, a2)),
                        domSubset
                      )
                      thenHave(in(m, initialSegment(p, a1)) ==> in(m, initialSegment(p, a2))) by InstantiateForall(m)
                      have(in(m, initialSegment(p, a2))) by Tautology.from(lastStep, mLTa1)

                      thenHave(thesis) by Substitution.ApplyRules(domEQ)
                    }

                    // if the application is equal on the ordered restriction, it must be equal on the entire functions
                    have((app(orderedRestriction(k1, n, p), m) === app(orderedRestriction(k2, n, p), m)) <=> (app(k1, m) === app(k2, m))) by Tautology.from(
                      orderedRestrictionAgreement of (f -> k1, g -> k2, a -> n, b -> m),
                      pIsAPartialOrder,
                      mInDom1,
                      mInDom2
                    )
                    have(thesis) by Tautology.from(mViolatesRestricted, lastStep)
                  }

                  // but n was the minimal violation
                  // contradiction
                  have(mDef |- bot()) subproof {
                    assume(mDef)
                    // m < a1 and k1 m != k2 m ==> n < m \/ n = m
                    have(forall(b, (in(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b))) ==> (in(pair(n, b), p2) \/ (n === b)))) by Restate
                    thenHave((in(m, initialSegment(p, a1)) /\ !(app(k1, m) === app(k2, m))) ==> (in(pair(n, m), p2) \/ (n === m))) by InstantiateForall(m)
                    val mLeqn = have((in(pair(n, m), p2) \/ (n === m))) by Tautology.from(lastStep, mViolates)

                    // we had m < n, and the order is anti-symmetric, so n = m
                    have(forall(n, forall(m, (in(pair(m, n), p2) /\ in(pair(n, m), p2)) ==> (n === m)))) by Tautology.from(
                      wellOrder.definition,
                      totalOrder.definition,
                      partialOrder.definition,
                      antiSymmetric.definition of (r -> p2, x -> p1)
                    )
                    thenHave((in(pair(m, n), p2) /\ in(pair(n, m), p2)) ==> (n === m)) by InstantiateForall(n, m)
                    val nEQm = have((n === m)) by Tautology.from(lastStep, mViolates, mLeqn)

                    // however, that means n < n, but the order is anti-reflexive
                    have(in(pair(m, n), p2)) by Weakening(mViolates)
                    val nLTn = thenHave(in(pair(n, n), p2)) by Substitution.ApplyRules(nEQm)

                    have(forall(n, in(n, p1) ==> !in(pair(n, n), p2))) by Tautology.from(pIsAPartialOrder, partialOrder.definition, antiReflexive.definition of (r -> p2, x -> p1))
                    thenHave(in(n, p1) ==> !in(pair(n, n), p2)) by InstantiateForall(n)
                    have(!in(pair(n, n), p2)) by Tautology.from(lastStep, initialSegmentBaseElement of (x -> n, y -> a1), pIsAPartialOrder)

                    // this is a contradiction
                    have(thesis) by Tautology.from(lastStep, nLTn)
                  }
                  thenHave(exists(m, mDef) |- bot()) by LeftExists
                  have(bot()) by Cut(mExists, lastStep)
                }

                have(F(orderedRestriction(k1, n, p)) === F(orderedRestriction(k1, n, p))) by Restate
                thenHave(thesis) by Substitution.ApplyRules(k1k2)
              }

              // // finally k1 n == k2 n
              // // this is a contradiction
              val appEq = have(nDef |- app(k1, n) === app(k2, n)) subproof {
                assume(nDef)
                val k1ToFK2 = equalityTransitivity of (x -> app(k1, n), y -> F(orderedRestriction(k1, n, p)), z -> F(orderedRestriction(k2, n, p)))
                val k1ToK2 = equalityTransitivity of (x -> app(k1, n), y -> F(orderedRestriction(k2, n, p)), z -> app(k2, n))

                have(thesis) by Tautology.from(fK1, fK2, ordResEq, k1ToFK2, k1ToK2)
              }

              thenHave(nDef |- ()) by Tautology
              thenHave(exists(n, nDef) |- ()) by LeftExists
              val disagreeCase = have(k1k2disagree |- ()) by Cut(nExists, lastStep)

              have(!k1k2disagree |- subset(k1, k2)) subproof {
                assume(!k1k2disagree)
                val impl = have(forall(b, in(b, initialSegment(p, a1)) ==> (app(k1, b) === app(k2, b)))) by Restate

                // k1 k2 are functional
                val funK1 = have(functionalOver(k1, initialSegment(p, a1))) by Tautology
                val funK2 = have(functionalOver(k2, initialSegment(p, a2))) by Tautology

                // // and <a1 \subseteq <a2
                val domSubset = have(subset(initialSegment(p, a1), initialSegment(p, a2))) by Tautology.from(initialSegmentsSubset of (x -> a1, y -> a2), pIsAPartialOrder)

                have(thesis) by Tautology.from(impl, funK1, funK2, domSubset, functionsSubsetIfEqualOnSubsetDomain of (f -> k1, g -> k2, a -> initialSegment(p, a1), b -> initialSegment(p, a2)))
              }

              have(thesis) by Tautology.from(lastStep, disagreeCase)
            }

            // finally, instantiate to y1 < y2 and to y2 < y1
            val y1LTy2 = have(in(pair(y1, y2), p2) |- subset(t1, t2)) by Restate.from(ltToSubset of (a1 -> y1, k1 -> t1, a2 -> y2, k2 -> t2))
            val y2LTy1 = have(in(pair(y2, y1), p2) |- subset(t2, t1)) by Restate.from(ltToSubset of (a1 -> y2, k1 -> t2, a2 -> y1, k2 -> t1))

            // totality of the order means y1 < y2 or y2 < y1
            have(in(pair(y1, y2), p2) \/ in(pair(y2, y1), p2)) subproof {
              have(forall(y1, forall(y2, (in(y1, p1) /\ in(y2, p1)) ==> (in(pair(y1, y2), p2) \/ in(pair(y2, y1), p2) \/ (y1 === y2))))) by Tautology.from(
                wellOrder.definition,
                totalOrder.definition,
                total.definition of (r -> p2, x -> p1)
              )
              val impl = thenHave((in(y1, p1) /\ in(y2, p1)) ==> (in(pair(y1, y2), p2) \/ in(pair(y2, y1), p2) \/ (y1 === y2))) by InstantiateForall(y1, y2)

              // expand defs
              have(forall(z, (z === initialSegment(x, y)) <=> forall(t, in(t, z) <=> (in(t, firstInPair(x)) /\ in(pair(t, y), secondInPair(x)))))) by Weakening(
                initialSegment.definition of (p -> x, a -> y)
              )
              thenHave(forall(t, in(t, initialSegment(x, y)) <=> (in(t, firstInPair(x)) /\ in(pair(t, y), secondInPair(x))))) by InstantiateForall(initialSegment(x, y))
              val initXY = thenHave(in(c, initialSegment(x, y)) <=> (in(c, firstInPair(x)) /\ in(pair(c, y), secondInPair(x)))) by InstantiateForall(c)

              have(in(y1, p1) /\ in(y2, p1)) by Tautology.from(initialSegmentBaseElement of (y -> x, x -> y1), initialSegmentBaseElement of (y -> x, x -> y2), pIsAPartialOrder)
              have(thesis) by Tautology.from(lastStep, impl)
            }

            have(thesis) by Tautology.from(lastStep, y1LTy2, y2LTy1)
            // sorry
          }

          have(thesis) by Tautology.from(yeq, neq)
        }

        thenHave((ytDef(y1, t1), ytDef(y2, t2)) |- subset(t1, t2) \/ subset(t2, t1)) by Restate
        thenHave((ytDef(y1, t1), exists(y2, ytDef(y2, t2))) |- subset(t1, t2) \/ subset(t2, t1)) by LeftExists
        val exToRes = thenHave((exists(y1, ytDef(y1, t1)), exists(y2, ytDef(y2, t2))) |- subset(t1, t2) \/ subset(t2, t1)) by LeftExists

        // wDef
        val exy = have(in(b, w) <=> exists(y, in(y, initialSegment(p, x)) /\ fun(b, y))) by InstantiateForall

        have(thesis) by Tautology.from(exToRes, exy of b -> t1, exy of b -> t2)
      }

      have(thesis) by Tautology.from(t1EQt2, t1NEQt2)
    }

    thenHave(in(t1, w) /\ in(t2, w) ==> subset(t1, t2) \/ subset(t2, t1)) by Restate
    thenHave(forall(t2, in(t1, w) /\ in(t2, w) ==> subset(t1, t2) \/ subset(t2, t1))) by RightForall
    thenHave(forall(t1, forall(t2, in(t1, w) /\ in(t2, w) ==> subset(t1, t2) \/ subset(t2, t1)))) by RightForall
  }

  val uwfunctional = Lemma(
    wDef /\ wellOrder(p) |- functional(uw)
  ) {
    have(thesis) by Tautology.from(elemsFunctional, elemsSubset, unionOfFunctionSet of z -> w)
  }

  val uwRestrictedEq = Lemma(
    wellOrder(p) /\ wDef /\ in(z, relationDomain(uw)) |- app(uw, z) === F(orderedRestriction(uw, z, p))
  ) {
    assume(wellOrder(p), wDef)
    assume(in(z, relationDomain(uw)))

    // \exists g \in w. uw z = F g |^ z
    val gExists = have(exists(g, in(g, w) /\ in(z, relationDomain(g)) /\ (app(uw, z) === F(orderedRestriction(g, z, p))))) subproof {
      // dom uw = < x
      // val domUEq = have(relationDomain(uw) === initialSegment(p, x)) by Tautology.from(uwFunctionalOver, functionalOverImpliesDomain of (f -> uw, x -> initialSegment(p, x)))

      // z in dom uw
      // have(in(z, initialSegment(p, x))) by Restate
      // val zInDom = thenHave(in(z, relationDomain(uw))) by EqualityReasoning.ApplyRules(domUEq)

      // so exists g \in w, z \in dom g
      have(functional(uw) /\ in(z, relationDomain(uw)) |- exists(g, in(g, w) /\ in(z, relationDomain(g)))) by InstantiateForall(z)(domainOfFunctionalUnion of z -> w)
      val gExists = have(exists(g, in(g, w) /\ in(z, relationDomain(g)))) by Tautology.from(lastStep, uwfunctional)

      have((in(g, w), in(z, relationDomain(g))) |- app(uw, z) === F(orderedRestriction(g, z, p))) subproof {
        assume(in(g, w))
        assume(in(z, relationDomain(g)))

        // given such a g, g(z) = uw(z)
        val gEqU = have(app(g, z) === app(uw, z)) subproof {
          have(
            (b === app(f, z)) <=> ((functional(f) /\ in(z, relationDomain(f))) ==> in(pair(z, b), f)) /\ ((!functional(f) \/ !in(z, relationDomain(f))) ==> (b === ∅))
          ) by InstantiateForall(b)(app.definition of x -> z)
          val appDef = thenHave(functional(f) /\ in(z, relationDomain(f)) |- (b === app(f, z)) <=> in(pair(z, b), f)) by Tautology

          // for g z
          val gb = have((b === app(g, z)) <=> in(pair(z, b), g)) subproof {
            // g is functional
            have(in(g, w) ==> functional(g)) by InstantiateForall(g)(elemsFunctional)
            have(thesis) by Tautology.from(lastStep, appDef of f -> g)
          }

          // for uw z
          val uwb = have((b === app(uw, z)) <=> in(pair(z, b), uw)) by Tautology.from(appDef of f -> uw, uwfunctional)

          // in g ==> in uw
          have(in(t, g) ==> in(t, uw)) subproof {
            assume(in(t, g))

            // suffices to show the existence of g
            val unionAx = have(in(t, uw) <=> exists(g, in(g, w) /\ in(t, g))) by Weakening(unionAxiom of (z -> t, x -> w))

            have(in(g, w) /\ in(t, g)) by Restate
            thenHave(exists(g, in(g, w) /\ in(t, g))) by RightExists

            have(thesis) by Tautology.from(lastStep, unionAx)
          }

          // equal
          have((b === app(g, z)) |- (b === app(uw, z))) by Tautology.from(lastStep of t -> pair(z, b), gb, uwb)
          have(thesis) by Restate.from(lastStep of b -> app(g, z))
        }

        // we must also have g(z) = F(g |^ z)
        have(app(g, z) === F(orderedRestriction(g, z, p))) subproof {
          have(in(g, w) <=> exists(y, in(y, initialSegment(p, x)) /\ fun(g, y))) by InstantiateForall
          val yExists = thenHave(exists(y, in(y, initialSegment(p, x)) /\ fun(g, y))) by Tautology

          have(fun(g, y) |- app(g, z) === F(orderedRestriction(g, z, p))) subproof {
            assume(fun(g, y))

            // dom g = < y
            val domEq = have(relationDomain(g) === initialSegment(p, y)) by Tautology.from(functionalOverImpliesDomain of (f -> g, x -> initialSegment(p, y)))

            have(forall(a, in(a, initialSegment(p, y)) ==> (app(g, a) === F(orderedRestriction(g, a, p))))) by Restate
            thenHave(in(z, initialSegment(p, y)) ==> (app(g, z) === F(orderedRestriction(g, z, p)))) by InstantiateForall(z)
            thenHave(in(z, relationDomain(g)) ==> (app(g, z) === F(orderedRestriction(g, z, p)))) by Substitution.ApplyRules(domEq)
            thenHave(thesis) by Restate
          }
          thenHave(in(y, initialSegment(p, x)) /\ fun(g, y) |- app(g, z) === F(orderedRestriction(g, z, p))) by Weakening
          thenHave(exists(y, in(y, initialSegment(p, x)) /\ fun(g, y)) |- app(g, z) === F(orderedRestriction(g, z, p))) by LeftExists
          have(thesis) by Cut(yExists, lastStep)
        }

        thenHave(thesis) by Substitution.ApplyRules(gEqU)
      }

      thenHave((in(g, w) /\ in(z, relationDomain(g))) |- in(g, w) /\ in(z, relationDomain(g)) /\ (app(uw, z) === F(orderedRestriction(g, z, p)))) by Tautology
      thenHave((in(g, w) /\ in(z, relationDomain(g))) |- exists(g, in(g, w) /\ in(z, relationDomain(g)) /\ (app(uw, z) === F(orderedRestriction(g, z, p))))) by RightExists
      thenHave(exists(g, in(g, w) /\ in(z, relationDomain(g))) |- exists(g, in(g, w) /\ in(z, relationDomain(g)) /\ (app(uw, z) === F(orderedRestriction(g, z, p))))) by LeftExists

      have(thesis) by Cut(gExists, lastStep)
    }

    // but g \in w ==> g |^ z = uw |^ z
    val gRestrictedEq = have(in(g, w) /\ in(z, relationDomain(g)) |- orderedRestriction(g, z, p) === orderedRestriction(uw, z, p)) subproof {
      assume(in(g, w))
      assume(in(z, relationDomain(g)))

      val og = orderedRestriction(g, z, p)
      val ou = orderedRestriction(uw, z, p)

      // we prove this for a generic element t
      val ogDef = have(in(t, og) <=> (in(t, g) /\ in(firstInPair(t), initialSegment(p, z)))) by Tautology.from(orderedRestrictionMembership of (f -> g, a -> z, b -> t), pIsAPartialOrder)

      val ouDef = have(in(t, ou) <=> (in(t, uw) /\ in(firstInPair(t), initialSegment(p, z)))) by Tautology.from(orderedRestrictionMembership of (f -> uw, a -> z, b -> t), pIsAPartialOrder)

      // t \in g |^ z ==> t \in uw |^ z
      val fwd = have(in(t, og) |- in(t, ou)) subproof {
        assume(in(t, og))
        val tInG = have((in(t, g) /\ in(firstInPair(t), initialSegment(p, z)))) by Tautology.from(ogDef)

        // but g is a subset of uw
        have(in(t, g) ==> in(t, uw)) subproof {
          assume(in(t, g))

          have(in(g, w) /\ in(t, g)) by Restate
          thenHave(exists(g, in(g, w) /\ in(t, g))) by RightExists
          have(thesis) by Tautology.from(lastStep, unionAxiom of (x -> w, z -> t))
        }

        have(thesis) by Tautology.from(lastStep, tInG, ouDef)
      }

      // t \in uw |^ z ==> t \in g |^ z
      val bwd = have(in(t, ou) |- in(t, og)) subproof {
        assume(in(t, ou))
        val tInU = have((in(t, uw) /\ in(firstInPair(t), initialSegment(p, z)))) by Tautology.from(ouDef)

        // if t \in uw and t1 < z
        have(in(t, uw) /\ in(firstInPair(t), initialSegment(p, z)) |- in(t, g)) subproof {
          assume(in(t, uw))
          assume(in(firstInPair(t), initialSegment(p, z)))

          // suppose ! t \in g
          have(!in(t, g) |- ()) subproof {
            assume(!in(t, g))

            // exists f \in w, t \in f by union axiom on uw
            val fExists = have(exists(f, in(f, w) /\ in(t, f))) by Tautology.from(unionAxiom of (x -> w, z -> t))

            // if such an f exists
            have(in(f, w) /\ in(t, f) |- ()) subproof {
              assume(in(f, w))
              assume(in(t, f))

              // f \subseteq g or g \subseteq f
              val cases = have(subset(f, g) \/ subset(g, f)) subproof {
                have((in(g, w) /\ in(f, w)) ==> (subset(g, f) \/ subset(f, g))) by InstantiateForall(g, f)(elemsSubset)
                thenHave(thesis) by Tautology
              }

              // f \subseteq g ==> contradiction directly
              val fg = have(subset(f, g) |- ()) subproof {
                assume(subset(f, g))

                have(forall(t, in(t, f) ==> in(t, g))) by Tautology.from(subsetAxiom of (x -> f, y -> g))
                thenHave(in(t, f) ==> in(t, g)) by InstantiateForall(t)
                thenHave(thesis) by Tautology
              }

              // g \subseteq f
              val gf = have(subset(g, f) |- ()) subproof {
                assume(subset(g, f))

                val t1 = firstInPair(t)
                val t2 = secondInPair(t)

                // t1 \in dom og
                val t1InDomOG = have(in(t1, relationDomain(og))) subproof {
                  // t \in ou
                  // so t1 \in <z
                  val t1LTz = have(in(t1, initialSegment(p, z))) by Tautology.from(ouDef)

                  // <z = dom og
                  have(relationDomain(og) === initialSegment(p, z)) subproof {
                    // dom g is < y for some y
                    have(in(g, w) <=> exists(y, in(y, initialSegment(p, x)) /\ fun(g, y))) by InstantiateForall
                    val yExists = thenHave(exists(y, in(y, initialSegment(p, x)) /\ fun(g, y))) by Tautology

                    have(in(y, initialSegment(p, x)) /\ fun(g, y) |- relationDomain(og) === initialSegment(p, z)) subproof {
                      assume(in(y, initialSegment(p, x)))
                      assume(fun(g, y))

                      // dom g = < y
                      have(functionalOver(g, initialSegment(p, y))) by Restate
                      val domEq = have(relationDomain(g) === initialSegment(p, y)) by Tautology.from(lastStep, functionalOver.definition of (f -> g, x -> initialSegment(p, y)))

                      // but z in dom g, so z < y
                      have(in(pair(z, y), p2)) subproof {
                        have(in(z, relationDomain(g))) by Restate
                        thenHave(in(z, initialSegment(p, y))) by Substitution.ApplyRules(domEq)
                        have(thesis) by Tautology.from(lastStep, initialSegmentElement of x -> z, pIsAPartialOrder)
                      }

                      // so < z \subseteq < y
                      val zySubset = have(subset(initialSegment(p, z), initialSegment(p, y))) by Tautology.from(lastStep, initialSegmentsSubset of (x -> z, y -> y), pIsAPartialOrder)

                      // dom og = < y \cap < z = < z
                      have(thesis) subproof {
                        // dom og = < y \cap < z
                        val domEQ = have(relationDomain(og) === setIntersection(initialSegment(p, z), initialSegment(p, y))) subproof {
                          val ogExpand = have(restrictedFunction(g, initialSegment(p, z)) === og) by InstantiateForall(og)(orderedRestriction.definition of (f -> g, a -> z))

                          have(relationDomain(restrictedFunction(g, initialSegment(p, z))) === setIntersection(initialSegment(p, z), relationDomain(g))) by Weakening(
                            restrictedFunctionDomain of (f -> g, x -> initialSegment(p, z))
                          )
                          thenHave(thesis) by Substitution.ApplyRules(ogExpand, domEq)
                        }

                        have(setIntersection(initialSegment(p, z), initialSegment(p, y)) === initialSegment(p, z)) by Tautology.from(
                          lastStep,
                          zySubset,
                          intersectionOfSubsets of (x -> initialSegment(p, z), y -> initialSegment(p, y))
                        )

                        have(thesis) by Substitution.ApplyRules(lastStep)(domEQ)
                      }
                    }

                    thenHave(exists(y, in(y, initialSegment(p, x)) /\ fun(g, y)) |- relationDomain(og) === initialSegment(p, z)) by LeftExists
                    have(thesis) by Cut(yExists, lastStep)
                  }

                  // t1 \in dom g
                  have(thesis) by Substitution.ApplyRules(lastStep)(t1LTz)
                }

                // since t1 \in dom g, exists a. (t, a) \in g
                val aExists = have(exists(a, in(pair(t1, a), g))) subproof {
                  have(forall(t, in(t, relationDomain(g)) <=> exists(a, in(pair(t, a), g)))) by InstantiateForall(relationDomain(g))(relationDomain.definition of r -> g)
                  val domIff = thenHave(in(t1, relationDomain(g)) <=> exists(a, in(pair(t1, a), g))) by InstantiateForall(t1)

                  // t1 is in dom og, so it is in dom g
                  have(in(t1, relationDomain(g))) subproof {
                    val ordEQ = have(og === restrictedFunction(g, initialSegment(p, z))) by InstantiateForall(og)(orderedRestriction.definition of (f -> g, a -> z))

                    have(relationDomain(restrictedFunction(g, initialSegment(p, z))) === setIntersection(initialSegment(p, z), relationDomain(g))) by Tautology.from(
                      restrictedFunctionDomain of (f -> g, x -> initialSegment(p, z))
                    )
                    thenHave(relationDomain(og) === setIntersection(initialSegment(p, z), relationDomain(g))) by Substitution.ApplyRules(ordEQ)

                    have(forall(b, in(b, relationDomain(og)) <=> in(b, setIntersection(initialSegment(p, z), relationDomain(g))))) by Tautology.from(
                      lastStep,
                      extensionalityAxiom of (x -> relationDomain(og), y -> setIntersection(initialSegment(p, z), relationDomain(g)))
                    )
                    thenHave(in(t1, relationDomain(og)) <=> in(t1, setIntersection(initialSegment(p, z), relationDomain(g)))) by InstantiateForall(t1)
                    have(in(t1, setIntersection(initialSegment(p, z), relationDomain(g)))) by Tautology.from(lastStep, t1InDomOG)
                    have(thesis) by Tautology.from(lastStep, setIntersectionMembership of (t -> t1, x -> initialSegment(p, z), y -> relationDomain(g)))
                  }

                  have(thesis) by Tautology.from(lastStep, domIff)
                }

                have(in(pair(t1, a), g) |- ()) subproof {
                  assume(in(pair(t1, a), g))

                  // (t1, a) \in f
                  have(forall(t, in(t, g) ==> in(t, f))) by Tautology.from(subsetAxiom of (x -> g, y -> f))
                  thenHave(in(pair(t1, a), g) ==> in(pair(t1, a), f)) by InstantiateForall(pair(t1, a))
                  val t1aInF = thenHave(in(pair(t1, a), f)) by Tautology

                  // t must be a pair
                  val tIsPair = have(exists(a, exists(b, pair(a, b) === t))) subproof {
                    have(forall(t, in(t, uw) ==> exists(a, exists(b, (pair(a, b) === t) /\ in(a, relationDomain(uw)))))) by Tautology.from(uwfunctional, functionalMembership of (f -> uw))
                    val exIn = thenHave(exists(a, exists(b, (pair(a, b) === t) /\ in(a, relationDomain(uw))))) by InstantiateForall(t)

                    // eliminate extra terms inside exists
                    have(exists(a, exists(b, (pair(a, b) === t) /\ in(a, relationDomain(uw)))) |- exists(a, exists(b, (pair(a, b) === t)))) subproof {
                      have((pair(c, b) === t) /\ in(c, relationDomain(uw)) |- (pair(c, b) === t)) by Restate
                      thenHave((pair(c, b) === t) /\ in(c, relationDomain(uw)) |- exists(b, (pair(c, b) === t))) by RightExists
                      thenHave((pair(c, b) === t) /\ in(c, relationDomain(uw)) |- exists(c, exists(b, (pair(c, b) === t)))) by RightExists
                      thenHave(exists(b, (pair(c, b) === t) /\ in(c, relationDomain(uw))) |- exists(c, exists(b, (pair(c, b) === t)))) by LeftExists
                      thenHave(exists(c, exists(b, (pair(c, b) === t) /\ in(c, relationDomain(uw)))) |- exists(c, exists(b, (pair(c, b) === t)))) by LeftExists
                    }
                    have(thesis) by Cut(exIn, lastStep)
                  }
                  val tEqt1t2 = have(t === pair(t1, t2)) by Tautology.from(tIsPair, pairReconstruction of x -> t)

                  // but (t1, t2) \in f
                  val t1t2InF = have(in(pair(t1, t2), f)) subproof {
                    // t in f
                    val tInF = have(in(t, f)) by Restate

                    // so (t1, t2) = t
                    have(thesis) by Substitution.ApplyRules(tEqt1t2)(tInF)
                  }

                  // t2 = a
                  val t2Eqa = have(t2 === a) subproof {
                    // f is functional
                    have(in(f, w) ==> functional(f)) by InstantiateForall(f)(elemsFunctional)

                    // given t1, there must be a unique element in ran f it maps to
                    have(forall(t, exists(b, in(pair(t, b), f)) ==> existsOne(b, in(pair(t, b), f)))) by Tautology.from(lastStep, functional.definition)
                    val exToExOne = thenHave(exists(b, in(pair(t1, b), f)) |- existsOne(b, in(pair(t1, b), f))) by InstantiateForall(t1)

                    have(in(pair(t1, a), f)) by Weakening(t1aInF)
                    val ex = thenHave(exists(b, in(pair(t1, b), f))) by RightExists
                    val exOne = have(existsOne(b, in(pair(t1, b), f))) by Cut(lastStep, exToExOne)

                    have(forall(a, forall(b, !in(pair(t1, a), f) \/ !in(pair(t1, b), f) \/ (a === b)))) by Tautology.from(atleastTwoExist of P -> lambda(a, in(pair(t1, a), f)), ex, exOne)
                    thenHave(!in(pair(t1, a), f) \/ !in(pair(t1, t2), f) \/ (a === t2)) by InstantiateForall(a, t2)
                    have(thesis) by Tautology.from(lastStep, t1aInF, t1t2InF)
                  }

                  // but then (t1, t2) = t \in g
                  have(in(pair(t1, a), g)) by Restate
                  thenHave(in(pair(t1, t2), g)) by Substitution.ApplyRules(t2Eqa)
                  thenHave(in(t, g)) by Substitution.ApplyRules(tEqt1t2)

                  // this is a contradiction
                  thenHave(thesis) by Tautology
                }

                thenHave(exists(a, in(pair(t1, a), g)) |- ()) by LeftExists
                have(thesis) by Tautology.from(lastStep, aExists)
              }

              have(thesis) by Tautology.from(cases, gf, fg)
            }

            thenHave(exists(f, in(f, w) /\ in(t, f)) |- ()) by LeftExists
            have(thesis) by Tautology.from(lastStep, fExists)
          }
        }

        have(thesis) by Tautology.from(lastStep, tInU, ogDef)
      }

      have(in(t, ou) <=> in(t, og)) by Tautology.from(fwd, bwd)
      thenHave(forall(t, in(t, ou) <=> in(t, og))) by RightForall
      have(ou === og) by Tautology.from(lastStep, extensionalityAxiom of (x -> ou, y -> og))
    }

    have(in(g, w) /\ in(z, relationDomain(g)) /\ (app(uw, z) === F(orderedRestriction(g, z, p))) |- app(uw, z) === F(orderedRestriction(uw, z, p))) subproof {
      have(in(g, w) /\ in(z, relationDomain(g)) /\ (app(uw, z) === F(orderedRestriction(g, z, p))) |- (app(uw, z) === F(orderedRestriction(g, z, p)))) by Restate
      thenHave(thesis) by Substitution.ApplyRules(gRestrictedEq)
    }

    thenHave(exists(g, in(g, w) /\ in(z, relationDomain(g)) /\ (app(uw, z) === F(orderedRestriction(g, z, p)))) |- app(uw, z) === F(orderedRestriction(uw, z, p))) by LeftExists
    have(thesis) by Tautology.from(gExists, lastStep)

  }

  /**
   * Theorem --- Recursive Function Exists
   *
   * Given that for each element of the initial segment of `x`, a function as
   * defined by [[wellOrderedRecursion]] exists, then a function with the same
   * properties exists for `x`.
   */
  val recursiveFunctionExistencePropagates = Theorem(
    wellOrder(p) /\ in(x, p1) /\ forall(y, in(y, initialSegment(p, x)) ==> prop(y)) |- exists(g, fun(g, x))
  ) {
    assume(wellOrder(p))
    assume(in(x, p1))
    assume(forall(y, in(y, initialSegment(p, x)) ==> prop(y)))

    // if w is as defined, there is a function g as required
    have(wDef |- exists(g, fun(g, x))) subproof {
      assume(wDef)
      // properties of the elements of w
      // 1. t \in w ==> functional t
      // 2. t1, t2 \in w ==> t1 \subseteq t2 \/ t2 \subseteq t1

      // 1. t \in w ==> functional t
      // see [[elemsFunctional]] and [[elemsSubset]]

      // working with orderedRestrictions
      val ordBreakdown = have(orderedRestriction(a, b, p) === restrictedFunction(a, initialSegment(p, b))) by InstantiateForall(orderedRestriction(a, b, p))(
        orderedRestriction.definition of (f -> a, a -> b)
      )

      // see [[uwfunctional]]

      // now, from w, we will construct the requisite function g for x
      // see [[uwRestrictedEq]]

      // common subproof
      val zyInDomUw = have(in(z, initialSegment(p, y)) /\ in(y, initialSegment(p, x)) |- in(z, relationDomain(uw))) subproof {
        assume(in(z, initialSegment(p, y)), in(y, initialSegment(p, x)))

        have(in(y, initialSegment(p, x)) ==> (in(y, p1) /\ existsOne(g, fun(g, y)))) by InstantiateForall
        val gExists = have(exists(g, fun(g, y))) by Tautology.from(lastStep, existsOneImpliesExists of (P -> lambda(g, fun(g, y))))

        have(fun(g, y) |- in(z, relationDomain(uw))) subproof {
          assume(fun(g, y))

          val zIng = have(in(z, relationDomain(g))) subproof {
            have(functionalOver(g, initialSegment(p, y))) by Tautology
            val domEQ = have(relationDomain(g) === initialSegment(p, y)) by Tautology.from(lastStep, functionalOver.definition of (f -> g, x -> initialSegment(p, y)))

            have(in(z, initialSegment(p, y))) by Restate
            thenHave(thesis) by Substitution.ApplyRules(domEQ)
          }

          val gInw = have(in(g, w)) subproof {
            have(in(y, initialSegment(p, x)) /\ fun(g, y)) by Restate
            val yEx = thenHave(exists(y, in(y, initialSegment(p, x)) /\ fun(g, y))) by RightExists

            have(forall(t, in(t, w) <=> exists(y, in(y, initialSegment(p, x)) /\ fun(t, y)))) by Restate
            thenHave(in(g, w) <=> exists(y, in(y, initialSegment(p, x)) /\ fun(g, y))) by InstantiateForall(g)
            have(thesis) by Tautology.from(lastStep, yEx)
          }

          have(forall(z, in(z, relationDomain(uw)) <=> exists(g, in(g, w) /\ in(z, relationDomain(g))))) by Tautology.from(uwfunctional, domainOfFunctionalUnion of z -> w)
          val zInUiff = thenHave(in(z, relationDomain(uw)) <=> exists(g, in(g, w) /\ in(z, relationDomain(g)))) by InstantiateForall(z)

          have(in(g, w) /\ in(z, relationDomain(g))) by Tautology.from(zIng, gInw)
          thenHave(exists(g, in(g, w) /\ in(z, relationDomain(g)))) by RightExists
          have(in(z, relationDomain(uw))) by Tautology.from(lastStep, zInUiff)
        }

        thenHave(exists(g, fun(g, y)) |- in(z, relationDomain(uw))) by LeftExists
        have(in(z, relationDomain(uw))) by Cut.withParameters(exists(g, fun(g, y)))(gExists, lastStep)
      }

      // there are two cases, either x has a predecessor, or it doesn't
      val limSuccCases = have(limitElement(p, x) \/ successorElement(p, x)) by Tautology.from(everyElemInTotalOrderLimitOrSuccessor, wellOrder.definition)

      // if x has no predecessor, i.e., it is a limit element, w is the required function
      val limitCase = have(limitElement(p, x) |- exists(g, fun(g, x))) subproof {
        assume(limitElement(p, x))

        // <x = \cup <y

        // uw is a function on <x
        val uwFunctionalOver = have(functionalOver(uw, initialSegment(p, x))) subproof {
          val elem = variable
          val limitProp =
            have(in(pair(elem, x), p2) ==> exists(y, in(pair(y, x), p2) /\ in(pair(elem, y), p2))) by Tautology.from(initialSegmentUnionForLimitElementsIsComplete of t -> elem, pIsATotalOrder)

          have(forall(t, in(t, relationDomain(uw)) <=> exists(g, in(g, w) /\ in(t, relationDomain(g))))) by Tautology.from(domainOfFunctionalUnion of z -> w, uwfunctional)
          val domDef = thenHave(in(elem, relationDomain(uw)) <=> exists(g, in(g, w) /\ in(elem, relationDomain(g)))) by InstantiateForall(elem)

          have(exists(g, in(g, w) /\ in(elem, relationDomain(g))) <=> in(elem, initialSegment(p, x))) subproof {
            val fwd = have(exists(g, in(g, w) /\ in(elem, relationDomain(g))) |- in(elem, initialSegment(p, x))) subproof {
              have(in(g, w) /\ in(elem, relationDomain(g)) |- in(elem, initialSegment(p, x))) subproof {
                assume(in(g, w))
                assume(in(elem, relationDomain(g)))

                // there must be a y < x that g is a recursive function for
                have(in(g, w) <=> exists(y, in(y, initialSegment(p, x)) /\ fun(g, y))) by InstantiateForall
                val yExists = thenHave(exists(y, in(y, initialSegment(p, x)) /\ fun(g, y))) by Tautology

                // elem is in dom g, which is <y, so elem < y, and finally elem < x by transitivity
                have(in(y, initialSegment(p, x)) /\ fun(g, y) |- in(elem, initialSegment(p, x))) subproof {
                  assume(in(y, initialSegment(p, x)))
                  assume(fun(g, y))

                  have(relationDomain(g) === initialSegment(p, y)) by Tautology.from(functionalOver.definition of (f -> g, x -> initialSegment(p, y)))
                  have(forall(elem, in(elem, relationDomain(g)) <=> in(elem, initialSegment(p, y)))) by Tautology.from(
                    lastStep,
                    extensionalityAxiom of (x -> relationDomain(g), y -> initialSegment(p, y))
                  )
                  thenHave(in(elem, relationDomain(g)) <=> in(elem, initialSegment(p, y))) by InstantiateForall(elem)
                  val eLTy = have(in(pair(elem, y), p2)) by Tautology.from(lastStep, initialSegmentElement of x -> elem, pIsAPartialOrder)
                  val yLTx = have(in(pair(y, x), p2)) by Tautology.from(initialSegmentElement of (x -> y, y -> x), pIsAPartialOrder)

                  // apply transitivity
                  have(forall(elem, forall(y, forall(x, (in(pair(elem, y), p2) /\ in(pair(y, x), p2)) ==> in(pair(elem, x), p2))))) by Weakening(wellOrderTransitivity)
                  thenHave((in(pair(elem, y), p2) /\ in(pair(y, x), p2)) ==> in(pair(elem, x), p2)) by InstantiateForall(elem, y, x)
                  have(in(pair(elem, x), p2)) by Tautology.from(lastStep, eLTy, yLTx)
                  have(thesis) by Tautology.from(lastStep, initialSegmentElement of (y -> x, x -> elem), pIsAPartialOrder)
                }

                thenHave(exists(y, in(y, initialSegment(p, x)) /\ fun(g, y)) |- in(elem, initialSegment(p, x))) by LeftExists
                have(thesis) by Tautology.from(yExists, lastStep)
              }

              thenHave(thesis) by LeftExists
            }

            val bwd = have(in(elem, initialSegment(p, x)) |- exists(g, in(g, w) /\ in(elem, relationDomain(g)))) subproof {
              assume(in(elem, initialSegment(p, x)))

              // find a y s.t. elem < y < x
              // this exists since x is a limit element
              val yExists = have(exists(y, in(pair(elem, y), p2) /\ in(pair(y, x), p2))) by Tautology.from(limitProp, initialSegmentElement of (y -> x, x -> elem), pIsAPartialOrder)

              // given y, there is a g which is defined recursively for y
              val gExists = have(in(pair(y, x), p2) |- exists(g, fun(g, y))) subproof {
                have(in(y, initialSegment(p, x)) ==> (in(y, p1) /\ existsOne(g, fun(g, y)))) by InstantiateForall
                have(thesis) by Tautology.from(lastStep, initialSegmentElement of (x -> y, y -> x), existsOneImpliesExists of P -> lambda(g, fun(g, y)), pIsAPartialOrder)
              }

              // these g and y give us the required witness for elem
              have((in(pair(elem, y), p2) /\ in(pair(y, x), p2), fun(g, y)) |- exists(g, in(g, w) /\ in(elem, relationDomain(g)))) subproof {
                assume(in(pair(elem, y), p2) /\ in(pair(y, x), p2))
                assume(fun(g, y))

                have(relationDomain(g) === initialSegment(p, y)) by Tautology.from(functionalOver.definition of (f -> g, x -> initialSegment(p, y)))
                have(forall(elem, in(elem, relationDomain(g)) <=> in(elem, initialSegment(p, y)))) by Tautology.from(
                  lastStep,
                  extensionalityAxiom of (x -> relationDomain(g), y -> initialSegment(p, y))
                )
                thenHave(in(elem, relationDomain(g)) <=> in(elem, initialSegment(p, y))) by InstantiateForall(elem)

                val elemInDom = have(in(elem, relationDomain(g))) by Tautology.from(lastStep, initialSegmentElement of x -> elem, pIsAPartialOrder)

                have(in(y, initialSegment(p, x)) /\ fun(g, y)) by Tautology.from(initialSegmentElement of (x -> y, y -> x), pIsAPartialOrder)
                val yExists = thenHave(exists(y, in(y, initialSegment(p, x)) /\ fun(g, y))) by RightExists

                have(in(g, w) <=> exists(y, in(y, initialSegment(p, x)) /\ fun(g, y))) by InstantiateForall
                have(in(g, w) /\ in(elem, relationDomain(g))) by Tautology.from(lastStep, yExists, elemInDom)
                thenHave(thesis) by RightExists
              }

              thenHave((in(pair(elem, y), p2) /\ in(pair(y, x), p2), exists(g, fun(g, y))) |- exists(g, in(g, w) /\ in(elem, relationDomain(g)))) by LeftExists
              have((in(pair(elem, y), p2) /\ in(pair(y, x), p2)) |- exists(g, in(g, w) /\ in(elem, relationDomain(g)))) by Tautology.from(lastStep, gExists)
              thenHave(exists(y, in(pair(elem, y), p2) /\ in(pair(y, x), p2)) |- exists(g, in(g, w) /\ in(elem, relationDomain(g)))) by LeftExists
              have(thesis) by Cut(yExists, lastStep)
            }

            have(thesis) by Tautology.from(fwd, bwd)
          }

          have(in(elem, relationDomain(uw)) <=> in(elem, initialSegment(p, x))) by Tautology.from(lastStep, domDef)
          thenHave(forall(elem, in(elem, relationDomain(uw)) <=> in(elem, initialSegment(p, x)))) by RightForall
          have(relationDomain(uw) === initialSegment(p, x)) by Tautology.from(lastStep, extensionalityAxiom of (x -> relationDomain(uw), y -> initialSegment(p, x)))

          have(thesis) by Tautology.from(functionalOver.definition of (f -> uw, x -> initialSegment(p, x)), lastStep, uwfunctional)
        }

        // z < x ==> uw z = F uw |^ z
        have(in(z, initialSegment(p, x)) |- app(uw, z) === F(orderedRestriction(uw, z, p))) subproof {
          assume(in(z, initialSegment(p, x)))

          // z in dom uw
          have(in(z, relationDomain(uw))) subproof {
            // \exists y. z < y < x as x is limit
            // \exists g \in w. fun g y
            // z in dom g
            // so z in dom uw
            have(in(pair(z, x), p2)) by Tautology.from(initialSegmentElement of (x -> z, y -> x), pIsAPartialOrder)
            val yExists = have(exists(y, in(pair(z, y), p2) /\ in(pair(y, x), p2))) by Tautology.from(lastStep, initialSegmentUnionForLimitElementsIsComplete of t -> z, pIsATotalOrder)

            have(in(pair(z, y), p2) /\ in(pair(y, x), p2) |- in(z, relationDomain(uw))) subproof {
              assume(in(pair(z, y), p2), in(pair(y, x), p2))

              val zLTy = have(in(z, initialSegment(p, y))) by Tautology.from(initialSegmentElement of (x -> z, y -> y), pIsAPartialOrder)
              val yLTx = have(in(y, initialSegment(p, x))) by Tautology.from(initialSegmentElement of (x -> y, y -> x), pIsAPartialOrder)

              have(thesis) by Tautology.from(zLTy, yLTx, zyInDomUw)
            }

            thenHave(exists(y, in(pair(z, y), p2) /\ in(pair(y, x), p2)) |- in(z, relationDomain(uw))) by LeftExists
            have(thesis) by Tautology.from(yExists, lastStep)
          }

          have(thesis) by Tautology.from(lastStep, uwRestrictedEq)
        }

        thenHave(in(z, initialSegment(p, x)) ==> (app(uw, z) === F(orderedRestriction(uw, z, p)))) by Restate
        thenHave(forall(z, in(z, initialSegment(p, x)) ==> (app(uw, z) === F(orderedRestriction(uw, z, p))))) by RightForall
        have(fun(uw, x)) by Tautology.from(lastStep, uwFunctionalOver)
        thenHave(exists(g, fun(g, x))) by RightExists
      }

      // if x has a predecessor, then we need to add an element to uw, giving us v as the requisite function
      val successorCase = have(successorElement(p, x) |- exists(g, fun(g, x))) subproof {
        assume(successorElement(p, x))
        // the right function is v = Uw \cup {(pred x, F Uw)}
        // i.e., Uw with a recursive addition for the predecessor of x
        // which is not included in any initial segment below x (! (pred x < y) for y < x)
        // define pr as the predecessor of x
        val pr = variable
        val prFun = singleton(pair(pr, F(uw)))
        val v = setUnion(uw, prFun)

        val vFun = have(predecessor(p, pr, x) |- fun(v, x)) subproof {
          assume(predecessor(p, pr, x))
          // to this end, we show:
          //   1. v is functional over <x
          //     1. Uw is functional over <pr
          //     2. {(pr, F Uw |^ pr)} is functional over {pr}
          //     3. <pr \cap {pr} = \emptyset
          //     4. So v is functional over <pr \cup {pr}
          //     5. and <pr \cup {pr} = <x
          //   2. v is recursive, i.e. \forall z < x. v z = F v |^ z as required

          val uwFunctionalOver = have(functionalOver(uw, initialSegment(p, pr))) subproof {
            val iffDom = have(functionalOver(uw, initialSegment(p, pr)) <=> (relationDomain(uw) === initialSegment(p, pr))) by Tautology.from(
              functionalOver.definition of (f -> uw, x -> initialSegment(p, pr)),
              uwfunctional
            )

            have(relationDomain(uw) === initialSegment(p, pr)) subproof {
              val fwd = have(in(t, relationDomain(uw)) |- in(t, initialSegment(p, pr))) subproof {
                assume(in(t, relationDomain(uw)))

                have(forall(t, in(t, relationDomain(uw)) <=> exists(g, in(g, w) /\ in(t, relationDomain(g))))) by Tautology.from(uwfunctional, domainOfFunctionalUnion of z -> w)
                thenHave(in(t, relationDomain(uw)) <=> exists(g, in(g, w) /\ in(t, relationDomain(g)))) by InstantiateForall(t)
                val gExists = thenHave(exists(g, in(g, w) /\ in(t, relationDomain(g)))) by Tautology

                have(in(g, w) /\ in(t, relationDomain(g)) |- in(t, initialSegment(p, pr))) subproof {
                  assume(in(g, w))
                  assume(in(t, relationDomain(g)))

                  have(in(g, w) <=> exists(y, in(y, initialSegment(p, x)) /\ fun(g, y))) by InstantiateForall
                  val yExists = thenHave(exists(y, in(y, initialSegment(p, x)) /\ fun(g, y))) by Tautology

                  have(in(y, initialSegment(p, x)) /\ fun(g, y) |- in(t, initialSegment(p, pr))) subproof {
                    assume(in(y, initialSegment(p, x)), fun(g, y))
                    // t < y
                    val domEQ = have(relationDomain(g) === initialSegment(p, y)) by Tautology.from(functionalOver.definition of (f -> g, x -> initialSegment(p, y)))
                    have(in(t, relationDomain(g))) by Restate
                    val tLTy = thenHave(in(t, initialSegment(p, y))) by Substitution.ApplyRules(domEQ)

                    // y <= pr
                    val cases = have((y === pr) \/ in(y, initialSegment(p, pr))) by Tautology.from(initialSegmentPredecessorSplit of (y -> pr, z -> y), pIsATotalOrder)

                    val eqCase = have((y === pr) |- in(t, initialSegment(p, pr))) by Substitution.ApplyRules(y === pr)(tLTy)
                    val initCase = have(in(y, initialSegment(p, pr)) |- in(t, initialSegment(p, pr))) by Tautology.from(tLTy, initialSegmentTransitivity of (x -> t, y -> y, z -> pr), pIsAPartialOrder)

                    have(thesis) by Tautology.from(cases, eqCase, initCase)
                  }

                  thenHave(exists(y, in(y, initialSegment(p, x)) /\ fun(g, y)) |- in(t, initialSegment(p, pr))) by LeftExists
                  have(thesis) by Tautology.from(lastStep, yExists)
                }

                thenHave(exists(g, in(g, w) /\ in(t, relationDomain(g))) |- in(t, initialSegment(p, pr))) by LeftExists
                have(thesis) by Cut(gExists, lastStep)
              }

              val bwd = have(in(t, initialSegment(p, pr)) |- in(t, relationDomain(uw))) subproof {
                assume(in(t, initialSegment(p, pr)))

                have(in(pair(pr, x), p2)) by Tautology.from(predecessor.definition of (x -> pr, y -> x))
                val prLTx = have(in(pr, initialSegment(p, x))) by Tautology.from(lastStep, pIsAPartialOrder, initialSegmentElement of (y -> x, x -> pr))

                have(forall(y, in(y, initialSegment(p, x)) ==> existsOne(g, fun(g, y)))) by Restate
                thenHave(in(pr, initialSegment(p, x)) ==> existsOne(g, fun(g, pr))) by InstantiateForall(pr)
                val gExists = have(exists(g, fun(g, pr))) by Tautology.from(lastStep, prLTx, existsOneImpliesExists of P -> lambda(g, fun(g, pr)))

                have(fun(g, pr) |- in(g, w) /\ in(t, relationDomain(g))) subproof {
                  assume(fun(g, pr))

                  have(in(pr, initialSegment(p, x)) /\ fun(g, pr)) by Tautology.from(prLTx)
                  val exPR = thenHave(exists(pr, in(pr, initialSegment(p, x)) /\ fun(g, pr))) by RightExists

                  have(in(g, w) <=> exists(y, in(y, initialSegment(p, x)) /\ fun(g, y))) by InstantiateForall
                  val gW = have(in(g, w)) by Tautology.from(lastStep, exPR)

                  have(functionalOver(g, initialSegment(p, pr))) by Tautology
                  val domEQ = have(relationDomain(g) === initialSegment(p, pr)) by Tautology.from(lastStep, functionalOver.definition of (f -> g, x -> initialSegment(p, pr)))

                  have(in(t, initialSegment(p, pr))) by Restate
                  thenHave(in(t, relationDomain(g))) by Substitution.ApplyRules(domEQ)
                  have(thesis) by Tautology.from(lastStep, gW)
                }

                thenHave(fun(g, pr) |- exists(g, in(g, w) /\ in(t, relationDomain(g)))) by RightExists
                thenHave(exists(g, fun(g, pr)) |- exists(g, in(g, w) /\ in(t, relationDomain(g)))) by LeftExists
                val gInW = have(exists(g, in(g, w) /\ in(t, relationDomain(g)))) by Cut(gExists, lastStep)

                have(forall(t, in(t, relationDomain(uw)) <=> exists(g, in(g, w) /\ in(t, relationDomain(g))))) by Tautology.from(uwfunctional, domainOfFunctionalUnion of z -> w)
                thenHave(in(t, relationDomain(uw)) <=> exists(g, in(g, w) /\ in(t, relationDomain(g)))) by InstantiateForall(t)
                have(thesis) by Tautology.from(lastStep, gInW)
              }

              have(in(t, relationDomain(uw)) <=> in(t, initialSegment(p, pr))) by Tautology.from(fwd, bwd)
              thenHave(forall(t, in(t, relationDomain(uw)) <=> in(t, initialSegment(p, pr)))) by RightForall
              have(thesis) by Tautology.from(lastStep, extensionalityAxiom of (x -> relationDomain(uw), y -> initialSegment(p, pr)))
            }

            have(thesis) by Tautology.from(lastStep, iffDom)
          }

          // 1. v is functional over <x
          val vFunctionalOver = have(functionalOver(v, initialSegment(p, x))) subproof {
            // 1. Uw is functional over <pr
            // [[uwFunctionalOver]]

            // 2. {(pr, F Uw |^ pr)} is functional over {pr}
            val pairFunctionalOver =
              have(functionalOver(prFun, singleton(pr))) by Tautology.from(pairSingletonIsFunctional of (x -> pr, y -> F(uw)), functionalOver.definition of (f -> prFun, x -> singleton(pr)))

            // 3. <pr \cap {pr} = \emptyset
            val domainsDisjoint = have(setIntersection(initialSegment(p, pr), singleton(pr)) === emptySet()) subproof {
              val singletonMembership = have(in(t, singleton(pr)) <=> (t === pr)) by Weakening(singletonHasNoExtraElements of (y -> t, x -> pr))

              val initMembership = have(in(t, initialSegment(p, pr)) <=> in(pair(t, pr), p2)) by Tautology.from(initialSegmentElement of (x -> t, y -> pr), pIsAPartialOrder)

              have(in(t, singleton(pr)) /\ in(t, initialSegment(p, pr)) |- ()) subproof {
                assume(in(t, singleton(pr)))
                assume(in(t, initialSegment(p, pr)))

                val tEQpr = have(t === pr) by Tautology.from(singletonMembership)
                val tLTpr = have(in(pair(t, pr), p2)) by Tautology.from(initMembership)
                val prprp2 = thenHave(in(pair(pr, pr), p2)) by Substitution.ApplyRules(tEQpr)

                // but the order is anti reflexive
                have(forall(pr, in(pr, p1) ==> !in(pair(pr, pr), p2))) by Tautology.from(pIsAPartialOrder, partialOrder.definition, antiReflexive.definition of (r -> p2, x -> p1))
                thenHave(in(pr, p1) ==> !in(pair(pr, pr), p2)) by InstantiateForall(pr)
                have(!in(pair(pr, pr), p2)) by Tautology.from(lastStep, predecessor.definition of (x -> pr, y -> x))

                have(thesis) by Tautology.from(lastStep, prprp2)
              }

              val inEmpty = thenHave((in(t, singleton(pr)) /\ in(t, initialSegment(p, pr))) ==> in(t, emptySet())) by Weakening

              have(in(t, setIntersection(initialSegment(p, pr), singleton(pr))) <=> (in(t, singleton(pr)) /\ in(t, initialSegment(p, pr)))) by Tautology.from(
                setIntersectionMembership of (x -> initialSegment(p, pr), y -> singleton(pr))
              )
              have(in(t, setIntersection(initialSegment(p, pr), singleton(pr))) ==> in(t, emptySet())) by Substitution.ApplyRules(lastStep)(inEmpty)
              thenHave(forall(t, in(t, setIntersection(initialSegment(p, pr), singleton(pr))) ==> in(t, emptySet()))) by RightForall
              have(subset(setIntersection(initialSegment(p, pr), singleton(pr)), emptySet())) by Tautology.from(
                lastStep,
                subsetAxiom of (x -> setIntersection(initialSegment(p, pr), singleton(pr)), y -> emptySet())
              )
              have(thesis) by Tautology.from(lastStep, emptySetIsItsOwnOnlySubset of x -> setIntersection(initialSegment(p, pr), singleton(pr)))
            }

            // 4. So v is functional over <pr \cup {pr}
            val vFunctionalOverUnion = have(functionalOver(v, setUnion(initialSegment(p, pr), singleton(pr)))) by Tautology.from(
              pairFunctionalOver,
              uwFunctionalOver,
              domainsDisjoint,
              unionOfFunctionsWithDisjointDomains of (f -> uw, a -> initialSegment(p, pr), g -> prFun, b -> singleton(pr))
            )

            // 5. and <pr \cup {pr} = <x
            val unionEQ = have(setUnion(initialSegment(p, pr), singleton(pr)) === initialSegment(p, x)) subproof {
              // < x <=> = pr \/ < pr
              val initBreakdown =
                have(in(t, initialSegment(p, x)) <=> ((t === pr) \/ in(t, initialSegment(p, pr)))) by Tautology.from(initialSegmentPredecessorSplit of (z -> t, y -> pr), pIsATotalOrder)

              val singletonMembership = have(in(t, singleton(pr)) <=> (t === pr)) by Tautology.from(singletonHasNoExtraElements of (y -> t, x -> pr))

              val initMembership = have(in(t, initialSegment(p, x)) <=> (in(t, singleton(pr)) \/ in(t, initialSegment(p, pr)))) by Substitution.ApplyRules(singletonMembership)(initBreakdown)

              have(in(t, setUnion(initialSegment(p, pr), singleton(pr))) <=> (in(t, singleton(pr)) \/ in(t, initialSegment(p, pr)))) by Tautology.from(
                setUnionMembership of (z -> t, x -> initialSegment(p, pr), y -> singleton(pr))
              )
              have(in(t, initialSegment(p, x)) <=> in(t, setUnion(initialSegment(p, pr), singleton(pr)))) by Substitution.ApplyRules(lastStep)(initMembership)
              thenHave(forall(t, in(t, initialSegment(p, x)) <=> in(t, setUnion(initialSegment(p, pr), singleton(pr))))) by RightForall

              have(thesis) by Tautology.from(lastStep, extensionalityAxiom of (x -> initialSegment(p, x), y -> setUnion(initialSegment(p, pr), singleton(pr))))
            }

            have(thesis) by Substitution.ApplyRules(unionEQ)(vFunctionalOverUnion)
          }

          // 2. v is recursive
          val vRecursive = have(forall(z, in(z, initialSegment(p, x)) ==> (app(v, z) === F(orderedRestriction(v, z, p))))) subproof {
            have(in(z, initialSegment(p, x)) |- (app(v, z) === F(orderedRestriction(v, z, p)))) subproof {
              assume(in(z, initialSegment(p, x)))

              // z is in dom v
              val zInDom = have(in(z, relationDomain(v))) subproof {
                val domEQ = have(relationDomain(v) === initialSegment(p, x)) by Tautology.from(functionalOver.definition of (f -> v, x -> initialSegment(p, x)), vFunctionalOver)
                have(in(z, initialSegment(p, x))) by Restate
                thenHave(thesis) by Substitution.ApplyRules(domEQ)
              }

              // app v z is well defined
              val vAppDef = have((a === app(v, z)) <=> in(pair(z, a), v)) subproof {
                have(functional(v)) by Tautology.from(vFunctionalOver, functionalOver.definition of (f -> v, x -> initialSegment(p, x)))
                have(thesis) by Tautology.from(lastStep, zInDom, pairInFunctionIsApp of (f -> v, a -> z, b -> a))
              }

              // z is either the predecessor or below it
              val zSplit = have(((z === pr) \/ in(z, initialSegment(p, pr)))) by Tautology.from(pIsATotalOrder, initialSegmentPredecessorSplit of (y -> pr))

              // uw is actually the ordered restriction of v to pr
              val uwEq = have((uw === orderedRestriction(v, pr, p))) subproof {
                val vpr = orderedRestriction(v, pr, p)

                // uw has domain <pr
                val domUW = have(functionalOver(uw, initialSegment(p, pr))) by Weakening(uwFunctionalOver)

                // so does v |^ pr
                val domRV = have(functionalOver(vpr, initialSegment(p, pr))) subproof {
                  have(functional(v)) by Tautology.from(vFunctionalOver, functionalOver.definition of (f -> v, x -> initialSegment(p, x)))
                  have(functionalOver(restrictedFunction(v, initialSegment(p, pr)), setIntersection(initialSegment(p, pr), relationDomain(v)))) by Tautology.from(
                    lastStep,
                    restrictedFunctionIsFunctionalOver of (f -> v, x -> initialSegment(p, pr))
                  )
                  val vprFun = thenHave(functionalOver(vpr, setIntersection(initialSegment(p, pr), relationDomain(v)))) by Substitution.ApplyRules(ordBreakdown of (a -> v, b -> pr))

                  have(relationDomain(v) === initialSegment(p, x)) by Tautology.from(vFunctionalOver, functionalOver.definition of (f -> v, x -> initialSegment(p, x)))
                  val initIntersection = have(functionalOver(vpr, setIntersection(initialSegment(p, pr), initialSegment(p, x)))) by Substitution.ApplyRules(lastStep)(vprFun)

                  have(setIntersection(initialSegment(p, pr), initialSegment(p, x)) === initialSegment(p, pr)) by Tautology.from(
                    predecessorInInitialSegment of y -> pr,
                    initialSegmentIntersection of y -> pr,
                    pIsAPartialOrder,
                    pIsATotalOrder
                  )
                  have(thesis) by Substitution.ApplyRules(lastStep)(initIntersection)
                }

                // and they agree on their domain
                have(in(b, initialSegment(p, pr)) |- (app(uw, b) === app(vpr, b))) subproof {
                  assume(in(b, initialSegment(p, pr)))

                  val appDefw = have((a === app(uw, b)) <=> in(pair(b, a), uw)) by Tautology.from(functionalOverApplication of (f -> uw, x -> initialSegment(p, pr), b -> a, a -> b), domUW)
                  val appDefv = have((a === app(vpr, b)) <=> in(pair(b, a), vpr)) by Tautology.from(functionalOverApplication of (f -> vpr, x -> initialSegment(p, pr), b -> a, a -> b), domRV)

                  val fwd = have(in(pair(b, a), uw) |- in(pair(b, a), vpr)) subproof {
                    assume(in(pair(b, a), uw))

                    have(in(pair(b, a), v)) by Tautology.from(setUnionMembership of (z -> pair(b, a), x -> uw, y -> prFun))
                    have(in(pair(b, a), restrictedFunction(v, initialSegment(p, pr)))) by Tautology.from(
                      lastStep,
                      restrictedFunctionPairMembership of (f -> v, x -> initialSegment(p, pr), t -> b, a -> a)
                    )
                    thenHave(thesis) by Substitution.ApplyRules(ordBreakdown of (a -> v, b -> pr))
                  }

                  val bwd = have(in(pair(b, a), vpr) |- in(pair(b, a), uw)) subproof {
                    assume(in(pair(b, a), vpr))
                    have(in(pair(b, a), vpr)) by Restate
                    thenHave(in(pair(b, a), restrictedFunction(v, initialSegment(p, pr)))) by Substitution.ApplyRules(ordBreakdown of (a -> v, b -> pr))
                    have(in(pair(b, a), v)) by Tautology.from(lastStep, restrictedFunctionPairMembership of (f -> v, x -> initialSegment(p, pr), t -> b, a -> a))
                    val cases = have(in(pair(b, a), uw) \/ in(pair(b, a), prFun)) by Tautology.from(lastStep, setUnionMembership of (z -> pair(b, a), x -> uw, y -> prFun))

                    have(!in(pair(b, a), prFun)) subproof {
                      // towards a contradiction, assume otherwise
                      assume(in(pair(b, a), prFun))

                      have(pair(b, a) === pair(pr, F(uw))) by Tautology.from(singletonHasNoExtraElements of (y -> pair(b, a), x -> pair(pr, F(uw))))
                      val bEQpr = have(b === pr) by Tautology.from(lastStep, pairExtensionality of (a -> b, b -> a, c -> pr, d -> F(uw)))

                      have(in(b, initialSegment(p, pr))) by Restate
                      thenHave(in(pr, initialSegment(p, pr))) by Substitution.ApplyRules(bEQpr)
                      have(bot()) by Tautology.from(lastStep, initialSegmentIrreflexivity of (x -> pr), pIsAPartialOrder)
                    }

                    have(thesis) by Tautology.from(lastStep, cases)
                  }

                  have(in(pair(b, a), uw) <=> in(pair(b, a), vpr)) by Tautology.from(fwd, bwd)
                  have((a === app(uw, b)) <=> (a === app(vpr, b))) by Tautology.from(appDefw, appDefv, lastStep)
                  have(thesis) by Restate.from(lastStep of a -> app(uw, b))
                }

                thenHave(in(b, initialSegment(p, pr)) ==> (app(uw, b) === app(vpr, b))) by Restate
                thenHave(forall(b, in(b, initialSegment(p, pr)) ==> (app(uw, b) === app(vpr, b)))) by RightForall

                have(thesis) by Tautology.from(functionsEqualIfEqualOnDomain of (f -> uw, g -> vpr, a -> initialSegment(p, pr)), lastStep, domUW, domRV)
              }

              // the property holds for the predecessor
              val prCase = have((z === pr) |- (app(v, z) === F(orderedRestriction(v, z, p)))) subproof {
                have(app(v, pr) === F(orderedRestriction(v, pr, p))) subproof {
                  val fuwEq = have(F(uw) === F(orderedRestriction(v, pr, p))) subproof {
                    have(F(uw) === F(uw)) by Restate
                    thenHave(thesis) by Substitution.ApplyRules(uwEq)
                  }

                  // app v pr = uw
                  val appEq = have(app(v, pr) === F(uw)) subproof {
                    val pairInV = have(in(pair(pr, F(uw)), v)) by Tautology.from(
                      setUnionMembership of (z -> pair(pr, F(uw)), x -> uw, y -> prFun),
                      singletonHasNoExtraElements of (x -> pair(pr, F(uw)), y -> pair(pr, F(uw)))
                    )
                    have(in(pr, initialSegment(p, x))) by Tautology.from(predecessorInInitialSegment of y -> pr, pIsATotalOrder)
                    have(thesis) by Tautology.from(vAppDef of (a -> F(uw), z -> pr), lastStep, pairInV)
                  }

                  have(thesis) by Tautology.from(equalityTransitivity of (x -> app(v, pr), y -> F(uw), z -> F(orderedRestriction(v, pr, p))), fuwEq, appEq)
                }

                thenHave(thesis) by Substitution.ApplyRules(z === pr)
              }

              // the property holds for elements < pr
              val wCase = have(in(z, initialSegment(p, pr)) |- (app(v, z) === F(orderedRestriction(v, z, p)))) subproof {
                assume(in(z, initialSegment(p, pr)))

                // uw is functional over <pr

                // ordered restriction of v to z is the same as uw to z
                val restrictionVW = have(orderedRestriction(v, z, p) === orderedRestriction(uw, z, p)) subproof {
                  have(orderedRestriction(uw, z, p) === orderedRestriction(uw, z, p)) by Restate
                  val doubleRestriction = thenHave(orderedRestriction(uw, z, p) === orderedRestriction(orderedRestriction(v, pr, p), z, p)) by Substitution.ApplyRules(uwEq)

                  have(orderedRestriction(orderedRestriction(v, pr, p), z, p) === orderedRestriction(v, z, p)) subproof {
                    // reduce to restricted functions

                    val intersectionEQ = have(setIntersection(initialSegment(p, pr), initialSegment(p, z)) === initialSegment(p, z)) subproof {
                      have(setIntersection(initialSegment(p, z), initialSegment(p, pr)) === initialSegment(p, z)) by Tautology.from(initialSegmentIntersection of (y -> z, x -> pr), pIsAPartialOrder)

                      thenHave(thesis) by Substitution.ApplyRules(setIntersectionCommutativity of (x -> initialSegment(p, z), y -> initialSegment(p, pr)))
                    }

                    have(orderedRestriction(orderedRestriction(v, pr, p), z, p) === orderedRestriction(orderedRestriction(v, pr, p), z, p)) by Restate
                    thenHave(orderedRestriction(orderedRestriction(v, pr, p), z, p) === restrictedFunction(orderedRestriction(v, pr, p), initialSegment(p, z))) by Substitution.ApplyRules(
                      ordBreakdown of (a -> orderedRestriction(v, pr, p), b -> z)
                    )
                    thenHave(orderedRestriction(orderedRestriction(v, pr, p), z, p) === restrictedFunction(restrictedFunction(v, initialSegment(p, pr)), initialSegment(p, z))) by Substitution
                      .ApplyRules(
                        ordBreakdown of (a -> v, b -> pr)
                      )
                    thenHave(orderedRestriction(orderedRestriction(v, pr, p), z, p) === restrictedFunction(v, setIntersection(initialSegment(p, pr), initialSegment(p, z)))) by Substitution
                      .ApplyRules(
                        restrictedFunctionAbsorption of (f -> v, x -> initialSegment(p, pr), y -> initialSegment(p, z))
                      )
                    thenHave(orderedRestriction(orderedRestriction(v, pr, p), z, p) === restrictedFunction(v, initialSegment(p, z))) by Substitution.ApplyRules(intersectionEQ)
                    thenHave(thesis) by Substitution.ApplyRules(ordBreakdown of (a -> v, b -> z))
                  }

                  have(thesis) by Tautology.from(
                    lastStep,
                    doubleRestriction,
                    equalityTransitivity of (x -> orderedRestriction(uw, z, p), y -> orderedRestriction(orderedRestriction(v, pr, p), z, p), z -> orderedRestriction(v, z, p))
                  )
                }

                val restrictionFVW = have(F(orderedRestriction(v, z, p)) === F(orderedRestriction(uw, z, p))) subproof {
                  have(F(orderedRestriction(v, z, p)) === F(orderedRestriction(v, z, p))) by Restate
                  thenHave(thesis) by Substitution.ApplyRules(restrictionVW)
                }

                // app v z = app uw z
                val appVW = have(app(v, z) === app(uw, z)) subproof {
                  have(app(uw, z) === app(uw, z)) by Restate
                  val uwToOrd = thenHave(app(uw, z) === app(orderedRestriction(v, pr, p), z)) by Substitution.ApplyRules(uwEq)

                  have(orderedRestriction(v, pr, p) === restrictedFunction(v, initialSegment(p, pr))) by InstantiateForall(orderedRestriction(v, pr, p))(
                    orderedRestriction.definition of (f -> v, a -> pr)
                  )
                  val uwToRest = have(app(uw, z) === app(restrictedFunction(v, initialSegment(p, pr)), z)) by Substitution.ApplyRules(lastStep)(uwToOrd)

                  have(app(restrictedFunction(v, initialSegment(p, pr)), z) === app(v, z)) by Tautology.from(restrictedFunctionApplication of (f -> v, x -> initialSegment(p, pr), y -> z))
                  have(app(uw, z) === app(v, z)) by Substitution.ApplyRules(lastStep)(uwToRest)

                }

                // app uw z = F (uw |^ z)
                val appRestrictionUW = have(app(uw, z) === F(orderedRestriction(uw, z, p))) subproof {
                  // z in dom uw
                  have(in(z, relationDomain(uw))) subproof {
                    // z < pr < x
                    // \exists g \in w. fun g pr
                    // z in dom g
                    // so z in dom uw
                    val zLTpr = have(in(z, initialSegment(p, pr))) by Restate
                    val prLTx = have(in(pr, initialSegment(p, x))) by Tautology.from(predecessorInInitialSegment of y -> pr, pIsATotalOrder)

                    have(thesis) by Tautology.from(zLTpr, prLTx, zyInDomUw of y -> pr)
                  }

                  have(thesis) by Tautology.from(lastStep, uwRestrictedEq)
                }

                // equality transitivity
                have(app(v, z) === F(orderedRestriction(uw, z, p))) by Tautology.from(
                  equalityTransitivity of (x -> app(v, z), y -> app(uw, z), z -> F(orderedRestriction(uw, z, p))),
                  appVW,
                  appRestrictionUW
                )
                have(app(v, z) === F(orderedRestriction(v, z, p))) by Tautology.from(
                  equalityTransitivity of (x -> app(v, z), y -> F(orderedRestriction(uw, z, p)), z -> F(orderedRestriction(v, z, p))),
                  lastStep,
                  restrictionFVW
                )
              }

              have(thesis) by Tautology.from(zSplit, prCase, wCase)
            }

            thenHave(in(z, initialSegment(p, x)) ==> (app(v, z) === F(orderedRestriction(v, z, p)))) by Restate
            thenHave(thesis) by RightForall
          }

          have(fun(v, x)) by Tautology.from(vRecursive, vFunctionalOver)
        }

        val prExists = have(exists(pr, predecessor(p, pr, x))) by Tautology.from(successorElement.definition)

        have(predecessor(p, pr, x) |- exists(g, fun(g, x))) by RightExists(vFun)
        thenHave(exists(pr, predecessor(p, pr, x)) |- exists(g, fun(g, x))) by LeftExists
        have(thesis) by Cut(prExists, lastStep)
      }

      have(thesis) by Tautology.from(limSuccCases, limitCase, successorCase)
    }

    val funExists = thenHave(exists(w, wDef) |- exists(g, fun(g, x))) by LeftExists

    have(exists(w, wDef)) subproof {
      // restating the definition of w
      // val wDef = forall(t, in(t, w) <=> exists(y, in(y, initialSegment(p, x)) /\ fun(t, y)))
      // forall t. t \in w <=> \exists y < x. fun(t, y)

      // we know that there exists a *unique* g for each y in the initial segment
      // so, there is a functional map from the initial segment that produces these values
      // by replacement, we can take the image of the initial segment
      // restating replacement:
      // forall(a, in(a, x) ==> existsOne(b, sPsi(x, a, b))) ==>
      //      exists(y, forall(b, in(b, y) <=> exists(a, in(a, x) /\ sPsi(x, a, b))))
      val sPsi = SchematicPredicateLabel("P", 3)

      have(forall(y, in(y, initialSegment(p, x)) ==> existsOne(g, fun(g, y)))) by Restate
      have(exists(w, forall(t, in(t, w) <=> exists(y, in(y, initialSegment(p, x)) /\ fun(t, y))))) by Tautology.from(
        lastStep,
        replacementSchema of (x -> initialSegment(p, x), sPsi -> lambda(Seq(x, y, g), fun(g, y)))
      )
    }

    have(thesis) by Tautology.from(lastStep, funExists)
  }

  /**
   * Theorem --- Well-Ordered Recursion
   *
   * Given any element `t` of a well order `p`, and a class function `F`, there
   * exists a unique function `g` with `<t`, the initial segment of `t`, as its
   * domain, defined recursively as
   *
   * `\forall a < t. g(a) = F(g |^ < a)`
   *
   * where `g |^ <a` is `g` with its domain restricted to `<a`, the initial
   * segment of `a`.
   */
  val wellOrderedRecursion = Lemma(
    wellOrder(p) |- forall(
      t,
      in(t, firstInPair(p)) ==> existsOne(g, (functionalOver(g, initialSegment(p, t)) /\ forall(a, in(a, initialSegment(p, t)) ==> (app(g, a) === F(orderedRestriction(g, a, p))))))
    )
  ) {
    assume(wellOrder(p))

    val pIsAPartialOrder = have(partialOrder(p)) by Tautology.from(wellOrder.definition, totalOrder.definition)
    val pIsATotalOrder = have(totalOrder(p)) by Tautology.from(wellOrder.definition)

    // the existence of g propagates up from initial segments
    val initPropagate = have(in(x, p1) ==> (forall(y, in(y, initialSegment(p, x)) ==> prop(y)) ==> prop(x))) subproof {

      assume(
        in(x, p1),
        forall(y, in(y, initialSegment(p, x)) ==> prop(y))
      )

      // see [[uniqueRecursiveFunction]] and [[recursiveFunctionExistencePropagates]]

      have(thesis) by Tautology.from(recursiveFunctionExistencePropagates, uniqueRecursiveFunction of t -> x)
    }

    // so we induct on the well-ordering
    thenHave(forall(x, in(x, p1) ==> (forall(y, in(y, initialSegment(p, x)) ==> prop(y)) ==> prop(x)))) by RightForall
    have(thesis) by Tautology.from(lastStep, wellOrderedInduction of Q -> lambda(x, prop(x)))
  }
  show

  /**
   * Theorem --- Transfinite Recursion
   *
   * Given any ordinal `a` and a class function `F`, there exists a unique
   * function `g` with `a` as its domain, defined recursively as
   *
   * `\forall b < a. g(b) = F(g |^ b)`
   *
   * where `g |^ b` is `g` with its domain restricted to `b`.
   */
  val transfiniteRecursion = Theorem(
    ordinal(a) |- existsOne(g, functionalOver(g, a) /\ forall(b, in(b, a) ==> (app(g, b) === F(restrictedFunction(g, b)))))
  ) {
    sorry
  }

}
