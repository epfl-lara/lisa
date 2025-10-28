package lisa.maths.SetTheory.Order.WellOrders

import lisa.maths.SetTheory.Base.Predef.{*, given}

/**
 * This file is dedicated to proving the well-ordered and transfinite recursion
 * theorems. Auxiliary lemmas are sections of the recursion proof separated out
 * for readability and faster compilation.
 */
object OldRecursion extends lisa.Main {
  /*
  // var defs
  private val w = variable[Ind]
  private val h = variable[Prop]
  private val t = variable[Ind]
  private val t1 = variable[Ind]
  private val t2 = variable[Ind]

  // relation and function symbols
  private val r = variable[Ind]
  private val p = variable[Ind]
  private val q = variable[Ind]
  private val F = variable[Set >>: Set]
  private val G = variable[Set >>: Set >>: Set]

  private val Q = variable[Set >>: Set]

  // Well-Ordered Recursion

  // superficial abbreviations
  def fun(g: Expr[Ind], t: Expr[Ind]): Expr[Prop] = (functionalOver(g, initialSegment(p, t)) /\ ∀(a, ∈(a, initialSegment(p, t)) ==> (app(g, a) === F(orderedRestriction(g, a, p)))))
  def prop(t: Expr[Ind]): Expr[Prop] = ∈(t, A) /\ ∃!(g, fun(g, t))

  // Lemmas:

  /**
   * Theorem --- Unique Recursive Function
   *
   * If a theorem as defined by [[wellOrderedRecursion]] ∃, it is unique
   */
  val uniqueRecursiveFunction = Lemma(
    (wellOrder(A)(<), ∃(g, fun(g, t)), t ∈ A) |- ∃!(g, fun(g, t))
  ) {
    assume(wellOrder(A)(<))
    assume(t ∈ A)

    // pt is a well order over t, which is needed for induction
    val pt: Expr[Ind] = (initialSegment(p, t), initialSegmentOrder(p, t))
    val ptWO = have(wellOrder(pt)) by Weakening(initialSegmentWellOrdered of a -> t)

    // suppose there exist two such distinct functions g1 and g2
    val g1 = variable
    val g2 = variable

    // expansion of ordered restriction
    val ordResDef = have(orderedRestriction(g, z, p) === restrictedFunction(g, initialSegment(p, z))) subproof {
      have(∀(b, (b === orderedRestriction(g, z, p)) <=> (b === restrictedFunction(g, initialSegment(p, z))))) by Weakening(orderedRestriction.definition of (f -> g, a -> z))
      thenHave(thesis) by InstantiateForall(orderedRestriction(g, z, p))
    }

    // if g1 and g2 agree on the initial segment of an element < z, they must agree on z
    val initToz = have(
      fun(g1, t) /\ fun(g2, t) /\ !(g1 === g2) /\ ∈(z, initialSegment(p, t)) /\ ∀(
        b ∈ initialSegment(pt, z), (app(g1, b) === app(g2, b))
      ) |- (app(g1, z) === app(g2, z))
    ) subproof {
      assume(fun(g1, t))
      assume(fun(g2, t))
      assume(!(g1 === g2))
      assume(z ∈ initialSegment(p, t))
      assume(∀(b ∈ initialSegment(pt, z), (app(g1, b) === app(g2, b))))

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
        have(⊆(initialSegment(p, z), initialSegment(p, t))) subproof {
          have(∀(z, (z === initialSegment(p, t)) <=> ∀(b, ∈(b, z) <=> (∈(b, A) /\ ∈((b, t), <))))) by Weakening(initialSegment.definition of a -> t)
          thenHave(∀(b, ∈(b, initialSegment(p, t)) <=> (∈(b, A) /\ ∈((b, t), <)))) by InstantiateForall(initialSegment(p, t))
          thenHave(∈(z, initialSegment(p, t)) <=> (∈(z, A) /\ ∈((z, t), <))) by InstantiateForall(z)
          val zLTt = thenHave(∈((z, t), <)) by Tautology

          have(partialOrder(p)) by Tautology.from(wellOrder.definition, totalOrder.definition)

          have(thesis) by Tautology.from(lastStep, zLTt, initialSegmentsSubset of (x -> z, y -> t), wellOrder.definition, strictTotalOrder.definition)
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
        have(∀(z, (z === initialSegment(x, y)) <=> ∀(t, ∈(t, z) <=> (∈(t, fst(x)) /\ ∈((t, y), snd(x)))))) by Weakening(
          initialSegment.definition of (p -> x, a -> y)
        )
        thenHave(∀(t, ∈(t, initialSegment(x, y)) <=> (∈(t, fst(x)) /\ ∈((t, y), snd(x))))) by InstantiateForall(initialSegment(x, y))
        val initXY = thenHave(∈(c, initialSegment(x, y)) <=> (∈(c, fst(x)) /\ ∈((c, y), snd(x)))) by InstantiateForall(c)

        // forward
        val fwd = have(∈(b, initialSegment(pt, z)) |- ∈(b, initialSegment(p, z))) subproof {
          assume(∈(b, initialSegment(pt, z)))

          have(∈(b, fst(pt))) by Tautology.from(initXY of (x -> pt, y -> z, c -> b))
          val bpt = thenHave(∈(b, initialSegment(p, t))) by Substitution.ApplyRules(fstReduction of (x -> initialSegment(p, t), y -> initialSegmentOrder(p, t)))
          have(∈(b, initialSegment(p, t)) ==> ∈(b, A)) by Tautology.from(initXY of (x -> p, y -> t, c -> b))
          val bInA = have(∈(b, A)) by Tautology.from(lastStep, bpt)

          val bzInP2 = have(∈((b, z), <)) subproof {
            have(∈(z, initialSegment(p, t))) by Restate
            val zt = have(∈((z, t), <)) by Tautology.from(lastStep, initXY of (x -> p, y -> t, c -> z))

            have(∈((b, z), snd(pt))) by Tautology.from(initXY of (x -> pt, y -> z, c -> b))
            val bzpt = thenHave(∈((b, z), initialSegmentOrder(p, t))) by Substitution.ApplyRules(sndReduction of (x -> initialSegment(p, t), y -> initialSegmentOrder(p, t)))

            have(thesis) subproof {
              have(
                ∀(
                  z,
                  (z === initialSegmentOrder(p, t)) <=> ∀(a, ∈(a, z) <=> (∈(a, snd(p)) /\ (∈(fst(a), initialSegment(p, t)) /\ ∈(snd(a), initialSegment(p, t)))))
                )
              ) by Weakening(initialSegmentOrder.definition of a -> t)
              thenHave(
                ∀(a, ∈(a, initialSegmentOrder(p, t)) <=> (∈(a, snd(p)) /\ (∈(fst(a), initialSegment(p, t)) /\ ∈(snd(a), initialSegment(p, t)))))
              ) by InstantiateForall(initialSegmentOrder(p, t))
              thenHave(
                ∈((b, z), initialSegmentOrder(p, t)) <=> (∈((b, z), snd(p)) /\ (∈(fst((b, z)), initialSegment(p, t)) /\ ∈(
                  snd((b, z)),
                  initialSegment(p, t)
                )))
              ) by InstantiateForall((b, z))
              have(thesis) by Tautology.from(lastStep, bzpt)
            }
          }

          have(thesis) by Tautology.from(bInA, bzInP2, initXY of (x -> p, y -> z, c -> b))
        }

        // backward
        val bwd = have(∈(b, initialSegment(p, z)) |- ∈(b, initialSegment(pt, z))) subproof {
          assume(∈(b, initialSegment(p, z)))

          val bpt = have(∈(b, initialSegment(p, t))) subproof {
            val bInA = have(∈(b, A)) by Tautology.from(initXY of (x -> p, y -> z, c -> b))

            val bz = have(∈((b, z), <)) by Tautology.from(initXY of (x -> p, y -> z, c -> b))
            val zt = have(∈((z, t), <)) by Tautology.from(initXY of (x -> p, y -> t, c -> z))

            have(∀(w, ∀(y, ∀(z, (∈((w, y), <) /\ ∈((y, z), <)) ==> ∈((w, z), <))))) by Weakening(wellOrderTransitivity)
            thenHave((∈((b, z), <) /\ ∈((z, t), <)) ==> ∈((b, t), <)) by InstantiateForall(b, z, t)

            have(∈((b, t), <)) by Tautology.from(lastStep, bz, zt)
            have(thesis) by Tautology.from(lastStep, bInA, initXY of (x -> p, y -> t, c -> b))
          }

          val bzInP2 = have(∈((b, z), initialSegmentOrder(p, t))) subproof {
            have(
              ∀(
                z,
                (z === initialSegmentOrder(p, t)) <=> ∀(a, ∈(a, z) <=> (∈(a, snd(p)) /\ (∈(fst(a), initialSegment(p, t)) /\ ∈(snd(a), initialSegment(p, t)))))
              )
            ) by Weakening(initialSegmentOrder.definition of a -> t)
            thenHave(
              ∀(a, ∈(a, initialSegmentOrder(p, t)) <=> (∈(a, snd(p)) /\ (∈(fst(a), initialSegment(p, t)) /\ ∈(snd(a), initialSegment(p, t)))))
            ) by InstantiateForall(initialSegmentOrder(p, t))
            thenHave(
              ∈((b, z), initialSegmentOrder(p, t)) <=> (∈((b, z), snd(p)) /\ (∈(fst((b, z)), initialSegment(p, t)) /\ ∈(
                snd((b, z)),
                initialSegment(p, t)
              )))
            ) by InstantiateForall((b, z))
            val ordDef = thenHave(∈((b, z), initialSegmentOrder(p, t)) <=> (∈((b, z), snd(p)) /\ (∈(b, initialSegment(p, t)) /\ ∈(z, initialSegment(p, t))))) by Substitution
              .ApplyRules(fstReduction of (x -> b, y -> z), sndReduction of (x -> b, y -> z))

            val bz = have(∈((b, z), <)) by Tautology.from(initXY of (x -> p, y -> z, c -> b))
            have(thesis) by Tautology.from(ordDef, bz, bpt)
          }

          have(∈(b, initialSegment(pt, z)) <=> (∈(b, initialSegment(p, t)) /\ ∈((b, z), initialSegmentOrder(p, t)))) by Substitution.ApplyRules(
            fstReduction of (x -> initialSegment(p, t), y -> initialSegmentOrder(p, t)),
            sndReduction of (x -> initialSegment(p, t), y -> initialSegmentOrder(p, t))
          )(initXY of (x -> pt, y -> z, c -> b))
          have(thesis) by Tautology.from(lastStep, bpt, bzInP2)
        }

        // combine
        have(∈(b, initialSegment(p, z)) <=> ∈(b, initialSegment(pt, z))) by Tautology.from(fwd, bwd)
        thenHave(∀(b, ∈(b, initialSegment(p, z)) <=> ∈(b, initialSegment(pt, z)))) by RightForall
        have(thesis) by Tautology.from(lastStep, extensionalityAxiom of (x -> initialSegment(p, z), y -> initialSegment(pt, z)))
      }

      // on the restricted domain, app(orderedRestriction(g, z, p), b) = app(g, b)
      val ordApp = have(∀(b, ∈(b, initialSegment(pt, z)) ==> (app(orderedRestriction(g, z, p), b) === app(g, b)))) subproof {
        // b < z ==> g_z(b) = g(b)
        val bToApp = have(∈(b, initialSegment(p, z)) ==> (app(orderedRestriction(g, z, p), b) === app(g, b))) subproof {
          have(∈(b, initialSegment(p, z)) ==> (app(restrictedFunction(g, initialSegment(p, z)), b) === app(g, b))) by Tautology.from(
            restrictedFunctionApplication of (f -> g, x -> initialSegment(p, z), y -> b)
          )
          thenHave(thesis) by Substitution.ApplyRules(ordResDef)
        }

        // b <_t z ==> b < z
        val btTobz = have(∈(b, initialSegment(pt, z)) ==> ∈(b, initialSegment(p, z))) subproof {
          have(∈(b, initialSegment(pt, z)) ==> ∈(b, initialSegment(pt, z))) by Restate
          thenHave(thesis) by Substitution.ApplyRules(initPTEqual)
        }

        // so b <_t z ==> g_z(b) = g(b)
        have(∈(b, initialSegment(pt, z)) ==> (app(orderedRestriction(g, z, p), b) === app(g, b))) by Tautology.from(bToApp, btTobz)

        // quantify
        thenHave(thesis) by RightForall
      }

      // for every element ∈ the restricted domain, g1_z(b)  = g2_z(b)
      val eqOnDom = have(∀(b, ∈(b, initialSegment(pt, z)) ==> (app(orderedRestriction(g1, z, p), b) === app(orderedRestriction(g2, z, p), b)))) subproof {
        val unquantified = have(∈(b, initialSegment(pt, z)) |- (app(orderedRestriction(g1, z, p), b) === app(orderedRestriction(g2, z, p), b))) subproof {
          assume(∈(b, initialSegment(pt, z)))

          val instOrd = have((app(orderedRestriction(g, z, p), b) === app(g, b))) by InstantiateForall(b)(ordApp)

          val eqTg2zg1 = equalityTransitivity of (x -> app(orderedRestriction(g2, z, p), b), z -> app(orderedRestriction(g1, z, p), b), y -> app(g1, b))
          val eqTg1g2 = equalityTransitivity of (x -> app(orderedRestriction(g2, z, p), b), y -> app(g2, b), z -> app(g1, b))

          have(∈(b, initialSegment(pt, z)) ==> (app(g1, b) === app(g2, b))) by InstantiateForall
          thenHave(app(g1, b) === app(g2, b)) by Tautology
          have(thesis) by Tautology.from(lastStep, instOrd of g -> g1, instOrd of g -> g2, eqTg2zg1, eqTg1g2)
        }

        thenHave(∈(b, initialSegment(pt, z)) ==> (app(orderedRestriction(g1, z, p), b) === app(orderedRestriction(g2, z, p), b))) by Restate
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
          have(∀(a, ∈(a, initialSegment(p, t)) ==> (app(g, a) === F(orderedRestriction(g, a, p))))) by Restate
          thenHave(∈(z, initialSegment(p, t)) ==> (app(g, z) === F(orderedRestriction(g, z, p)))) by InstantiateForall(z)
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
    val eqZ = have(fun(g1, t) /\ fun(g2, t) /\ !(g1 === g2) |- ∀(z, ∈(z, initialSegment(p, t)) ==> (app(g1, z) === app(g2, z)))) subproof {
      assume(fun(g1, t) /\ fun(g2, t) /\ !(g1 === g2))
      have(∈(z, initialSegment(p, t)) |- ∀(b, ∈(b, initialSegment(pt, z)) ==> (app(g1, b) === app(g2, b))) ==> (app(g1, z) === app(g2, z))) by Weakening(
        initToz
      )
      thenHave(
        ∈(z, fst(pt)) |- ∀(b, ∈(b, initialSegment(pt, z)) ==> (app(g1, b) === app(g2, b))) ==> (app(g1, z) === app(g2, z))
      ) by Substitution.ApplyRules(fstReduction of (x -> initialSegment(p, t), y -> initialSegmentOrder(p, t)))
      thenHave(
        ∈(z, fst(pt)) ==> (∀(b, ∈(b, initialSegment(pt, z)) ==> (app(g1, b) === app(g2, b))) ==> (app(g1, z) === app(g2, z)))
      ) by Restate
      thenHave(
        ∀(z, ∈(z, fst(pt)) ==> (∀(b, ∈(b, initialSegment(pt, z)) ==> (app(g1, b) === app(g2, b))) ==> (app(g1, z) === app(g2, z))))
      ) by RightForall
      have(
        ∀(z, ∈(z, fst(pt)) ==> (app(g1, z) === app(g2, z)))
      ) by Tautology.from(lastStep, ptWO, wellOrderedInduction of (p -> pt, Q -> lambda(x, app(g1, x) === app(g2, x))))
      thenHave(thesis) by Substitution.ApplyRules(fstReduction of (x -> initialSegment(p, t), y -> initialSegmentOrder(p, t)))
    }

    // so g1 = g2, but this is a contradiction
    val contra = have(fun(g1, t) /\ fun(g2, t) /\ !(g1 === g2) |- ()) subproof {
      assume(fun(g1, t) /\ fun(g2, t) /\ !(g1 === g2))
      have((g1 === g2)) by Tautology.from(eqZ, functionsEqualIfEqualOnDomain of (f -> g1, g -> g2, a -> initialSegment(p, t)))
      thenHave(thesis) by Restate
    }

    // so there ∃ a unique one, if there ∃ one at all
    have(!∃(g, fun(g, t)) \/ ∃!(g, fun(g, t))) subproof {
      have(fun(g1, t) /\ fun(g2, t) /\ !(g1 === g2) |- ()) by Restate.from(contra)
      thenHave(∃(g2, fun(g1, t) /\ fun(g2, t) /\ !(g1 === g2)) |- ()) by LeftExists
      thenHave(∃(g1, ∃(g2, fun(g1, t) /\ fun(g2, t) /\ !(g1 === g2))) |- ()) by LeftExists
      have(thesis) by Tautology.from(lastStep, atleastTwoExist of (P -> lambda(x, fun(x, t))))
    }

    thenHave(thesis) by Restate
  }

  // EXISTENCE ----------------------------------------

  // if there ∃ a unique function `g` for the initial segment of some `x`, get the set of these
  val wDef = ∀(t, (t ∈ w) <=> ∃(y ∈ initialSegment(p, x), fun(t, y)))

  // take its union
  // this is a function `g` for `x` (almost)
  val uw = ⋃(w) // + `(predecessor x, F(U w))` ∈ the successor case

  // properties of w / uw

  val elemsFunctional = Lemma(
    wDef |-
      ∀(t ∈ w, functional(t))
  ) {
    assume(wDef)
    have((t ∈ w) |- functional(t)) subproof {
      assume(t ∈ w)
      have(t ∈ w <=> ∃(y ∈ initialSegment(p, x), fun(t, y))) by InstantiateForall
      val exy = thenHave(∃(y, ∈(y, initialSegment(p, x)) /\ fun(t, y))) by Tautology

      have(∃(y, ∈(y, initialSegment(p, x)) /\ fun(t, y)) |- functional(t)) subproof {
        have(fun(t, y) |- functional(t)) by Tautology.from(functionalOver.definition of (f -> t, x -> initialSegment(p, y)))
        thenHave((∈(y, initialSegment(p, x)) /\ fun(t, y)) |- functional(t)) by Weakening
        thenHave(thesis) by LeftExists
      }

      have(thesis) by Cut(exy, lastStep)
    }
    thenHave(∈(t, w) ==> functional(t)) by Restate
    thenHave(thesis) by RightForall
  }

  val elemsSubset = Lemma(
    wellOrder(A)(<) /\ wDef |-
      ∀(t1, ∀(t2, (∈(t1, w) /\ ∈(t2, w)) ==> (⊆(t1, t2) \/ ⊆(t2, t1))))
  ) {
    assume(wDef, wellOrder(A)(<))

    have(∈(t1, w) /\ ∈(t2, w) |- ⊆(t1, t2) \/ ⊆(t2, t1)) subproof {
      assume(∈(t1, w))
      assume(∈(t2, w))

      // given t1 and t2
      // they must come from y1 and y2

      // if t1 == t2
      // done
      val t1EQt2 = have((t1 === t2) |- ⊆(t1, t2) \/ ⊆(t2, t1)) by Weakening(subsetEqualitySymmetry of (x -> t1, y -> t2))

      // if t1 != t2
      val t1NEQt2 = have(!(t1 === t2) |- ⊆(t1, t2) \/ ⊆(t2, t1)) subproof {
        assume(!(t1 === t2))
        def ytDef(y: Expr[Ind], t: Expr[Ind]) = ∈(y, initialSegment(p, x)) /\ fun(t, y)
        val y1 = variable
        val y2 = variable

        val initMemToA = have(∈(y, initialSegment(p, a)) |- ∈(y, A)) subproof {
          have(∀(y, ∈(y, initialSegment(p, a)) <=> (∈(y, A) /\ ∈((y, a), <)))) by InstantiateForall(initialSegment(p, a))(initialSegment.definition)
          thenHave(∈(y, initialSegment(p, a)) <=> (∈(y, A) /\ ∈((y, a), <))) by InstantiateForall(y)
          thenHave(thesis) by Tautology
        }

        have(ytDef(y1, t1) /\ ytDef(y2, t2) |- ⊆(t1, t2) \/ ⊆(t2, t1)) subproof {
          assume(ytDef(y1, t1))
          assume(ytDef(y2, t2))
          // cases:
          // y1 == y2
          // done by the uniqueness lemma above
          val yeq = have((y1 === y2) |- ⊆(t1, t2)) subproof {
            assume(y1 === y2)
            have(fun(t1, y1) /\ fun(t2, y2)) by Restate
            thenHave(fun(t1, y1) /\ fun(t2, y1)) by Substitution.ApplyRules(y1 === y2)
            thenHave(fun(t1, y1) /\ fun(t2, y1) /\ !(t1 === t2)) by Tautology
            thenHave(∃(t2, fun(t1, y1) /\ fun(t2, y1) /\ !(t1 === t2))) by RightExists
            thenHave(∃(t1, ∃(t2, fun(t1, y1) /\ fun(t2, y1) /\ !(t1 === t2)))) by RightExists
            have(∃(t1, fun(t1, y1)) /\ !∃!(t1, fun(t1, y1))) by Tautology.from(lastStep, atleastTwoExist of P -> lambda(t1, fun(t1, y1)))
            have(bot) by Tautology.from(lastStep, uniqueRecursiveFunction of t -> y1, initMemToA of (y -> y1, a -> x))
            thenHave(thesis) by Weakening
          }

          // y1 != y2
          // real work to be done here :-
          val neq = have(!(y1 === y2) |- ⊆(t1, t2) \/ ⊆(t2, t1)) subproof {
            assume(!(y1 === y2))

            // y1 < y2 or y2 < y1?
            // we prove it ∈ the generic case
            val a1 = variable
            val a2 = variable
            val k1 = variable
            val k2 = variable
            val ltToSubset = have(ytDef(a1, k1) /\ ytDef(a2, k2) /\ ∈((a1, a2), <) |- ⊆(k1, k2)) subproof {
              assume(ytDef(a1, k1))
              assume(ytDef(a2, k2))
              assume(∈((a1, a2), <))
              // fun(k1, a1)
              // fun(k2, a2)
              // a1 < a2
              // we should have k1 \subseteq k2

              // dom k1 \subseteq dom k2
              val domSubset =
                have(⊆(initialSegment(p, a1), initialSegment(p, a2))) by Tautology.from(initialSegmentsSubset of (x -> a1, y -> a2), wellOrder.definition, strictTotalOrder.definition)

              // suppose there is a minimal n such that k1 n != k2 n
              val n = variable
              val nDef =
                ∈(n, initialSegment(p, a1)) /\ !(app(k1, n) === app(k2, n)) /\ ∀(b, (∈(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b))) ==> (∈((n, b), <) \/ (n === b)))

              // if k1 and k2 disagree at all
              val k1k2disagree = ∃(n, ∈(n, initialSegment(p, a1)) /\ !(app(k1, n) === app(k2, n)))

              val nExists = have(k1k2disagree |- ∃(n, nDef)) subproof {
                assume(k1k2disagree)

                // B defined by x => x < a1 /\ k1 x != k2 x ∃
                val B = variable
                val BDef = ∀(x, ∈(x, B) <=> (∈(x, initialSegment(p, a1)) /\ !(app(k1, x) === app(k2, x))))
                val BExists = have(∃(B, BDef)) by Weakening(comprehensionSchema of (z -> initialSegment(p, a1), φ -> lambda(x, !(app(k1, x) === app(k2, x)))))

                // B forms a ⊆ of A
                val subsetB = have(BDef |- ⊆(B, A)) subproof {
                  assume(BDef)
                  have(∈(y, B) <=> (∈(y, initialSegment(p, a1)) /\ !(app(k1, y) === app(k2, y)))) by InstantiateForall
                  have(∈(y, B) ==> ∈(y, A)) by Tautology.from(lastStep, initMemToA of a -> a1)
                  thenHave(∀(y, ∈(y, B) ==> ∈(y, A))) by RightForall
                  have(thesis) by Tautology.from(lastStep, subsetAxiom of (x -> B, y -> A))
                }

                // B is non-empty
                val nonEmptyB = have(BDef |- !(B === emptySet)) subproof {
                  assume(BDef)
                  have(∈(n, B) <=> (∈(n, initialSegment(p, a1)) /\ !(app(k1, n) === app(k2, n)))) by InstantiateForall
                  thenHave((∈(n, initialSegment(p, a1)) /\ !(app(k1, n) === app(k2, n))) |- ∈(n, B)) by Weakening
                  have((∈(n, initialSegment(p, a1)) /\ !(app(k1, n) === app(k2, n))) |- !(B === emptySet)) by Cut(lastStep, setWithElementNonEmpty of (y -> n, x -> B))
                  thenHave(thesis) by LeftExists
                }

                // so it has a minimal element
                val minimalB = have(BDef |- ∃(n, nDef)) subproof {
                  assume(BDef)
                  have(∀(B, (⊆(B, A) /\ !(B === emptySet)) ==> ∃(n, ∈(n, B) /\ ∀(b, ∈(b, B) ==> (∈((n, b), <) \/ (n === b)))))) by Tautology.from(
                    wellOrder.definition
                  )
                  thenHave((⊆(B, A) /\ !(B === emptySet)) ==> ∃(n, ∈(n, B) /\ ∀(b, ∈(b, B) ==> (∈((n, b), <) \/ (n === b))))) by InstantiateForall(B)
                  val exN = have(∃(n, ∈(n, B) /\ ∀(b, ∈(b, B) ==> (∈((n, b), <) \/ (n === b))))) by Tautology.from(lastStep, nonEmptyB, subsetB)

                  // transform n \∈ B to n < a1 /\ k1 n != k2 n
                  have(∈(b, B) <=> (∈(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b)))) by InstantiateForall
                  thenHave(
                    (∈(b, B) ==> (∈((n, b), <) \/ (n === b))) <=> ((∈(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b))) ==> (∈((n, b), <) \/ (n === b)))
                  ) by Tautology
                  thenHave(
                    ∀(b, (∈(b, B) ==> (∈((n, b), <) \/ (n === b))) <=> ((∈(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b))) ==> (∈((n, b), <) \/ (n === b))))
                  ) by RightForall
                  val bEq = have(
                    ∀(b, ∈(b, B) ==> (∈((n, b), <) \/ (n === b))) <=> ∀(
                      b,
                      (∈(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b))) ==> (∈((n, b), <) \/ (n === b))
                    )
                  ) by Tautology.from(
                    lastStep,
                    universalEquivalenceDistribution of (P := lambda(b, ∈(b, B) ==> (∈((n, b), <) \/ (n === b))), Q := lambda(
                      b,
                      (∈(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b))) ==> (∈((n, b), <) \/ (n === b))
                    ))
                  )

                  have(∈(n, B) <=> (∈(n, initialSegment(p, a1)) /\ !(app(k1, n) === app(k2, n)))) by InstantiateForall
                  have(
                    (∈(n, B) /\ ∀(b, ∈(b, B) ==> (∈((n, b), <) \/ (n === b)))) <=> (∈(n, initialSegment(p, a1)) /\ !(app(k1, n) === app(k2, n)) /\ ∀(
                      b,
                      (∈(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b))) ==> (∈((n, b), <) \/ (n === b))
                    ))
                  ) by Tautology.from(lastStep, bEq)
                  thenHave(
                    ∀(
                      n,
                      (∈(n, B) /\ ∀(b, ∈(b, B) ==> (∈((n, b), <) \/ (n === b)))) <=> (∈(n, initialSegment(p, a1)) /\ !(app(k1, n) === app(k2, n)) /\ ∀(
                        b,
                        (∈(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b))) ==> (∈((n, b), <) \/ (n === b))
                      ))
                    )
                  ) by RightForall

                  have(thesis) by Tautology.from(
                    lastStep,
                    exN,
                    existentialEquivalenceDistribution of (P -> lambda(n, (∈(n, B) /\ ∀(b, ∈(b, B) ==> (∈((n, b), <) \/ (n === b))))), Q -> lambda(
                      n,
                      (∈(n, initialSegment(p, a1)) /\ !(app(k1, n) === app(k2, n)) /\ ∀(
                        b,
                        (∈(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b))) ==> (∈((n, b), <) \/ (n === b))
                      ))
                    ))
                  )
                }

                thenHave(∃(B, BDef) |- ∃(n, nDef)) by LeftExists
                have(thesis) by Cut(BExists, lastStep)
              }

              // but k1 n == F(k1 |^ n) and k2 n == F(k2 |^ n)
              val fK1 = have(nDef |- app(k1, n) === F(orderedRestriction(k1, n, p))) subproof {
                // n < a1 ==> k1 n = F(k1 |^ n)
                have(∀(b, ∈(b, initialSegment(p, a1)) ==> (app(k1, b) === F(orderedRestriction(k1, b, p))))) by Tautology
                thenHave(∈(n, initialSegment(p, a1)) ==> (app(k1, n) === F(orderedRestriction(k1, n, p)))) by InstantiateForall(n)

                // we know n < a1, so result
                thenHave(thesis) by Tautology
              }
              val fK2 = have(nDef |- app(k2, n) === F(orderedRestriction(k2, n, p))) subproof {
                // n < a2 ==> k2 n = F(k2 |^ n)
                have(∀(b, ∈(b, initialSegment(p, a2)) ==> (app(k2, b) === F(orderedRestriction(k2, b, p))))) by Tautology
                val impl = thenHave(∈(n, initialSegment(p, a2)) ==> (app(k2, n) === F(orderedRestriction(k2, n, p)))) by InstantiateForall(n)

                // n < a1 and a1 < a2, so n < a2
                have(∀(b, ∈(b, initialSegment(p, a1)) ==> ∈(b, initialSegment(p, a2)))) by Tautology.from(
                  domSubset,
                  subsetAxiom of (x -> initialSegment(p, a1), y -> initialSegment(p, a2))
                )
                thenHave(∈(n, initialSegment(p, a1)) ==> ∈(n, initialSegment(p, a2))) by InstantiateForall(n)

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
                  val mDef = ∈(m, initialSegment(p, n)) /\ !(app(orderedRestriction(k1, n, p), m) === app(orderedRestriction(k2, n, p), m))
                  val mExists = have(∃(m, mDef)) subproof {
                    // k1 |^ n != k2 |^ n by assumption
                    val k1k2unequal = have(!(orderedRestriction(k1, n, p) === orderedRestriction(k2, n, p))) by Restate

                    // they are functions on the same domain
                    val k1k2functional = have(functionalOver(orderedRestriction(k1, n, p), initialSegment(p, n)) /\ functionalOver(orderedRestriction(k2, n, p), initialSegment(p, n))) subproof {
                      // n < a1 by definition
                      val nLTa1 = have(∈(n, initialSegment(p, a1))) by Restate

                      // but a1 < a2, so n < a2
                      have(∀(n, ∈(n, initialSegment(p, a1)) ==> ∈(n, initialSegment(p, a2)))) by Tautology.from(
                        domSubset,
                        subsetAxiom of (x -> initialSegment(p, a1), y -> initialSegment(p, a2))
                      )
                      thenHave(∈(n, initialSegment(p, a1)) ==> ∈(n, initialSegment(p, a2))) by InstantiateForall(n)
                      val nLTa2 = have(∈(n, initialSegment(p, a2))) by Tautology.from(lastStep, nLTa1)

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
                    have(!∀(m, ∈(m, initialSegment(p, n)) ==> (app(orderedRestriction(k1, n, p), m) === app(orderedRestriction(k2, n, p), m)))) by Tautology.from(
                      k1k2unequal,
                      k1k2functional,
                      functionsEqualIfEqualOnDomain of (f -> orderedRestriction(k1, n, p), g -> orderedRestriction(k2, n, p), a -> initialSegment(p, n))
                    )
                    thenHave(thesis) by Restate
                  }

                  // we must have m < n
                  val mViolatesRestricted =
                    have(mDef |- ∈(m, initialSegment(p, a1)) /\ !(app(orderedRestriction(k1, n, p), m) === app(orderedRestriction(k2, n, p), m)) /\ ∈((m, n), <)) subproof {
                      assume(mDef)
                      // we have n < a1
                      have(∀(z, (z === initialSegment(p, a)) <=> (∀(t, ∈(t, z) <=> (∈(t, A) /\ ∈((t, a), <)))))) by Weakening(initialSegment.definition)
                      val initSegMembership = thenHave((∀(t, ∈(t, initialSegment(p, a)) <=> (∈(t, A) /\ ∈((t, a), <))))) by InstantiateForall(initialSegment(p, a))

                      have(∈(n, initialSegment(p, a1)) <=> (∈(n, A) /\ ∈((n, a1), <))) by InstantiateForall(n)(initSegMembership of a -> a1)
                      val nLTa1 = thenHave(∈((n, a1), <)) by Tautology

                      // and m < n
                      have(∈(m, initialSegment(p, n)) <=> (∈(m, A) /\ ∈((m, n), <))) by InstantiateForall(m)(initSegMembership of a -> n)
                      val mLTn = thenHave(∈(m, A) /\ ∈((m, n), <)) by Tautology

                      // by transitivity, m < a1 as well
                      have(∀(w, ∀(y, ∀(z, (∈((w, y), <) /\ ∈((y, z), <)) ==> ∈((w, z), <))))) by Weakening(wellOrderTransitivity)
                      thenHave((∈((m, n), <) /\ ∈((n, a1), <)) ==> ∈((m, a1), <)) by InstantiateForall(m, n, a1)
                      val mLTa1 = have(∈(m, A) /\ ∈((m, a1), <)) by Tautology.from(lastStep, nLTa1, mLTn)

                      have(∈(m, initialSegment(p, a1)) <=> (∈(m, A) /\ ∈((m, a1), <))) by InstantiateForall(m)(initSegMembership of a -> a1)
                      have(thesis) by Tautology.from(lastStep, mLTa1, mLTn)
                    }

                  val mViolates = have(mDef |- ∈(m, initialSegment(p, a1)) /\ !(app(k1, m) === app(k2, m)) /\ ∈((m, n), <)) subproof {
                    assume(mDef)

                    val mInDom1 = have(∈(m, relationDomain(k1))) subproof {
                      val domEQ = have(initialSegment(p, a1) === relationDomain(k1)) by Tautology.from(functionalOver.definition of (f -> k1, x -> initialSegment(p, a1)))

                      have(∈(m, initialSegment(p, a1))) by Tautology.from(mViolatesRestricted)
                      thenHave(thesis) by Substitution.ApplyRules(domEQ)
                    }

                    val mInDom2 = have(∈(m, relationDomain(k2))) subproof {
                      val domEQ = have(initialSegment(p, a2) === relationDomain(k2)) by Tautology.from(functionalOver.definition of (f -> k2, x -> initialSegment(p, a2)))

                      val mLTa1 = have(∈(m, initialSegment(p, a1))) by Tautology.from(mViolatesRestricted)
                      have(∀(m, ∈(m, initialSegment(p, a1)) ==> ∈(m, initialSegment(p, a2)))) by Tautology.from(
                        subsetAxiom of (x -> initialSegment(p, a1), y -> initialSegment(p, a2)),
                        domSubset
                      )
                      thenHave(∈(m, initialSegment(p, a1)) ==> ∈(m, initialSegment(p, a2))) by InstantiateForall(m)
                      have(∈(m, initialSegment(p, a2))) by Tautology.from(lastStep, mLTa1)

                      thenHave(thesis) by Substitution.ApplyRules(domEQ)
                    }

                    // if the application is equal on the ordered restriction, it must be equal on the entire functions
                    have((app(orderedRestriction(k1, n, p), m) === app(orderedRestriction(k2, n, p), m)) <=> (app(k1, m) === app(k2, m))) by Tautology.from(
                      orderedRestrictionAgreement of (f -> k1, g -> k2, a -> n, b -> m),
                      wellOrder.definition, strictTotalOrder.definition,
                      mInDom1,
                      mInDom2
                    )
                    have(thesis) by Tautology.from(mViolatesRestricted, lastStep)
                  }

                  // but n was the minimal violation
                  // contradiction
                  have(mDef |- bot) subproof {
                    assume(mDef)
                    // m < a1 and k1 m != k2 m ==> n < m \/ n = m
                    have(∀(b, (∈(b, initialSegment(p, a1)) /\ !(app(k1, b) === app(k2, b))) ==> (∈((n, b), <) \/ (n === b)))) by Restate
                    thenHave((∈(m, initialSegment(p, a1)) /\ !(app(k1, m) === app(k2, m))) ==> (∈((n, m), <) \/ (n === m))) by InstantiateForall(m)
                    val mLeqn = have((∈((n, m), <) \/ (n === m))) by Tautology.from(lastStep, mViolates)

                    // we had m < n, and the order is anti-symmetric, so n = m
                    have(∀(n, ∀(m, (∈((m, n), <) /\ ∈((n, m), <)) ==> (n === m)))) by Tautology.from(
                      wellOrder.definition,
                      totalOrder.definition,
                      partialOrder.definition,
                      antiSymmetric.definition of (r -> <, x -> A)
                    )
                    thenHave((∈((m, n), <) /\ ∈((n, m), <)) ==> (n === m)) by InstantiateForall(n, m)
                    val nEQm = have((n === m)) by Tautology.from(lastStep, mViolates, mLeqn)

                    // however, that means n < n, but the order is anti-reflexive
                    have(∈((m, n), <)) by Weakening(mViolates)
                    val nLTn = thenHave(∈((n, n), <)) by Substitution.ApplyRules(nEQm)

                    have(∀(n, ∈(n, A) ==> !∈((n, n), <))) by Tautology.from(wellOrder.definition, strictTotalOrder.definition, partialOrder.definition, antiReflexive.definition of (r -> <, x -> A))
                    thenHave(∈(n, A) ==> !∈((n, n), <)) by InstantiateForall(n)
                    have(!∈((n, n), <)) by Tautology.from(lastStep, initialSegmentBaseElement of (x -> n, y -> a1), wellOrder.definition, strictTotalOrder.definition)

                    // this is a contradiction
                    have(thesis) by Tautology.from(lastStep, nLTn)
                  }
                  thenHave(∃(m, mDef) |- bot) by LeftExists
                  have(bot) by Cut(mExists, lastStep)
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
              thenHave(∃(n, nDef) |- ()) by LeftExists
              val disagreeCase = have(k1k2disagree |- ()) by Cut(nExists, lastStep)

              have(!k1k2disagree |- ⊆(k1, k2)) subproof {
                assume(!k1k2disagree)
                val impl = have(∀(b, ∈(b, initialSegment(p, a1)) ==> (app(k1, b) === app(k2, b)))) by Restate

                // k1 k2 are functional
                val funK1 = have(functionalOver(k1, initialSegment(p, a1))) by Tautology
                val funK2 = have(functionalOver(k2, initialSegment(p, a2))) by Tautology

                // // and <a1 \subseteq <a2
                val domSubset = have(⊆(initialSegment(p, a1), initialSegment(p, a2))) by Tautology.from(initialSegmentsSubset of (x -> a1, y -> a2), wellOrder.definition, strictTotalOrder.definition)

                have(thesis) by Tautology.from(impl, funK1, funK2, domSubset, functionsSubsetIfEqualOnSubsetDomain of (f -> k1, g -> k2, a -> initialSegment(p, a1), b -> initialSegment(p, a2)))
              }

              have(thesis) by Tautology.from(lastStep, disagreeCase)
            }

            // finally, instantiate to y1 < y2 and to y2 < y1
            val y1LTy2 = have(∈((y1, y2), <) |- ⊆(t1, t2)) by Restate.from(ltToSubset of (a1 -> y1, k1 -> t1, a2 -> y2, k2 -> t2))
            val y2LTy1 = have(∈((y2, y1), <) |- ⊆(t2, t1)) by Restate.from(ltToSubset of (a1 -> y2, k1 -> t2, a2 -> y1, k2 -> t1))

            // totality of the order means y1 < y2 or y2 < y1
            have(∈((y1, y2), <) \/ ∈((y2, y1), <)) subproof {
              have(∀(y1, ∀(y2, (∈(y1, A) /\ ∈(y2, A)) ==> (∈((y1, y2), <) \/ ∈((y2, y1), <) \/ (y1 === y2))))) by Tautology.from(
                wellOrder.definition,
                totalOrder.definition,
                total.definition of (r -> <, x -> A)
              )
              val impl = thenHave((∈(y1, A) /\ ∈(y2, A)) ==> (∈((y1, y2), <) \/ ∈((y2, y1), <) \/ (y1 === y2))) by InstantiateForall(y1, y2)

              // expand defs
              have(∀(z, (z === initialSegment(x, y)) <=> ∀(t, ∈(t, z) <=> (∈(t, fst(x)) /\ ∈((t, y), snd(x)))))) by Weakening(
                initialSegment.definition of (p -> x, a -> y)
              )
              thenHave(∀(t, ∈(t, initialSegment(x, y)) <=> (∈(t, fst(x)) /\ ∈((t, y), snd(x))))) by InstantiateForall(initialSegment(x, y))
              val initXY = thenHave(∈(c, initialSegment(x, y)) <=> (∈(c, fst(x)) /\ ∈((c, y), snd(x)))) by InstantiateForall(c)

              have(∈(y1, A) /\ ∈(y2, A)) by Tautology.from(initialSegmentBaseElement of (y -> x, x -> y1), initialSegmentBaseElement of (y -> x, x -> y2), wellOrder.definition, strictTotalOrder.definition)
              have(thesis) by Tautology.from(lastStep, impl)
            }

            have(thesis) by Tautology.from(lastStep, y1LTy2, y2LTy1)
            // sorry
          }

          have(thesis) by Tautology.from(yeq, neq)
        }

        thenHave((ytDef(y1, t1), ytDef(y2, t2)) |- ⊆(t1, t2) \/ ⊆(t2, t1)) by Restate
        thenHave((ytDef(y1, t1), ∃(y2, ytDef(y2, t2))) |- ⊆(t1, t2) \/ ⊆(t2, t1)) by LeftExists
        val exToRes = thenHave((∃(y1, ytDef(y1, t1)), ∃(y2, ytDef(y2, t2))) |- ⊆(t1, t2) \/ ⊆(t2, t1)) by LeftExists

        // wDef
        val exy = have(∈(b, w) <=> ∃(y, ∈(y, initialSegment(p, x)) /\ fun(b, y))) by InstantiateForall

        have(thesis) by Tautology.from(exToRes, exy of b -> t1, exy of b -> t2)
      }

      have(thesis) by Tautology.from(t1EQt2, t1NEQt2)
    }

    thenHave(∈(t1, w) /\ ∈(t2, w) ==> ⊆(t1, t2) \/ ⊆(t2, t1)) by Restate
    thenHave(∀(t2, ∈(t1, w) /\ ∈(t2, w) ==> ⊆(t1, t2) \/ ⊆(t2, t1))) by RightForall
    thenHave(∀(t1, ∀(t2, ∈(t1, w) /\ ∈(t2, w) ==> ⊆(t1, t2) \/ ⊆(t2, t1)))) by RightForall
  }

  val uwfunctional = Lemma(
    wDef /\ wellOrder(A)(<) |- functional(uw)
  ) {
    have(thesis) by Tautology.from(elemsFunctional, elemsSubset, unionOfFunctionSet of z -> w)
  }

  val uwRestrictedEq = Lemma(
    wellOrder(A)(<) /\ wDef /\ ∈(z, relationDomain(uw)) |- app(uw, z) === F(orderedRestriction(uw, z, p))
  ) {
    assume(wellOrder(A)(<), wDef)
    assume(∈(z, relationDomain(uw)))

    // \∃ g \∈ w. uw z = F g |^ z
    val gExists = have(∃(g, ∈(g, w) /\ ∈(z, relationDomain(g)) /\ (app(uw, z) === F(orderedRestriction(g, z, p))))) subproof {
      // dom uw = < x
      // val domUEq = have(relationDomain(uw) === initialSegment(p, x)) by Tautology.from(uwFunctionalOver, functionalOverImpliesDomain of (f -> uw, x -> initialSegment(p, x)))

      // z ∈ dom uw
      // have(∈(z, initialSegment(p, x))) by Restate
      // val zInDom = thenHave(∈(z, relationDomain(uw))) by EqualityReasoning.ApplyRules(domUEq)

      // so ∃ g \∈ w, z \∈ dom g
      have(functional(uw) /\ ∈(z, relationDomain(uw)) |- ∃(g, ∈(g, w) /\ ∈(z, relationDomain(g)))) by InstantiateForall(z)(domainOfFunctionalUnion of z -> w)
      val gExists = have(∃(g, ∈(g, w) /\ ∈(z, relationDomain(g)))) by Tautology.from(lastStep, uwfunctional)

      have((∈(g, w), ∈(z, relationDomain(g))) |- app(uw, z) === F(orderedRestriction(g, z, p))) subproof {
        assume(∈(g, w))
        assume(∈(z, relationDomain(g)))

        // given such a g, g(z) = uw(z)
        val gEqU = have(app(g, z) === app(uw, z)) subproof {
          have(
            (b === app(f, z)) <=> ((functional(f) /\ ∈(z, relationDomain(f))) ==> ∈((z, b), f)) /\ ((!functional(f) \/ !∈(z, relationDomain(f))) ==> (b === ∅))
          ) by InstantiateForall(b)(app.definition of x -> z)
          val appDef = thenHave(functional(f) /\ ∈(z, relationDomain(f)) |- (b === app(f, z)) <=> ∈((z, b), f)) by Tautology

          // for g z
          val gb = have((b === app(g, z)) <=> ∈((z, b), g)) subproof {
            // g is functional
            have(∈(g, w) ==> functional(g)) by InstantiateForall(g)(elemsFunctional)
            have(thesis) by Tautology.from(lastStep, appDef of f -> g)
          }

          // for uw z
          val uwb = have((b === app(uw, z)) <=> ∈((z, b), uw)) by Tautology.from(appDef of f -> uw, uwfunctional)

          // ∈ g ==> ∈ uw
          have(∈(t, g) ==> ∈(t, uw)) subproof {
            assume(∈(t, g))

            // suffices to show the existence of g
            val unionAx = have(∈(t, uw) <=> ∃(g, ∈(g, w) /\ ∈(t, g))) by Weakening(unionAxiom of (z -> t, x -> w))

            have(∈(g, w) /\ ∈(t, g)) by Restate
            thenHave(∃(g, ∈(g, w) /\ ∈(t, g))) by RightExists

            have(thesis) by Tautology.from(lastStep, unionAx)
          }

          // equal
          have((b === app(g, z)) |- (b === app(uw, z))) by Tautology.from(lastStep of t -> (z, b), gb, uwb)
          have(thesis) by Restate.from(lastStep of b -> app(g, z))
        }

        // we must also have g(z) = F(g |^ z)
        have(app(g, z) === F(orderedRestriction(g, z, p))) subproof {
          have(∈(g, w) <=> ∃(y, ∈(y, initialSegment(p, x)) /\ fun(g, y))) by InstantiateForall
          val yExists = thenHave(∃(y, ∈(y, initialSegment(p, x)) /\ fun(g, y))) by Tautology

          have(fun(g, y) |- app(g, z) === F(orderedRestriction(g, z, p))) subproof {
            assume(fun(g, y))

            // dom g = < y
            val domEq = have(relationDomain(g) === initialSegment(p, y)) by Tautology.from(functionalOverImpliesDomain of (f -> g, x -> initialSegment(p, y)))

            have(∀(a, ∈(a, initialSegment(p, y)) ==> (app(g, a) === F(orderedRestriction(g, a, p))))) by Restate
            thenHave(∈(z, initialSegment(p, y)) ==> (app(g, z) === F(orderedRestriction(g, z, p)))) by InstantiateForall(z)
            thenHave(∈(z, relationDomain(g)) ==> (app(g, z) === F(orderedRestriction(g, z, p)))) by Substitution.ApplyRules(domEq)
            thenHave(thesis) by Restate
          }
          thenHave(∈(y, initialSegment(p, x)) /\ fun(g, y) |- app(g, z) === F(orderedRestriction(g, z, p))) by Weakening
          thenHave(∃(y, ∈(y, initialSegment(p, x)) /\ fun(g, y)) |- app(g, z) === F(orderedRestriction(g, z, p))) by LeftExists
          have(thesis) by Cut(yExists, lastStep)
        }

        thenHave(thesis) by Substitution.ApplyRules(gEqU)
      }

      thenHave((∈(g, w) /\ ∈(z, relationDomain(g))) |- ∈(g, w) /\ ∈(z, relationDomain(g)) /\ (app(uw, z) === F(orderedRestriction(g, z, p)))) by Tautology
      thenHave((∈(g, w) /\ ∈(z, relationDomain(g))) |- ∃(g, ∈(g, w) /\ ∈(z, relationDomain(g)) /\ (app(uw, z) === F(orderedRestriction(g, z, p))))) by RightExists
      thenHave(∃(g, ∈(g, w) /\ ∈(z, relationDomain(g))) |- ∃(g, ∈(g, w) /\ ∈(z, relationDomain(g)) /\ (app(uw, z) === F(orderedRestriction(g, z, p))))) by LeftExists

      have(thesis) by Cut(gExists, lastStep)
    }

    // but g \∈ w ==> g |^ z = uw |^ z
    val gRestrictedEq = have(∈(g, w) /\ ∈(z, relationDomain(g)) |- orderedRestriction(g, z, p) === orderedRestriction(uw, z, p)) subproof {
      assume(∈(g, w))
      assume(∈(z, relationDomain(g)))

      val og = orderedRestriction(g, z, p)
      val ou = orderedRestriction(uw, z, p)

      // we prove this for a generic element t
      val ogDef = have(∈(t, og) <=> (∈(t, g) /\ ∈(fst(t), initialSegment(p, z)))) by Tautology.from(orderedRestrictionMembership of (f -> g, a -> z, b -> t), wellOrder.definition, strictTotalOrder.definition)

      val ouDef = have(∈(t, ou) <=> (∈(t, uw) /\ ∈(fst(t), initialSegment(p, z)))) by Tautology.from(orderedRestrictionMembership of (f -> uw, a -> z, b -> t), wellOrder.definition, strictTotalOrder.definition)

      // t \∈ g |^ z ==> t \∈ uw |^ z
      val fwd = have(∈(t, og) |- ∈(t, ou)) subproof {
        assume(∈(t, og))
        val tInG = have((∈(t, g) /\ ∈(fst(t), initialSegment(p, z)))) by Tautology.from(ogDef)

        // but g is a ⊆ of uw
        have(∈(t, g) ==> ∈(t, uw)) subproof {
          assume(∈(t, g))

          have(∈(g, w) /\ ∈(t, g)) by Restate
          thenHave(∃(g, ∈(g, w) /\ ∈(t, g))) by RightExists
          have(thesis) by Tautology.from(lastStep, unionAxiom of (x -> w, z -> t))
        }

        have(thesis) by Tautology.from(lastStep, tInG, ouDef)
      }

      // t \∈ uw |^ z ==> t \∈ g |^ z
      val bwd = have(∈(t, ou) |- ∈(t, og)) subproof {
        assume(∈(t, ou))
        val tInU = have((∈(t, uw) /\ ∈(fst(t), initialSegment(p, z)))) by Tautology.from(ouDef)

        // if t \∈ uw and t1 < z
        have(∈(t, uw) /\ ∈(fst(t), initialSegment(p, z)) |- ∈(t, g)) subproof {
          assume(∈(t, uw))
          assume(∈(fst(t), initialSegment(p, z)))

          // suppose ! t \∈ g
          have(!∈(t, g) |- ()) subproof {
            assume(!∈(t, g))

            // ∃ f \∈ w, t \∈ f by union axiom on uw
            val fExists = have(∃(f, ∈(f, w) /\ ∈(t, f))) by Tautology.from(unionAxiom of (x -> w, z -> t))

            // if such an f ∃
            have(∈(f, w) /\ ∈(t, f) |- ()) subproof {
              assume(∈(f, w))
              assume(∈(t, f))

              // f \subseteq g or g \subseteq f
              val cases = have(⊆(f, g) \/ ⊆(g, f)) subproof {
                have((∈(g, w) /\ ∈(f, w)) ==> (⊆(g, f) \/ ⊆(f, g))) by InstantiateForall(g, f)(elemsSubset)
                thenHave(thesis) by Tautology
              }

              // f \subseteq g ==> contradiction directly
              val fg = have(⊆(f, g) |- ()) subproof {
                assume(⊆(f, g))

                have(∀(t, ∈(t, f) ==> ∈(t, g))) by Tautology.from(subsetAxiom of (x -> f, y -> g))
                thenHave(∈(t, f) ==> ∈(t, g)) by InstantiateForall(t)
                thenHave(thesis) by Tautology
              }

              // g \subseteq f
              val gf = have(⊆(g, f) |- ()) subproof {
                assume(⊆(g, f))

                val t1 = fst(t)
                val t2 = snd(t)

                // t1 \∈ dom og
                val t1InDomOG = have(∈(t1, relationDomain(og))) subproof {
                  // t \∈ ou
                  // so t1 \∈ <z
                  val t1LTz = have(∈(t1, initialSegment(p, z))) by Tautology.from(ouDef)

                  // <z = dom og
                  have(relationDomain(og) === initialSegment(p, z)) subproof {
                    // dom g is < y for some y
                    have(∈(g, w) <=> ∃(y, ∈(y, initialSegment(p, x)) /\ fun(g, y))) by InstantiateForall
                    val yExists = thenHave(∃(y, ∈(y, initialSegment(p, x)) /\ fun(g, y))) by Tautology

                    have(∈(y, initialSegment(p, x)) /\ fun(g, y) |- relationDomain(og) === initialSegment(p, z)) subproof {
                      assume(∈(y, initialSegment(p, x)))
                      assume(fun(g, y))

                      // dom g = < y
                      have(functionalOver(g, initialSegment(p, y))) by Restate
                      val domEq = have(relationDomain(g) === initialSegment(p, y)) by Tautology.from(lastStep, functionalOver.definition of (f -> g, x -> initialSegment(p, y)))

                      // but z ∈ dom g, so z < y
                      have(∈((z, y), <)) subproof {
                        have(∈(z, relationDomain(g))) by Restate
                        thenHave(∈(z, initialSegment(p, y))) by Substitution.ApplyRules(domEq)
                        have(thesis) by Tautology.from(lastStep, initialSegmentElement of x -> z, wellOrder.definition, strictTotalOrder.definition)
                      }

                      // so < z \subseteq < y
                      val zySubset = have(⊆(initialSegment(p, z), initialSegment(p, y))) by Tautology.from(lastStep, initialSegmentsSubset of (x -> z, y -> y), wellOrder.definition, strictTotalOrder.definition)

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

                    thenHave(∃(y, ∈(y, initialSegment(p, x)) /\ fun(g, y)) |- relationDomain(og) === initialSegment(p, z)) by LeftExists
                    have(thesis) by Cut(yExists, lastStep)
                  }

                  // t1 \∈ dom g
                  have(thesis) by Substitution.ApplyRules(lastStep)(t1LTz)
                }

                // since t1 \∈ dom g, ∃ a. (t, a) \∈ g
                val aExists = have(∃(a, ∈((t1, a), g))) subproof {
                  have(∀(t, ∈(t, relationDomain(g)) <=> ∃(a, ∈((t, a), g)))) by InstantiateForall(relationDomain(g))(relationDomain.definition of r -> g)
                  val domIff = thenHave(∈(t1, relationDomain(g)) <=> ∃(a, ∈((t1, a), g))) by InstantiateForall(t1)

                  // t1 is ∈ dom og, so it is ∈ dom g
                  have(∈(t1, relationDomain(g))) subproof {
                    val ordEQ = have(og === restrictedFunction(g, initialSegment(p, z))) by InstantiateForall(og)(orderedRestriction.definition of (f -> g, a -> z))

                    have(relationDomain(restrictedFunction(g, initialSegment(p, z))) === setIntersection(initialSegment(p, z), relationDomain(g))) by Tautology.from(
                      restrictedFunctionDomain of (f -> g, x -> initialSegment(p, z))
                    )
                    thenHave(relationDomain(og) === setIntersection(initialSegment(p, z), relationDomain(g))) by Substitution.ApplyRules(ordEQ)

                    have(∀(b, ∈(b, relationDomain(og)) <=> ∈(b, setIntersection(initialSegment(p, z), relationDomain(g))))) by Tautology.from(
                      lastStep,
                      extensionalityAxiom of (x -> relationDomain(og), y -> setIntersection(initialSegment(p, z), relationDomain(g)))
                    )
                    thenHave(∈(t1, relationDomain(og)) <=> ∈(t1, setIntersection(initialSegment(p, z), relationDomain(g)))) by InstantiateForall(t1)
                    have(∈(t1, setIntersection(initialSegment(p, z), relationDomain(g)))) by Tautology.from(lastStep, t1InDomOG)
                    have(thesis) by Tautology.from(lastStep, setIntersectionMembership of (t -> t1, x -> initialSegment(p, z), y -> relationDomain(g)))
                  }

                  have(thesis) by Tautology.from(lastStep, domIff)
                }

                have(∈((t1, a), g) |- ()) subproof {
                  assume(∈((t1, a), g))

                  // (t1, a) \∈ f
                  have(∀(t, ∈(t, g) ==> ∈(t, f))) by Tautology.from(subsetAxiom of (x -> g, y -> f))
                  thenHave(∈((t1, a), g) ==> ∈((t1, a), f)) by InstantiateForall((t1, a))
                  val t1aInF = thenHave(∈((t1, a), f)) by Tautology

                  // t must be a 
                  val tIsPair = have(∃(a, ∃(b, (a, b) === t))) subproof {
                    have(∀(t, ∈(t, uw) ==> ∃(a, ∃(b, ((a, b) === t) /\ ∈(a, relationDomain(uw)))))) by Tautology.from(uwfunctional, functionalMembership of (f -> uw))
                    val exIn = thenHave(∃(a, ∃(b, ((a, b) === t) /\ ∈(a, relationDomain(uw))))) by InstantiateForall(t)

                    // eliminate extra terms inside ∃
                    have(∃(a, ∃(b, ((a, b) === t) /\ ∈(a, relationDomain(uw)))) |- ∃(a, ∃(b, ((a, b) === t)))) subproof {
                      have(((c, b) === t) /\ ∈(c, relationDomain(uw)) |- ((c, b) === t)) by Restate
                      thenHave(((c, b) === t) /\ ∈(c, relationDomain(uw)) |- ∃(b, ((c, b) === t))) by RightExists
                      thenHave(((c, b) === t) /\ ∈(c, relationDomain(uw)) |- ∃(c, ∃(b, ((c, b) === t)))) by RightExists
                      thenHave(∃(b, ((c, b) === t) /\ ∈(c, relationDomain(uw))) |- ∃(c, ∃(b, ((c, b) === t)))) by LeftExists
                      thenHave(∃(c, ∃(b, ((c, b) === t) /\ ∈(c, relationDomain(uw)))) |- ∃(c, ∃(b, ((c, b) === t)))) by LeftExists
                    }
                    have(thesis) by Cut(exIn, lastStep)
                  }
                  val tEqt1t2 = have(t === (t1, t2)) by Tautology.from(tIsPair, pairReconstruction of x -> t)

                  // but (t1, t2) \∈ f
                  val t1t2InF = have(∈((t1, t2), f)) subproof {
                    // t ∈ f
                    val tInF = have(∈(t, f)) by Restate

                    // so (t1, t2) = t
                    have(thesis) by Substitution.ApplyRules(tEqt1t2)(tInF)
                  }

                  // t2 = a
                  val t2Eqa = have(t2 === a) subproof {
                    // f is functional
                    have(∈(f, w) ==> functional(f)) by InstantiateForall(f)(elemsFunctional)

                    // given t1, there must be a unique element ∈ ran f it maps to
                    have(∀(t, ∃(b, ∈((t, b), f)) ==> ∃!(b, ∈((t, b), f)))) by Tautology.from(lastStep, functional.definition)
                    val exToExOne = thenHave(∃(b, ∈((t1, b), f)) |- ∃!(b, ∈((t1, b), f))) by InstantiateForall(t1)

                    have(∈((t1, a), f)) by Weakening(t1aInF)
                    val ex = thenHave(∃(b, ∈((t1, b), f))) by RightExists
                    val exOne = have(∃!(b, ∈((t1, b), f))) by Cut(lastStep, exToExOne)

                    have(∀(a, ∀(b, !∈((t1, a), f) \/ !∈((t1, b), f) \/ (a === b)))) by Tautology.from(atleastTwoExist of P -> lambda(a, ∈((t1, a), f)), ex, exOne)
                    thenHave(!∈((t1, a), f) \/ !∈((t1, t2), f) \/ (a === t2)) by InstantiateForall(a, t2)
                    have(thesis) by Tautology.from(lastStep, t1aInF, t1t2InF)
                  }

                  // but then (t1, t2) = t \∈ g
                  have(∈((t1, a), g)) by Restate
                  thenHave(∈((t1, t2), g)) by Substitution.ApplyRules(t2Eqa)
                  thenHave(∈(t, g)) by Substitution.ApplyRules(tEqt1t2)

                  // this is a contradiction
                  thenHave(thesis) by Tautology
                }

                thenHave(∃(a, ∈((t1, a), g)) |- ()) by LeftExists
                have(thesis) by Tautology.from(lastStep, aExists)
              }

              have(thesis) by Tautology.from(cases, gf, fg)
            }

            thenHave(∃(f, ∈(f, w) /\ ∈(t, f)) |- ()) by LeftExists
            have(thesis) by Tautology.from(lastStep, fExists)
          }
        }

        have(thesis) by Tautology.from(lastStep, tInU, ogDef)
      }

      have(∈(t, ou) <=> ∈(t, og)) by Tautology.from(fwd, bwd)
      thenHave(∀(t, ∈(t, ou) <=> ∈(t, og))) by RightForall
      have(ou === og) by Tautology.from(lastStep, extensionalityAxiom of (x -> ou, y -> og))
    }

    have(∈(g, w) /\ ∈(z, relationDomain(g)) /\ (app(uw, z) === F(orderedRestriction(g, z, p))) |- app(uw, z) === F(orderedRestriction(uw, z, p))) subproof {
      have(∈(g, w) /\ ∈(z, relationDomain(g)) /\ (app(uw, z) === F(orderedRestriction(g, z, p))) |- (app(uw, z) === F(orderedRestriction(g, z, p)))) by Restate
      thenHave(thesis) by Substitution.ApplyRules(gRestrictedEq)
    }

    thenHave(∃(g, ∈(g, w) /\ ∈(z, relationDomain(g)) /\ (app(uw, z) === F(orderedRestriction(g, z, p)))) |- app(uw, z) === F(orderedRestriction(uw, z, p))) by LeftExists
    have(thesis) by Tautology.from(gExists, lastStep)

  }

  val uniquenessFromExistsOne = Theorem(
    ∃!(x, P(x)) |- ∀(y, ∀(z, (P(y) /\ P(z)) ==> (y === z)))
  ) {
    val a1 = assume(∃(x, ∀(y, P(y) <=> (y === x))))
    val xe = witness(a1)
    have(P(y) <=> (y === xe)) by InstantiateForall(y)(xe.definition)
    val py = thenHave(P(y) |- y === xe) by Weakening
    have(P(z) <=> (z === xe)) by InstantiateForall(z)(xe.definition)
    val pz = thenHave(P(z) |- z === xe) by Weakening
    have((P(y), P(z)) |- (y === z)) by Substitution.ApplyRules(pz)(py)
    have((P(y) /\ P(z)) ==> (y === z)) by Tautology.from(lastStep)
    thenHave(∀(z, (P(y) /\ P(z)) ==> (y === z))) by RightForall
    thenHave(thesis) by RightForall

  }

  private val R = variable[Set >>: Set >>: Prop]
  val strictReplacementSchema = Theorem(
    ∀(x, ∈(x, A) ==> ∃!(y, R(x, y)))
      |- ∃(B, ∀(y, ∈(y, B) <=> ∃(x, ∈(x, A) /\ R(x, y))))
  ) {
    assume(∀(x, ∈(x, A) ==> ∃!(y, R(x, y))))
    thenHave(∈(x, A) ==> ∃!(y, R(x, y))) by InstantiateForall(x)
    have(∈(x, A) ==> ∀(y, ∀(z, (R(x, y) /\ R(x, z)) ==> (y === z)))) by Tautology.from(uniquenessFromExistsOne of (P := lambda(y, R(x, y))), lastStep)
    thenHave(∀(x, ∈(x, A) ==> ∀(y, ∀(z, (R(x, y) /\ R(x, z)) ==> (y === z))))) by RightForall
    have(thesis) by Tautology.from(lastStep, replacementSchema of (SchematicPredicateLabel("P", 2) -> R))
  }

  /**
   * Theorem --- Recursive Function ∃
   *
   * Given that for each element of the initial segment of `x`, a function as
   * defined by [[wellOrderedRecursion]] ∃, then a function with the same
   * properties ∃ for `x`.
   */
  val recursiveFunctionExistencePropagates = Theorem(
    wellOrder(A)(<) /\ ∈(x, A) /\ ∀(y, ∈(y, initialSegment(p, x)) ==> prop(y)) |- ∃(g, fun(g, x))
  ) {
    assume(wellOrder(A)(<))
    assume(∈(x, A))
    assume(∀(y, ∈(y, initialSegment(p, x)) ==> prop(y)))

    // if w is as defined, there is a function g as required
    have(wDef |- ∃(g, fun(g, x))) subproof {
      assume(wDef)
      // properties of the elements of w
      // 1. t \∈ w ==> functional t
      // 2. t1, t2 \∈ w ==> t1 \subseteq t2 \/ t2 \subseteq t1

      // 1. t \∈ w ==> functional t
      // see [[elemsFunctional]] and [[elemsSubset]]

      // working with orderedRestrictions
      val ordBreakdown = have(orderedRestriction(a, b, p) === restrictedFunction(a, initialSegment(p, b))) by InstantiateForall(orderedRestriction(a, b, p))(
        orderedRestriction.definition of (f -> a, a -> b)
      )

      // see [[uwfunctional]]

      // now, from w, we will construct the requisite function g for x
      // see [[uwRestrictedEq]]

      // common subproof
      val zyInDomUw = have(∈(z, initialSegment(p, y)) /\ ∈(y, initialSegment(p, x)) |- ∈(z, relationDomain(uw))) subproof {
        assume(∈(z, initialSegment(p, y)), ∈(y, initialSegment(p, x)))

        have(∈(y, initialSegment(p, x)) ==> (∈(y, A) /\ ∃!(g, fun(g, y)))) by InstantiateForall
        val gExists = have(∃(g, fun(g, y))) by Tautology.from(lastStep, existsOneImpliesExists of (P -> lambda(g, fun(g, y))))

        have(fun(g, y) |- ∈(z, relationDomain(uw))) subproof {
          assume(fun(g, y))

          val zIng = have(∈(z, relationDomain(g))) subproof {
            have(functionalOver(g, initialSegment(p, y))) by Tautology
            val domEQ = have(relationDomain(g) === initialSegment(p, y)) by Tautology.from(lastStep, functionalOver.definition of (f -> g, x -> initialSegment(p, y)))

            have(∈(z, initialSegment(p, y))) by Restate
            thenHave(thesis) by Substitution.ApplyRules(domEQ)
          }

          val gInw = have(∈(g, w)) subproof {
            have(∈(y, initialSegment(p, x)) /\ fun(g, y)) by Restate
            val yEx = thenHave(∃(y, ∈(y, initialSegment(p, x)) /\ fun(g, y))) by RightExists

            have(∀(t, ∈(t, w) <=> ∃(y, ∈(y, initialSegment(p, x)) /\ fun(t, y)))) by Restate
            thenHave(∈(g, w) <=> ∃(y, ∈(y, initialSegment(p, x)) /\ fun(g, y))) by InstantiateForall(g)
            have(thesis) by Tautology.from(lastStep, yEx)
          }

          have(∀(z, ∈(z, relationDomain(uw)) <=> ∃(g, ∈(g, w) /\ ∈(z, relationDomain(g))))) by Tautology.from(uwfunctional, domainOfFunctionalUnion of z -> w)
          val zInUiff = thenHave(∈(z, relationDomain(uw)) <=> ∃(g, ∈(g, w) /\ ∈(z, relationDomain(g)))) by InstantiateForall(z)

          have(∈(g, w) /\ ∈(z, relationDomain(g))) by Tautology.from(zIng, gInw)
          thenHave(∃(g, ∈(g, w) /\ ∈(z, relationDomain(g)))) by RightExists
          have(∈(z, relationDomain(uw))) by Tautology.from(lastStep, zInUiff)
        }

        thenHave(∃(g, fun(g, y)) |- ∈(z, relationDomain(uw))) by LeftExists
        have(∈(z, relationDomain(uw))) by Cut.withParameters(∃(g, fun(g, y)))(gExists, lastStep)
      }

      // there are two cases, either x has a predecessor, or it doesn't
      val limSuccCases = have(limitElement(p, x) \/ successorElement(p, x)) by Tautology.from(everyElemInTotalOrderLimitOrSuccessor, wellOrder.definition)

      // if x has no predecessor, i.e., it is a limit element, w is the required function
      val limitCase = have(limitElement(p, x) |- ∃(g, fun(g, x))) subproof {
        assume(limitElement(p, x))

        // <x = \cup <y

        // uw is a function on <x
        val uwFunctionalOver = have(functionalOver(uw, initialSegment(p, x))) subproof {
          val elem = variable
          val limitProp =
            have(∈((elem, x), <) ==> ∃(y, ∈((y, x), <) /\ ∈((elem, y), <))) by Tautology.from(initialSegmentUnionForLimitElementsIsComplete of t -> elem, wellOrder.definition)

          have(∀(t, ∈(t, relationDomain(uw)) <=> ∃(g, ∈(g, w) /\ ∈(t, relationDomain(g))))) by Tautology.from(domainOfFunctionalUnion of z -> w, uwfunctional)
          val domDef = thenHave(∈(elem, relationDomain(uw)) <=> ∃(g, ∈(g, w) /\ ∈(elem, relationDomain(g)))) by InstantiateForall(elem)

          have(∃(g, ∈(g, w) /\ ∈(elem, relationDomain(g))) <=> ∈(elem, initialSegment(p, x))) subproof {
            val fwd = have(∃(g, ∈(g, w) /\ ∈(elem, relationDomain(g))) |- ∈(elem, initialSegment(p, x))) subproof {
              have(∈(g, w) /\ ∈(elem, relationDomain(g)) |- ∈(elem, initialSegment(p, x))) subproof {
                assume(∈(g, w))
                assume(∈(elem, relationDomain(g)))

                // there must be a y < x that g is a recursive function for
                have(∈(g, w) <=> ∃(y, ∈(y, initialSegment(p, x)) /\ fun(g, y))) by InstantiateForall
                val yExists = thenHave(∃(y, ∈(y, initialSegment(p, x)) /\ fun(g, y))) by Tautology

                // elem is ∈ dom g, which is <y, so elem < y, and finally elem < x by transitivity
                have(∈(y, initialSegment(p, x)) /\ fun(g, y) |- ∈(elem, initialSegment(p, x))) subproof {
                  assume(∈(y, initialSegment(p, x)))
                  assume(fun(g, y))

                  have(relationDomain(g) === initialSegment(p, y)) by Tautology.from(functionalOver.definition of (f -> g, x -> initialSegment(p, y)))
                  have(∀(elem, ∈(elem, relationDomain(g)) <=> ∈(elem, initialSegment(p, y)))) by Tautology.from(
                    lastStep,
                    extensionalityAxiom of (x -> relationDomain(g), y -> initialSegment(p, y))
                  )
                  thenHave(∈(elem, relationDomain(g)) <=> ∈(elem, initialSegment(p, y))) by InstantiateForall(elem)
                  val eLTy = have(∈((elem, y), <)) by Tautology.from(lastStep, initialSegmentElement of x -> elem, wellOrder.definition, strictTotalOrder.definition)
                  val yLTx = have(∈((y, x), <)) by Tautology.from(initialSegmentElement of (x -> y, y -> x), wellOrder.definition, strictTotalOrder.definition)

                  // apply transitivity
                  have(∀(elem, ∀(y, ∀(x, (∈((elem, y), <) /\ ∈((y, x), <)) ==> ∈((elem, x), <))))) by Weakening(wellOrderTransitivity)
                  thenHave((∈((elem, y), <) /\ ∈((y, x), <)) ==> ∈((elem, x), <)) by InstantiateForall(elem, y, x)
                  have(∈((elem, x), <)) by Tautology.from(lastStep, eLTy, yLTx)
                  have(thesis) by Tautology.from(lastStep, initialSegmentElement of (y -> x, x -> elem), wellOrder.definition, strictTotalOrder.definition)
                }

                thenHave(∃(y, ∈(y, initialSegment(p, x)) /\ fun(g, y)) |- ∈(elem, initialSegment(p, x))) by LeftExists
                have(thesis) by Tautology.from(yExists, lastStep)
              }

              thenHave(thesis) by LeftExists
            }

            val bwd = have(∈(elem, initialSegment(p, x)) |- ∃(g, ∈(g, w) /\ ∈(elem, relationDomain(g)))) subproof {
              assume(∈(elem, initialSegment(p, x)))

              // find a y s.t. elem < y < x
              // this ∃ since x is a limit element
              val yExists = have(∃(y, ∈((elem, y), <) /\ ∈((y, x), <))) by Tautology.from(limitProp, initialSegmentElement of (y -> x, x -> elem), wellOrder.definition, strictTotalOrder.definition)

              // given y, there is a g which is defined recursively for y
              val gExists = have(∈((y, x), <) |- ∃(g, fun(g, y))) subproof {
                have(∈(y, initialSegment(p, x)) ==> (∈(y, A) /\ ∃!(g, fun(g, y)))) by InstantiateForall
                have(thesis) by Tautology.from(lastStep, initialSegmentElement of (x -> y, y -> x), existsOneImpliesExists of P -> lambda(g, fun(g, y)), wellOrder.definition, strictTotalOrder.definition)
              }

              // these g and y give us the required witness for elem
              have((∈((elem, y), <) /\ ∈((y, x), <), fun(g, y)) |- ∃(g, ∈(g, w) /\ ∈(elem, relationDomain(g)))) subproof {
                assume(∈((elem, y), <) /\ ∈((y, x), <))
                assume(fun(g, y))

                have(relationDomain(g) === initialSegment(p, y)) by Tautology.from(functionalOver.definition of (f -> g, x -> initialSegment(p, y)))
                have(∀(elem, ∈(elem, relationDomain(g)) <=> ∈(elem, initialSegment(p, y)))) by Tautology.from(
                  lastStep,
                  extensionalityAxiom of (x -> relationDomain(g), y -> initialSegment(p, y))
                )
                thenHave(∈(elem, relationDomain(g)) <=> ∈(elem, initialSegment(p, y))) by InstantiateForall(elem)

                val elemInDom = have(∈(elem, relationDomain(g))) by Tautology.from(lastStep, initialSegmentElement of x -> elem, wellOrder.definition, strictTotalOrder.definition)

                have(∈(y, initialSegment(p, x)) /\ fun(g, y)) by Tautology.from(initialSegmentElement of (x -> y, y -> x), wellOrder.definition, strictTotalOrder.definition)
                val yExists = thenHave(∃(y, ∈(y, initialSegment(p, x)) /\ fun(g, y))) by RightExists

                have(∈(g, w) <=> ∃(y, ∈(y, initialSegment(p, x)) /\ fun(g, y))) by InstantiateForall
                have(∈(g, w) /\ ∈(elem, relationDomain(g))) by Tautology.from(lastStep, yExists, elemInDom)
                thenHave(thesis) by RightExists
              }

              thenHave((∈((elem, y), <) /\ ∈((y, x), <), ∃(g, fun(g, y))) |- ∃(g, ∈(g, w) /\ ∈(elem, relationDomain(g)))) by LeftExists
              have((∈((elem, y), <) /\ ∈((y, x), <)) |- ∃(g, ∈(g, w) /\ ∈(elem, relationDomain(g)))) by Tautology.from(lastStep, gExists)
              thenHave(∃(y, ∈((elem, y), <) /\ ∈((y, x), <)) |- ∃(g, ∈(g, w) /\ ∈(elem, relationDomain(g)))) by LeftExists
              have(thesis) by Cut(yExists, lastStep)
            }

            have(thesis) by Tautology.from(fwd, bwd)
          }

          have(∈(elem, relationDomain(uw)) <=> ∈(elem, initialSegment(p, x))) by Tautology.from(lastStep, domDef)
          thenHave(∀(elem, ∈(elem, relationDomain(uw)) <=> ∈(elem, initialSegment(p, x)))) by RightForall
          have(relationDomain(uw) === initialSegment(p, x)) by Tautology.from(lastStep, extensionalityAxiom of (x -> relationDomain(uw), y -> initialSegment(p, x)))

          have(thesis) by Tautology.from(functionalOver.definition of (f -> uw, x -> initialSegment(p, x)), lastStep, uwfunctional)
        }

        // z < x ==> uw z = F uw |^ z
        have(∈(z, initialSegment(p, x)) |- app(uw, z) === F(orderedRestriction(uw, z, p))) subproof {
          assume(∈(z, initialSegment(p, x)))

          // z ∈ dom uw
          have(∈(z, relationDomain(uw))) subproof {
            // \∃ y. z < y < x as x is limit
            // \∃ g \∈ w. fun g y
            // z ∈ dom g
            // so z ∈ dom uw
            have(∈((z, x), <)) by Tautology.from(initialSegmentElement of (x -> z, y -> x), wellOrder.definition, strictTotalOrder.definition)
            val yExists = have(∃(y, ∈((z, y), <) /\ ∈((y, x), <))) by Tautology.from(lastStep, initialSegmentUnionForLimitElementsIsComplete of t -> z, wellOrder.definition)

            have(∈((z, y), <) /\ ∈((y, x), <) |- ∈(z, relationDomain(uw))) subproof {
              assume(∈((z, y), <), ∈((y, x), <))

              val zLTy = have(∈(z, initialSegment(p, y))) by Tautology.from(initialSegmentElement of (x -> z, y -> y), wellOrder.definition, strictTotalOrder.definition)
              val yLTx = have(∈(y, initialSegment(p, x))) by Tautology.from(initialSegmentElement of (x -> y, y -> x), wellOrder.definition, strictTotalOrder.definition)

              have(thesis) by Tautology.from(zLTy, yLTx, zyInDomUw)
            }

            thenHave(∃(y, ∈((z, y), <) /\ ∈((y, x), <)) |- ∈(z, relationDomain(uw))) by LeftExists
            have(thesis) by Tautology.from(yExists, lastStep)
          }

          have(thesis) by Tautology.from(lastStep, uwRestrictedEq)
        }

        thenHave(∈(z, initialSegment(p, x)) ==> (app(uw, z) === F(orderedRestriction(uw, z, p)))) by Restate
        thenHave(∀(z, ∈(z, initialSegment(p, x)) ==> (app(uw, z) === F(orderedRestriction(uw, z, p))))) by RightForall
        have(fun(uw, x)) by Tautology.from(lastStep, uwFunctionalOver)
        thenHave(∃(g, fun(g, x))) by RightExists
      }

      // if x has a predecessor, then we need to add an element to uw, giving us v as the requisite function
      val successorCase = have(successorElement(p, x) |- ∃(g, fun(g, x))) subproof {
        assume(successorElement(p, x))
        // the right function is v = Uw \cup {(pred x, F Uw)}
        // i.e., Uw with a recursive addition for the predecessor of x
        // which is not included ∈ any initial segment below x (! (pred x < y) for y < x)
        // define pr as the predecessor of x
        val pr = variable
        val prFun = singleton((pr, F(uw)))
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
          //   2. v is recursive, i.e. \∀ z < x. v z = F v |^ z as required

          val uwFunctionalOver = have(functionalOver(uw, initialSegment(p, pr))) subproof {
            val iffDom = have(functionalOver(uw, initialSegment(p, pr)) <=> (relationDomain(uw) === initialSegment(p, pr))) by Tautology.from(
              functionalOver.definition of (f -> uw, x -> initialSegment(p, pr)),
              uwfunctional
            )

            have(relationDomain(uw) === initialSegment(p, pr)) subproof {
              val fwd = have(∈(t, relationDomain(uw)) |- ∈(t, initialSegment(p, pr))) subproof {
                assume(∈(t, relationDomain(uw)))

                have(∀(t, ∈(t, relationDomain(uw)) <=> ∃(g, ∈(g, w) /\ ∈(t, relationDomain(g))))) by Tautology.from(uwfunctional, domainOfFunctionalUnion of z -> w)
                thenHave(∈(t, relationDomain(uw)) <=> ∃(g, ∈(g, w) /\ ∈(t, relationDomain(g)))) by InstantiateForall(t)
                val gExists = thenHave(∃(g, ∈(g, w) /\ ∈(t, relationDomain(g)))) by Tautology

                have(∈(g, w) /\ ∈(t, relationDomain(g)) |- ∈(t, initialSegment(p, pr))) subproof {
                  assume(∈(g, w))
                  assume(∈(t, relationDomain(g)))

                  have(∈(g, w) <=> ∃(y, ∈(y, initialSegment(p, x)) /\ fun(g, y))) by InstantiateForall
                  val yExists = thenHave(∃(y, ∈(y, initialSegment(p, x)) /\ fun(g, y))) by Tautology

                  have(∈(y, initialSegment(p, x)) /\ fun(g, y) |- ∈(t, initialSegment(p, pr))) subproof {
                    assume(∈(y, initialSegment(p, x)), fun(g, y))
                    // t < y
                    val domEQ = have(relationDomain(g) === initialSegment(p, y)) by Tautology.from(functionalOver.definition of (f -> g, x -> initialSegment(p, y)))
                    have(∈(t, relationDomain(g))) by Restate
                    val tLTy = thenHave(∈(t, initialSegment(p, y))) by Substitution.ApplyRules(domEQ)

                    // y <= pr
                    val cases = have((y === pr) \/ ∈(y, initialSegment(p, pr))) by Tautology.from(initialSegmentPredecessorSplit of (y -> pr, z -> y), wellOrder.definition)

                    val eqCase = have((y === pr) |- ∈(t, initialSegment(p, pr))) by Substitution.ApplyRules(y === pr)(tLTy)
                    val initCase = have(∈(y, initialSegment(p, pr)) |- ∈(t, initialSegment(p, pr))) by Tautology.from(tLTy, initialSegmentTransitivity of (x -> t, y -> y, z -> pr), wellOrder.definition, strictTotalOrder.definition)

                    have(thesis) by Tautology.from(cases, eqCase, initCase)
                  }

                  thenHave(∃(y, ∈(y, initialSegment(p, x)) /\ fun(g, y)) |- ∈(t, initialSegment(p, pr))) by LeftExists
                  have(thesis) by Tautology.from(lastStep, yExists)
                }

                thenHave(∃(g, ∈(g, w) /\ ∈(t, relationDomain(g))) |- ∈(t, initialSegment(p, pr))) by LeftExists
                have(thesis) by Cut(gExists, lastStep)
              }

              val bwd = have(∈(t, initialSegment(p, pr)) |- ∈(t, relationDomain(uw))) subproof {
                assume(∈(t, initialSegment(p, pr)))

                have(∈((pr, x), <)) by Tautology.from(predecessor.definition of (x -> pr, y -> x))
                val prLTx = have(∈(pr, initialSegment(p, x))) by Tautology.from(lastStep, wellOrder.definition, strictTotalOrder.definition, initialSegmentElement of (y -> x, x -> pr))

                have(∀(y, ∈(y, initialSegment(p, x)) ==> ∃!(g, fun(g, y)))) by Restate
                thenHave(∈(pr, initialSegment(p, x)) ==> ∃!(g, fun(g, pr))) by InstantiateForall(pr)
                val gExists = have(∃(g, fun(g, pr))) by Tautology.from(lastStep, prLTx, existsOneImpliesExists of P -> lambda(g, fun(g, pr)))

                have(fun(g, pr) |- ∈(g, w) /\ ∈(t, relationDomain(g))) subproof {
                  assume(fun(g, pr))

                  have(∈(pr, initialSegment(p, x)) /\ fun(g, pr)) by Tautology.from(prLTx)
                  val exPR = thenHave(∃(pr, ∈(pr, initialSegment(p, x)) /\ fun(g, pr))) by RightExists

                  have(∈(g, w) <=> ∃(y, ∈(y, initialSegment(p, x)) /\ fun(g, y))) by InstantiateForall
                  val gW = have(∈(g, w)) by Tautology.from(lastStep, exPR)

                  have(functionalOver(g, initialSegment(p, pr))) by Tautology
                  val domEQ = have(relationDomain(g) === initialSegment(p, pr)) by Tautology.from(lastStep, functionalOver.definition of (f -> g, x -> initialSegment(p, pr)))

                  have(∈(t, initialSegment(p, pr))) by Restate
                  thenHave(∈(t, relationDomain(g))) by Substitution.ApplyRules(domEQ)
                  have(thesis) by Tautology.from(lastStep, gW)
                }

                thenHave(fun(g, pr) |- ∃(g, ∈(g, w) /\ ∈(t, relationDomain(g)))) by RightExists
                thenHave(∃(g, fun(g, pr)) |- ∃(g, ∈(g, w) /\ ∈(t, relationDomain(g)))) by LeftExists
                val gInW = have(∃(g, ∈(g, w) /\ ∈(t, relationDomain(g)))) by Cut(gExists, lastStep)

                have(∀(t, ∈(t, relationDomain(uw)) <=> ∃(g, ∈(g, w) /\ ∈(t, relationDomain(g))))) by Tautology.from(uwfunctional, domainOfFunctionalUnion of z -> w)
                thenHave(∈(t, relationDomain(uw)) <=> ∃(g, ∈(g, w) /\ ∈(t, relationDomain(g)))) by InstantiateForall(t)
                have(thesis) by Tautology.from(lastStep, gInW)
              }

              have(∈(t, relationDomain(uw)) <=> ∈(t, initialSegment(p, pr))) by Tautology.from(fwd, bwd)
              thenHave(∀(t, ∈(t, relationDomain(uw)) <=> ∈(t, initialSegment(p, pr)))) by RightForall
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
            val domainsDisjoint = have(setIntersection(initialSegment(p, pr), singleton(pr)) === emptySet) subproof {
              val singletonMembership = have(∈(t, singleton(pr)) <=> (t === pr)) by Weakening(singletonHasNoExtraElements of (y -> t, x -> pr))

              val initMembership = have(∈(t, initialSegment(p, pr)) <=> ∈((t, pr), <)) by Tautology.from(initialSegmentElement of (x -> t, y -> pr), wellOrder.definition, strictTotalOrder.definition)

              have(∈(t, singleton(pr)) /\ ∈(t, initialSegment(p, pr)) |- ()) subproof {
                assume(∈(t, singleton(pr)))
                assume(∈(t, initialSegment(p, pr)))

                val tEQpr = have(t === pr) by Tautology.from(singletonMembership)
                val tLTpr = have(∈((t, pr), <)) by Tautology.from(initMembership)
                val prprp2 = thenHave(∈((pr, pr), <)) by Substitution.ApplyRules(tEQpr)

                // but the order is anti reflexive
                have(∀(pr, ∈(pr, A) ==> !∈((pr, pr), <))) by Tautology.from(wellOrder.definition, strictTotalOrder.definition, partialOrder.definition, antiReflexive.definition of (r -> <, x -> A))
                thenHave(∈(pr, A) ==> !∈((pr, pr), <)) by InstantiateForall(pr)
                have(!∈((pr, pr), <)) by Tautology.from(lastStep, predecessor.definition of (x -> pr, y -> x))

                have(thesis) by Tautology.from(lastStep, prprp2)
              }

              val inEmpty = thenHave((∈(t, singleton(pr)) /\ ∈(t, initialSegment(p, pr))) ==> ∈(t, emptySet)) by Weakening

              have(∈(t, setIntersection(initialSegment(p, pr), singleton(pr))) <=> (∈(t, singleton(pr)) /\ ∈(t, initialSegment(p, pr)))) by Tautology.from(
                setIntersectionMembership of (x -> initialSegment(p, pr), y -> singleton(pr))
              )
              have(∈(t, setIntersection(initialSegment(p, pr), singleton(pr))) ==> ∈(t, emptySet)) by Substitution.ApplyRules(lastStep)(inEmpty)
              thenHave(∀(t, ∈(t, setIntersection(initialSegment(p, pr), singleton(pr))) ==> ∈(t, emptySet))) by RightForall
              have(⊆(setIntersection(initialSegment(p, pr), singleton(pr)), emptySet)) by Tautology.from(
                lastStep,
                subsetAxiom of (x -> setIntersection(initialSegment(p, pr), singleton(pr)), y -> emptySet)
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
                have(∈(t, initialSegment(p, x)) <=> ((t === pr) \/ ∈(t, initialSegment(p, pr)))) by Tautology.from(initialSegmentPredecessorSplit of (z -> t, y -> pr), wellOrder.definition)

              val singletonMembership = have(∈(t, singleton(pr)) <=> (t === pr)) by Tautology.from(singletonHasNoExtraElements of (y -> t, x -> pr))

              val initMembership = have(∈(t, initialSegment(p, x)) <=> (∈(t, singleton(pr)) \/ ∈(t, initialSegment(p, pr)))) by Substitution.ApplyRules(singletonMembership)(initBreakdown)

              have(∈(t, setUnion(initialSegment(p, pr), singleton(pr))) <=> (∈(t, singleton(pr)) \/ ∈(t, initialSegment(p, pr)))) by Tautology.from(
                setUnionMembership of (z -> t, x -> initialSegment(p, pr), y -> singleton(pr))
              )
              have(∈(t, initialSegment(p, x)) <=> ∈(t, setUnion(initialSegment(p, pr), singleton(pr)))) by Substitution.ApplyRules(lastStep)(initMembership)
              thenHave(∀(t, ∈(t, initialSegment(p, x)) <=> ∈(t, setUnion(initialSegment(p, pr), singleton(pr))))) by RightForall

              have(thesis) by Tautology.from(lastStep, extensionalityAxiom of (x -> initialSegment(p, x), y -> setUnion(initialSegment(p, pr), singleton(pr))))
            }

            have(thesis) by Substitution.ApplyRules(unionEQ)(vFunctionalOverUnion)
          }

          // 2. v is recursive
          val vRecursive = have(∀(z, ∈(z, initialSegment(p, x)) ==> (app(v, z) === F(orderedRestriction(v, z, p))))) subproof {
            have(∈(z, initialSegment(p, x)) |- (app(v, z) === F(orderedRestriction(v, z, p)))) subproof {
              assume(∈(z, initialSegment(p, x)))

              // z is ∈ dom v
              val zInDom = have(∈(z, relationDomain(v))) subproof {
                val domEQ = have(relationDomain(v) === initialSegment(p, x)) by Tautology.from(functionalOver.definition of (f -> v, x -> initialSegment(p, x)), vFunctionalOver)
                have(∈(z, initialSegment(p, x))) by Restate
                thenHave(thesis) by Substitution.ApplyRules(domEQ)
              }

              // app v z is well defined
              val vAppDef = have((a === app(v, z)) <=> ∈((z, a), v)) subproof {
                have(functional(v)) by Tautology.from(vFunctionalOver, functionalOver.definition of (f -> v, x -> initialSegment(p, x)))
                have(thesis) by Tautology.from(lastStep, zInDom, pairInFunctionIsApp of (f -> v, a -> z, b -> a))
              }

              // z is either the predecessor or below it
              val zSplit = have(((z === pr) \/ ∈(z, initialSegment(p, pr)))) by Tautology.from(wellOrder.definition, initialSegmentPredecessorSplit of (y -> pr))

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
                    wellOrder.definition, strictTotalOrder.definition,
                    wellOrder.definition
                  )
                  have(thesis) by Substitution.ApplyRules(lastStep)(initIntersection)
                }

                // and they agree on their domain
                have(∈(b, initialSegment(p, pr)) |- (app(uw, b) === app(vpr, b))) subproof {
                  assume(∈(b, initialSegment(p, pr)))

                  val appDefw = have((a === app(uw, b)) <=> ∈((b, a), uw)) by Tautology.from(functionalOverApplication of (f -> uw, x -> initialSegment(p, pr), b -> a, a -> b), domUW)
                  val appDefv = have((a === app(vpr, b)) <=> ∈((b, a), vpr)) by Tautology.from(functionalOverApplication of (f -> vpr, x -> initialSegment(p, pr), b -> a, a -> b), domRV)

                  val fwd = have(∈((b, a), uw) |- ∈((b, a), vpr)) subproof {
                    assume(∈((b, a), uw))

                    have(∈((b, a), v)) by Tautology.from(setUnionMembership of (z -> (b, a), x -> uw, y -> prFun))
                    have(∈((b, a), restrictedFunction(v, initialSegment(p, pr)))) by Tautology.from(
                      lastStep,
                      restrictedFunctionPairMembership of (f -> v, x -> initialSegment(p, pr), t -> b, a -> a)
                    )
                    thenHave(thesis) by Substitution.ApplyRules(ordBreakdown of (a -> v, b -> pr))
                  }

                  val bwd = have(∈((b, a), vpr) |- ∈((b, a), uw)) subproof {
                    assume(∈((b, a), vpr))
                    have(∈((b, a), vpr)) by Restate
                    thenHave(∈((b, a), restrictedFunction(v, initialSegment(p, pr)))) by Substitution.ApplyRules(ordBreakdown of (a -> v, b -> pr))
                    have(∈((b, a), v)) by Tautology.from(lastStep, restrictedFunctionPairMembership of (f -> v, x -> initialSegment(p, pr), t -> b, a -> a))
                    val cases = have(∈((b, a), uw) \/ ∈((b, a), prFun)) by Tautology.from(lastStep, setUnionMembership of (z -> (b, a), x -> uw, y -> prFun))

                    have(!∈((b, a), prFun)) subproof {
                      // towards a contradiction, assume otherwise
                      assume(∈((b, a), prFun))

                      have((b, a) === (pr, F(uw))) by Tautology.from(singletonHasNoExtraElements of (y -> (b, a), x -> (pr, F(uw))))
                      val bEQpr = have(b === pr) by Tautology.from(lastStep, pairExtensionality of (a -> b, b -> a, c -> pr, d -> F(uw)))

                      have(∈(b, initialSegment(p, pr))) by Restate
                      thenHave(∈(pr, initialSegment(p, pr))) by Substitution.ApplyRules(bEQpr)
                      have(bot) by Tautology.from(lastStep, initialSegmentIrreflexivity of (x -> pr), wellOrder.definition, strictTotalOrder.definition)
                    }

                    have(thesis) by Tautology.from(lastStep, cases)
                  }

                  have(∈((b, a), uw) <=> ∈((b, a), vpr)) by Tautology.from(fwd, bwd)
                  have((a === app(uw, b)) <=> (a === app(vpr, b))) by Tautology.from(appDefw, appDefv, lastStep)
                  have(thesis) by Restate.from(lastStep of a -> app(uw, b))
                }

                thenHave(∈(b, initialSegment(p, pr)) ==> (app(uw, b) === app(vpr, b))) by Restate
                thenHave(∀(b, ∈(b, initialSegment(p, pr)) ==> (app(uw, b) === app(vpr, b)))) by RightForall

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
                    val pairInV = have(∈((pr, F(uw)), v)) by Tautology.from(
                      setUnionMembership of (z -> (pr, F(uw)), x -> uw, y -> prFun),
                      singletonHasNoExtraElements of (x -> (pr, F(uw)), y -> (pr, F(uw)))
                    )
                    have(∈(pr, initialSegment(p, x))) by Tautology.from(predecessorInInitialSegment of y -> pr, wellOrder.definition)
                    have(thesis) by Tautology.from(vAppDef of (a -> F(uw), z -> pr), lastStep, pairInV)
                  }

                  have(thesis) by Tautology.from(equalityTransitivity of (x -> app(v, pr), y -> F(uw), z -> F(orderedRestriction(v, pr, p))), fuwEq, appEq)
                }

                thenHave(thesis) by Substitution.ApplyRules(z === pr)
              }

              // the property holds for elements < pr
              val wCase = have(∈(z, initialSegment(p, pr)) |- (app(v, z) === F(orderedRestriction(v, z, p)))) subproof {
                assume(∈(z, initialSegment(p, pr)))

                // uw is functional over <pr

                // ordered restriction of v to z is the same as uw to z
                val restrictionVW = have(orderedRestriction(v, z, p) === orderedRestriction(uw, z, p)) subproof {
                  have(orderedRestriction(uw, z, p) === orderedRestriction(uw, z, p)) by Restate
                  val doubleRestriction = thenHave(orderedRestriction(uw, z, p) === orderedRestriction(orderedRestriction(v, pr, p), z, p)) by Substitution.ApplyRules(uwEq)

                  have(orderedRestriction(orderedRestriction(v, pr, p), z, p) === orderedRestriction(v, z, p)) subproof {
                    // reduce to restricted functions

                    val intersectionEQ = have(setIntersection(initialSegment(p, pr), initialSegment(p, z)) === initialSegment(p, z)) subproof {
                      have(setIntersection(initialSegment(p, z), initialSegment(p, pr)) === initialSegment(p, z)) by Tautology.from(initialSegmentIntersection of (y -> z, x -> pr), wellOrder.definition, strictTotalOrder.definition)

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
                  // z ∈ dom uw
                  have(∈(z, relationDomain(uw))) subproof {
                    // z < pr < x
                    // \∃ g \∈ w. fun g pr
                    // z ∈ dom g
                    // so z ∈ dom uw
                    val zLTpr = have(∈(z, initialSegment(p, pr))) by Restate
                    val prLTx = have(∈(pr, initialSegment(p, x))) by Tautology.from(predecessorInInitialSegment of y -> pr, wellOrder.definition)

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

            thenHave(∈(z, initialSegment(p, x)) ==> (app(v, z) === F(orderedRestriction(v, z, p)))) by Restate
            thenHave(thesis) by RightForall
          }

          have(fun(v, x)) by Tautology.from(vRecursive, vFunctionalOver)
        }

        val prExists = have(∃(pr, predecessor(p, pr, x))) by Tautology.from(successorElement.definition)

        have(predecessor(p, pr, x) |- ∃(g, fun(g, x))) by RightExists(vFun)
        thenHave(∃(pr, predecessor(p, pr, x)) |- ∃(g, fun(g, x))) by LeftExists
        have(thesis) by Cut(prExists, lastStep)
      }

      have(thesis) by Tautology.from(limSuccCases, limitCase, successorCase)
    }

    val funExists = thenHave(∃(w, wDef) |- ∃(g, fun(g, x))) by LeftExists

    have(∃(w, wDef)) subproof {
      // restating the definition of w
      // val wDef = ∀(t, ∈(t, w) <=> ∃(y, ∈(y, initialSegment(p, x)) /\ fun(t, y)))
      // ∀ t. t \∈ w <=> \∃ y < x. fun(t, y)

      // we know that there ∃ a *unique* g for each y ∈ the initial segment
      // so, there is a functional map from the initial segment that produces these values
      // by replacement, we can take the image of the initial segment
      // restating replacement:

      have(∀(y, ∈(y, initialSegment(p, x)) ==> ∃!(g, fun(g, y)))) by Restate
      have(∃(w, ∀(t, ∈(t, w) <=> ∃(y, ∈(y, initialSegment(p, x)) /\ fun(t, y))))) by Tautology.from(
        lastStep,
        strictReplacementSchema of (A -> initialSegment(p, x), R -> lambda((y, g), fun(g, y)))
      )
    }

    have(thesis) by Tautology.from(lastStep, funExists)
  }

  /**
   * Theorem --- Well-Ordered Recursion
   *
   * Given any element `t` of a well order `p`, and a class function `F`, there
   * ∃ a unique function `g` with `<t`, the initial segment of `t`, as its
   * domain, defined recursively as
   *
   * `\forall a < t. g(a) = F(g |^ < a)`
   *
   * where `g |^ <a` is `g` with its domain restricted to `<a`, the initial
   * segment of `a`.
   */
  val wellOrderedRecursion = Lemma(
    wellOrder(A)(<) |- ∀(t ∈ A, ∃!(g, (functionalOver(g, initialSegment(p, t)) /\ ∀(a ∈ initialSegment(p, t), app(g, a) === F(orderedRestriction(g, a, p))))))
  ) {
    assume(wellOrder(A)(<))

    // the existence of g propagates up from initial segments
    val initPropagate = have(x ∈ A ==> (∀(y ∈ initialSegment(p, x), prop(y)) ==> prop(x))) subproof {

      assume(
        ∈(x, A),
        ∀(y, ∈(y, initialSegment(p, x)) ==> prop(y))
      )

      // see [[uniqueRecursiveFunction]] and [[recursiveFunctionExistencePropagates]]

      have(thesis) by Tautology.from(recursiveFunctionExistencePropagates, uniqueRecursiveFunction of t -> x)
    }

    // so we induct on the well-ordering
    thenHave(∀(x, ∈(x, A) ==> (∀(y, ∈(y, initialSegment(p, x)) ==> prop(y)) ==> prop(x)))) by RightForall
    have(thesis) by Tautology.from(lastStep, wellOrderedInduction of Q -> lambda(x, prop(x)))
  }
  show

  /**
   * Theorem --- Transfinite Recursion
   *
   * Given any ordinal `a` and a class function `F`, there ∃ a unique
   * function `g` with `a` as its domain, defined recursively as
   *
   * `\forall b < a. g(b) = F(g |^ b)`
   *
   * where `g |^ b` is `g` with its domain restricted to `b`.
   */
  val transfiniteRecursion = Theorem(
    ordinal(a) |- ∃!(g, functionalOver(g, a) /\ ∀(b ∈ a, app(g, b) === F(restrictedFunction(g, b))))
  ) {
    sorry
  }
   */

}

