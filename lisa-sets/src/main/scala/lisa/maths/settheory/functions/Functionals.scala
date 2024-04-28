package lisa.maths.settheory.functions
import lisa.automation.kernel.CommonTactics.Definition
import lisa.automation.settheory.SetTheoryTactics.*
import lisa.maths.settheory.SetTheory.*
import lisa.maths.Quantifiers.*

/**
 * Functional sets
 *
 * Defines functionals, their application, and spaces of functions.
 */
object Functionals extends lisa.Main {
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
  private val f = variable
  private val g = variable

  private val P = predicate[1]
  private val Q = predicate[1]

  /**
   * Functional --- A binary [[relation]] is functional if it maps every element in its domain
   * to a unique element (in its range).
   *
   *     `functional(f) ⇔ relation(f) ∧ ∀ x. (∃ y. (x, y) ∈ f) ⟹ (∃! y. (x, y) ∈ f)`
   *
   * We may alternatively denote `(z, y) ∈ f` as `y = f(z)`.
   *
   * @param f relation (set)
   */
  val functional = DEF(f) --> relation(f) /\ ∀(x, ∃(y, in(pair(x, y), f)) ==> ∃!(y, in(pair(x, y), f)))

  /**
   * Functional Over a Set --- A binary [[relation]] is functional over a set `x` if it is
   * [[functional]] and has`x` as its domain ([[relationDomain]]).
   *
   * @param f relation (set)
   * @param x set
   */
  val functionalOver = DEF(f, x) --> functional(f) /\ (relationDomain(f) === x)

  /**
   * Lemma --- If `f` is a function, then `t ∈ f` implies `t = (x, y)` such that `x ∈ relationDomain(f)`.
   */
  val functionalMembership = Lemma(
    functional(f) |- ∀(t, in(t, f) ==> ∃(x, ∃(y, in(x, relationDomain(f)) /\ (t === pair(x, y)))))
  ) {
    assume(functional(f))

    have((functional(f), in(t, f)) |- ∃(x, ∃(y, in(x, relationDomain(f)) /\ (t === pair(x, y))))) subproof {
      val isRelation = have(relation(f)) by Tautology.from(functional.definition)

      // Use the definitions
      have(relationBetween(f, relationDomain(f), relationRange(f)) |- ∀(x, in(x, f) ==> in(x, cartesianProduct(relationDomain(f), relationRange(f))))) by Tautology.from(
        relationBetween.definition of (r -> f, a -> relationDomain(f), b -> relationRange(f)),
        subset.definition of (x -> f, y -> cartesianProduct(relationDomain(f), relationRange(f)))
      )
      thenHave(relationBetween(f, relationDomain(f), relationRange(f)) |- in(t, f) ==> in(t, cartesianProduct(relationDomain(f), relationRange(f)))) by InstantiateForall(t)
      thenHave((relationBetween(f, relationDomain(f), relationRange(f)), in(t, f)) |- in(t, cartesianProduct(relationDomain(f), relationRange(f)))) by Restate

      val almostThere =
        have((relationBetween(f, relationDomain(f), relationRange(f)), in(t, f)) |- ∃(x, ∃(y, (t === pair(x, y)) /\ in(x, relationDomain(f)) /\ in(y, relationRange(f))))) by Tautology.from(
          lastStep,
          elemOfCartesianProduct of (x -> relationDomain(f), y -> relationRange(f))
        )

      // Remove the extraneous term in the conjunction
      have((t === pair(x, y)) /\ in(x, relationDomain(f)) /\ in(y, relationRange(f)) |- in(x, relationDomain(f)) /\ (t === pair(x, y))) by Tautology
      thenHave((t === pair(x, y)) /\ in(x, relationDomain(f)) /\ in(y, relationRange(f)) |- ∃(y, in(x, relationDomain(f)) /\ (t === pair(x, y)))) by RightExists
      thenHave((t === pair(x, y)) /\ in(x, relationDomain(f)) /\ in(y, relationRange(f)) |- ∃(x, ∃(y, in(x, relationDomain(f)) /\ (t === pair(x, y))))) by RightExists
      thenHave(∃(y, (t === pair(x, y)) /\ in(x, relationDomain(f)) /\ in(y, relationRange(f))) |- ∃(x, ∃(y, in(x, relationDomain(f)) /\ (t === pair(x, y))))) by LeftExists
      thenHave(∃(x, ∃(y, (t === pair(x, y)) /\ in(x, relationDomain(f)) /\ in(y, relationRange(f)))) |- ∃(x, ∃(y, in(x, relationDomain(f)) /\ (t === pair(x, y))))) by LeftExists

      have((relationBetween(f, relationDomain(f), relationRange(f)), in(t, f)) |- ∃(x, ∃(y, in(x, relationDomain(f)) /\ (t === pair(x, y))))) by Cut(almostThere, lastStep)
      have((relation(f), in(t, f)) |- ∃(x, ∃(y, in(x, relationDomain(f)) /\ (t === pair(x, y))))) by Cut(relationImpliesRelationBetweenDomainAndRange of (r -> f), lastStep)
      have(in(t, f) |- ∃(x, ∃(y, in(x, relationDomain(f)) /\ (t === pair(x, y))))) by Cut(isRelation, lastStep)
    }
    thenHave(in(t, f) ==> ∃(x, ∃(y, in(x, relationDomain(f)) /\ (t === pair(x, y))))) by Restate
    thenHave(thesis) by RightForall
  }

  /**
   * Theorem --- a function cannot have two pairs representing different values
   * for a given element.
   *
   *    `functional(f) /\ (x, y) \in f /\ (x, z) \in f /\ !(y = z) |- \bot`
   */
  val violatingPairInFunction = Theorem(
    functional(f) /\ in(pair(x, y), f) /\ in(pair(x, z), f) /\ !(y === z) |- ()
  ) {
    assume(functional(f), in(pair(x, y), f), in(pair(x, z), f), !(y === z))

    have(forall(x, exists(y, in(pair(x, y), f)) ==> existsOne(y, in(pair(x, y), f)))) by Tautology.from(functional.definition)
    val exExOne = thenHave(exists(y, in(pair(x, y), f)) ==> existsOne(y, in(pair(x, y), f))) by InstantiateForall(x)

    have(in(pair(x, y), f) /\ in(pair(x, z), f) /\ !(y === z)) by Restate
    thenHave(exists(z, in(pair(x, y), f) /\ in(pair(x, z), f) /\ !(y === z))) by RightExists
    thenHave(exists(y, exists(z, in(pair(x, y), f) /\ in(pair(x, z), f) /\ !(y === z)))) by RightExists

    have(thesis) by Tautology.from(lastStep, exExOne, atleastTwoExist of (P -> lambda(y, in(pair(x, y), f))))
  }

  /**
   * Theorem --- a set containing a single pair is a function.
   *
   * Given `s = {(x, y)}`,
   *
   *    `functional(s) /\ dom(s) = {x} /\ ran(s) = {y}`
   */
  val pairSingletonIsFunctional = Theorem(
    {
      val s = singleton(pair(x, y))
      functional(s) /\ (relationDomain(s) === singleton(x)) /\ (relationRange(s) === singleton(y))
    }
  ) {
    val s = singleton(pair(x, y))

    val elemOfS = have(in(z, s) <=> (z === pair(x, y))) by Restate.from(singletonHasNoExtraElements of (y -> z, x -> pair(x, y)))

    // (x, y) in {x} * {y}
    val xyInCart = have(in(pair(x, y), cartesianProduct(singleton(x), singleton(y)))) subproof {
      have((pair(x, y) === pair(x, y)) /\ in(x, singleton(x)) /\ in(y, singleton(y))) by Tautology.from(singletonHasNoExtraElements of (y -> x), singletonHasNoExtraElements of (x -> y))
      thenHave(exists(b, (pair(x, y) === pair(x, b)) /\ in(x, singleton(x)) /\ in(b, singleton(y)))) by RightExists
      thenHave(exists(a, exists(b, (pair(x, y) === pair(a, b)) /\ in(a, singleton(x)) /\ in(b, singleton(y))))) by RightExists
      have(thesis) by Tautology.from(lastStep, elemOfCartesianProduct of (t -> pair(x, y), x -> singleton(x), y -> singleton(y)))
    }

    val relS = have(relation(s)) subproof {
      have((z === pair(x, y)) |- in(z, cartesianProduct(singleton(x), singleton(y)))) by Substitution.ApplyRules(z === pair(x, y))(xyInCart)
      have(in(z, s) ==> in(z, cartesianProduct(singleton(x), singleton(y)))) by Tautology.from(lastStep, elemOfS)
      thenHave(forall(z, in(z, s) ==> in(z, cartesianProduct(singleton(x), singleton(y))))) by RightForall
      have(relationBetween(s, singleton(x), singleton(y))) by Tautology.from(
        lastStep,
        subsetAxiom of (x -> s, y -> cartesianProduct(singleton(x), singleton(y))),
        relationBetween.definition of (r -> s, a -> singleton(x), b -> singleton(y))
      )
      thenHave(exists(b, relationBetween(s, singleton(x), b))) by RightExists
      thenHave(exists(a, exists(b, relationBetween(s, a, b)))) by RightExists
      have(thesis) by Tautology.from(lastStep, relation.definition of r -> s)
    }

    val uniq = have(forall(a, exists(b, in(pair(a, b), s)) ==> existsOne(b, in(pair(a, b), s)))) subproof {
      have((pair(a, z) === pair(x, y)) <=> in(pair(a, z), s)) by Restate.from(elemOfS of z -> pair(a, z))
      val eq = thenHave(((a === x) /\ (z === y)) <=> in(pair(a, z), s)) by Substitution.ApplyRules(pairExtensionality)
      thenHave((a === x) |- (z === y) <=> in(pair(a, z), s)) by Tautology
      thenHave((a === x) |- forall(z, (z === y) <=> in(pair(a, z), s))) by RightForall
      thenHave((a === x) |- exists(b, forall(z, (z === b) <=> in(pair(a, z), s)))) by RightExists
      thenHave((a === x) |- existsOne(b, in(pair(a, b), s))) by RightExistsOne
      val pos = thenHave((a === x) |- exists(b, in(pair(a, b), s)) ==> existsOne(b, in(pair(a, b), s))) by Weakening

      val ax = have(in(pair(a, z), s) |- (a === x)) by Weakening(eq)
      thenHave(!(a === x) |- !in(pair(a, z), s)) by Restate
      thenHave(!(a === x) |- forall(z, !in(pair(a, z), s))) by RightForall
      thenHave(!(a === x) |- !exists(z, in(pair(a, z), s))) by Restate
      val neg = thenHave(!(a === x) |- exists(b, in(pair(a, b), s)) ==> existsOne(b, in(pair(a, b), s))) by Weakening

      have(exists(b, in(pair(a, b), s)) ==> existsOne(b, in(pair(a, b), s))) by Tautology.from(pos, neg)
      thenHave(thesis) by RightForall
    }

    val dom = have(relationDomain(s) === singleton(x)) subproof {
      have(forall(t, in(t, relationDomain(s)) <=> exists(a, in(pair(t, a), s)))) by InstantiateForall(relationDomain(s))(relationDomain.definition of r -> s)
      val inDom = thenHave(in(t, relationDomain(s)) <=> exists(a, in(pair(t, a), s))) by InstantiateForall(t)

      have(in(pair(t, a), s) <=> ((t === x) /\ (a === y))) by Substitution.ApplyRules(pairExtensionality)(elemOfS of z -> pair(t, a))
      thenHave(forall(a, in(pair(t, a), s) <=> ((t === x) /\ (a === y)))) by RightForall
      val exToEq = have(exists(a, in(pair(t, a), s)) <=> exists(a, ((t === x) /\ (a === y)))) by Cut(
        lastStep,
        existentialEquivalenceDistribution of (P -> lambda(a, in(pair(t, a), s)), Q -> lambda(a, ((t === x) /\ (a === y))))
      )

      val exRedundant = have(exists(a, ((t === x) /\ (a === y))) <=> (t === x)) subproof {
        have((t === x) /\ (a === y) |- (t === x)) by Restate
        val fwd = thenHave(exists(a, (t === x) /\ (a === y)) |- (t === x)) by LeftExists

        have((t === x) |- (t === x) /\ (y === y)) by Restate
        val bwd = thenHave((t === x) |- exists(a, (t === x) /\ (a === y))) by RightExists

        have(thesis) by Tautology.from(fwd, bwd)
      }

      have((t === x) <=> in(t, singleton(x))) by Restate.from(singletonHasNoExtraElements of y -> t)
      have(in(t, relationDomain(s)) <=> in(t, singleton(x))) by Tautology.from(lastStep, exRedundant, exToEq, inDom)
      thenHave(forall(t, in(t, relationDomain(s)) <=> in(t, singleton(x)))) by RightForall
      have(thesis) by Tautology.from(lastStep, extensionalityAxiom of (x -> relationDomain(s), y -> singleton(x)))
    }

    val ran = have(relationRange(s) === singleton(y)) subproof {
      have(forall(t, in(t, relationRange(s)) <=> exists(a, in(pair(a, t), s)))) by InstantiateForall(relationRange(s))(relationRange.definition of r -> s)
      val inDom = thenHave(in(t, relationRange(s)) <=> exists(a, in(pair(a, t), s))) by InstantiateForall(t)

      have(in(pair(a, t), s) <=> ((a === x) /\ (t === y))) by Substitution.ApplyRules(pairExtensionality)(elemOfS of z -> pair(a, t))
      thenHave(forall(a, in(pair(a, t), s) <=> ((a === x) /\ (t === y)))) by RightForall
      val exToEq = have(exists(a, in(pair(a, t), s)) <=> exists(a, ((a === x) /\ (t === y)))) by Cut(
        lastStep,
        existentialEquivalenceDistribution of (P -> lambda(a, in(pair(a, t), s)), Q -> lambda(a, ((a === x) /\ (t === y))))
      )

      val exRedundant = have(exists(a, ((a === x) /\ (t === y))) <=> (t === y)) subproof {
        have((a === x) /\ (t === y) |- (t === y)) by Restate
        val fwd = thenHave(exists(a, (a === x) /\ (t === y)) |- (t === y)) by LeftExists

        have((t === y) |- (x === x) /\ (t === y)) by Restate
        val bwd = thenHave((t === y) |- exists(a, (a === x) /\ (t === y))) by RightExists

        have(thesis) by Tautology.from(fwd, bwd)
      }

      have((t === y) <=> in(t, singleton(y))) by Restate.from(singletonHasNoExtraElements of (y -> t, x -> y))
      have(in(t, relationRange(s)) <=> in(t, singleton(y))) by Tautology.from(lastStep, exRedundant, exToEq, inDom)
      thenHave(forall(t, in(t, relationRange(s)) <=> in(t, singleton(y)))) by RightForall
      have(thesis) by Tautology.from(lastStep, extensionalityAxiom of (x -> relationRange(s), y -> singleton(y)))
    }

    have(functional(s)) by Tautology.from(relS, uniq, functional.definition of f -> s)

    have(thesis) by Tautology.from(ran, dom, lastStep)

  }

  val setOfFunctionsUniqueness = Theorem(
    ∃!(z, ∀(t, in(t, z) <=> (in(t, powerSet(cartesianProduct(x, y))) /\ functionalOver(t, x))))
  ) {
    have(thesis) by UniqueComprehension(powerSet(cartesianProduct(x, y)), lambda(t, functionalOver(t, x)))
  }

  /**
   * Set of functions --- All functions from `x` to `y`, denoted `x → y` or
   * `→(x, y)`.
   *
   * Since functions from `x` to `y` contain pairs of the form `(a, b) | a ∈
   * x, b ∈ y`, it is a filtering on the power set of their product, i.e. `x
   * → y ⊆ PP(x * y)`.
   */
  val setOfFunctions = DEF(x, y) --> The(z, ∀(t, in(t, z) <=> (in(t, powerSet(cartesianProduct(x, y))) /\ functionalOver(t, x))))(setOfFunctionsUniqueness)

  /**
   * Function From (x to y) --- denoted  `f ∈ x → y` or `f: x → y`.
   */
  val functionFrom = DEF(f, x, y) --> in(f, setOfFunctions(x, y))

  /**
   * Theorem --- A function between two sets is [[functional]]
   */
  val functionFromImpliesFunctional = Theorem(
    functionFrom(f, x, y) |- functional(f)
  ) {
    have(∀(t, in(t, setOfFunctions(x, y)) <=> (in(t, powerSet(cartesianProduct(x, y))) /\ functionalOver(t, x)))) by InstantiateForall(setOfFunctions(x, y))(setOfFunctions.definition)
    val funSetDef = thenHave(in(f, setOfFunctions(x, y)) <=> (in(f, powerSet(cartesianProduct(x, y))) /\ functionalOver(f, x))) by InstantiateForall(f)

    val funOver = have(functionFrom(f, x, y) |- functional(f)) by Tautology.from(funSetDef, functionFrom.definition, functionalOver.definition)
  }

  val functionApplicationUniqueness = Theorem(
    ∃!(z, ((functional(f) /\ in(x, relationDomain(f))) ==> in(pair(x, z), f)) /\ ((!functional(f) \/ !in(x, relationDomain(f))) ==> (z === ∅)))
  ) {
    val prem = functional(f) /\ in(x, relationDomain(f))

    // we prove thesis by two cases, first by assuming prem, and then by assuming !prem

    // positive direction
    have(functional(f) |- ∀(x, ∃(y, in(pair(x, y), f)) ==> ∃!(y, in(pair(x, y), f)))) by Tautology.from(functional.definition)
    val funcDef = thenHave(functional(f) |- ∃(y, in(pair(x, y), f)) ==> ∃!(y, in(pair(x, y), f))) by InstantiateForall(x)

    have((relationDomain(f) === relationDomain(f)) <=> ∀(t, in(t, relationDomain(f)) <=> (∃(y, in(pair(t, y), f))))) by InstantiateForall(relationDomain(f))(
      relationDomain.definition of (r -> f)
    )
    thenHave(∀(t, in(t, relationDomain(f)) <=> (∃(y, in(pair(t, y), f))))) by Restate
    thenHave(in(x, relationDomain(f)) <=> (∃(y, in(pair(x, y), f)))) by InstantiateForall(x)
    val domDef = thenHave(in(x, relationDomain(f)) |- ∃(y, in(pair(x, y), f))) by Weakening

    val uniqPrem = have(functional(f) /\ in(x, relationDomain(f)) |- ∃!(z, in(pair(x, z), f))) by Tautology.from(funcDef, domDef)

    val positive = have(prem |- ∃!(z, ((prem ==> in(pair(x, z), f)) /\ (!prem ==> (z === ∅))))) subproof {
      val lhs = have(prem /\ ((z === y) <=> in(pair(x, y), f)) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ ⊤))) subproof {
        val iff = have(prem |- (in(pair(x, y), f)) <=> (prem ==> in(pair(x, y), f))) by Restate
        have(prem /\ ((z === y) <=> in(pair(x, y), f)) |- ((z === y) <=> in(pair(x, y), f))) by Restate
        val subst = thenHave((prem /\ ((z === y) <=> in(pair(x, y), f)), (in(pair(x, y), f)) <=> (prem ==> in(pair(x, y), f))) |- ((z === y) <=> (prem ==> in(pair(x, y), f)))) by RightSubstIff
          .withParametersSimple(
            List(((in(pair(x, y), f)), (prem ==> in(pair(x, y), f)))),
            lambda(h, ((z === y) <=> h))
          )

        have((prem /\ ((z === y) <=> in(pair(x, y), f)), prem) |- ((z === y) <=> (prem ==> in(pair(x, y), f)))) by Cut(iff, subst)
        thenHave(thesis) by Restate
      }

      val topIntro = have((prem, ((z === y) <=> in(pair(x, y), f))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) subproof {
        val topIff = have(prem |- (!prem ==> (y === ∅)) <=> ⊤) by Restate
        val topSubst = have(
          (prem /\ ((z === y) <=> in(pair(x, y), f)), ((!prem ==> (y === ∅)) <=> ⊤)) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))
        ) by RightSubstIff.withParametersSimple(List(((!prem ==> (y === ∅)), ⊤)), lambda(h, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ h))))(lhs)

        have((prem /\ ((z === y) <=> in(pair(x, y), f)), prem) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by Cut(topIff, topSubst)
        thenHave((prem, ((z === y) <=> in(pair(x, y), f))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by Restate
      }

      val quantification = have((prem, ∃!(z, in(pair(x, z), f))) |- ∃!(z, ((prem ==> in(pair(x, z), f)) /\ (!prem ==> (z === ∅))))) subproof {
        have((prem, ∀(y, ((z === y) <=> in(pair(x, y), f)))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by LeftForall(topIntro)
        thenHave((prem, ∀(y, ((z === y) <=> in(pair(x, y), f)))) |- ∀(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅)))))) by RightForall
        thenHave((prem, ∀(y, ((z === y) <=> in(pair(x, y), f)))) |- ∃(z, ∀(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))))) by RightExists
        thenHave(
          (prem, ∃(z, ∀(y, ((z === y) <=> in(pair(x, y), f))))) |- ∃(z, ∀(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))))
        ) by LeftExists
        thenHave(thesis) by Restate
      }

      have(thesis) by Cut(uniqPrem, quantification)
    }

    // negative
    have((∅ === y) <=> (∅ === y)) by Restate
    thenHave(∀(y, (∅ === y) <=> (∅ === y))) by RightForall
    thenHave(∃(z, ∀(y, (z === y) <=> (∅ === y)))) by RightExists
    val emptyPrem = thenHave(∃!(z, (z === ∅))) by Restate

    val negative = have(!prem |- ∃!(z, ((prem ==> in(pair(x, z), f)) /\ (!prem ==> (z === ∅))))) subproof {
      val lhs = have(!prem /\ ((z === y) <=> (y === ∅)) |- ((z === y) <=> ((!prem ==> (y === ∅)) /\ ⊤))) subproof {
        val iff = have(!prem |- ((y === ∅)) <=> (!prem ==> (y === ∅))) by Restate
        have(!prem /\ ((z === y) <=> (y === ∅)) |- ((z === y) <=> (y === ∅))) by Restate
        val subst = thenHave(
          (!prem /\ ((z === y) <=> (y === ∅)), ((y === ∅)) <=> (!prem ==> (y === ∅))) |- ((z === y) <=> (!prem ==> (y === ∅)))
        ) by RightSubstIff.withParametersSimple(List((((y === ∅)), (!prem ==> (y === ∅)))), lambda(h, ((z === y) <=> h)))

        have((!prem /\ ((z === y) <=> (y === ∅)), !prem) |- ((z === y) <=> (!prem ==> (y === ∅)))) by Cut(iff, subst)
        thenHave(thesis) by Restate
      }

      val topIntro = have((!prem, ((z === y) <=> (y === ∅))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) subproof {
        val topIff = have(!prem |- (prem ==> in(pair(x, y), f)) <=> ⊤) by Restate
        val topSubst = have(
          (!prem /\ ((z === y) <=> (y === ∅)), ((prem ==> in(pair(x, y), f)) <=> ⊤)) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))
        ) by RightSubstIff.withParametersSimple(List(((prem ==> in(pair(x, y), f)), ⊤)), lambda(h, ((z === y) <=> ((!prem ==> (y === ∅)) /\ h))))(lhs)

        have((!prem /\ ((z === y) <=> (y === ∅)), !prem) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by Cut(topIff, topSubst)
        thenHave((!prem, ((z === y) <=> (y === ∅))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by Restate
      }

      val quantification =
        have((!prem, ∃!(z, (z === ∅))) |- ∃!(z, ((prem ==> in(pair(x, z), f)) /\ (!prem ==> (z === ∅))))) subproof {
          have((!prem, ∀(y, ((z === y) <=> (y === ∅)))) |- ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by LeftForall(topIntro)
          thenHave((!prem, ∀(y, ((z === y) <=> (y === ∅)))) |- ∀(y, (z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))) by RightForall
          thenHave((!prem, ∀(y, ((z === y) <=> (y === ∅)))) |- ∃(z, ∀(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))))) by RightExists
          thenHave(
            (!prem, ∃(z, ∀(y, ((z === y) <=> (y === ∅))))) |- ∃(z, ∀(y, ((z === y) <=> ((prem ==> in(pair(x, y), f)) /\ (!prem ==> (y === ∅))))))
          ) by LeftExists
          thenHave(thesis) by Restate
        }

      have(thesis) by Cut(emptyPrem, quantification)
    }

    val negRhs = thenHave(() |- (prem, ∃!(z, ((prem ==> in(pair(x, z), f)) /\ (!prem ==> (z === ∅)))))) by Restate

    have(thesis) by Cut.withParameters(prem)(negRhs, positive)
  }

  /**
   * Function application --- denoted `f(x)`. The unique element `z` such that
   * `(x, z) ∈ f` if it exists and `f` is functional, [[emptySet]] otherwise.
   */
  val app =
    DEF(f, x) --> The(z, ((functional(f) /\ in(x, relationDomain(f))) ==> in(pair(x, z), f)) /\ ((!functional(f) \/ !in(x, relationDomain(f))) ==> (z === ∅)))(functionApplicationUniqueness)

  val pairInFunctionIsApp = Theorem(
    functional(f) /\ in(a, relationDomain(f)) |- in(pair(a, b), f) <=> (app(f, a) === b)
  ) {
    val appDef = have(
      (app(f, a) === b) <=> (((functional(f) /\ in(a, relationDomain(f))) ==> in(pair(a, b), f)) /\ ((!functional(f) \/ !in(a, relationDomain(f))) ==> (b === ∅)))
    ) by InstantiateForall(b)(app.definition of x -> a)

    assume(functional(f) /\ in(a, relationDomain(f)))

    val fwd = have(in(pair(a, b), f) |- app(f, a) === b) by Tautology.from(appDef)
    val bwd = have(app(f, a) === b |- in(pair(a, b), f)) by Tautology.from(appDef)
    have(thesis) by Tautology.from(fwd, bwd)
  }

  val functionalOverApplication = Theorem(
    functionalOver(f, x) /\ in(a, x) |- in(pair(a, b), f) <=> (app(f, a) === b)
  ) {
    assume(functionalOver(f, x))
    assume(in(a, x))

    val domEQ = have(relationDomain(f) === x) by Tautology.from(functionalOver.definition)
    have(in(a, x)) by Restate
    thenHave(in(a, relationDomain(f))) by Substitution.ApplyRules(domEQ)

    have(thesis) by Tautology.from(lastStep, functionalOver.definition, pairInFunctionIsApp)
  }

  val elemOfFunctional = Theorem(
    functional(f) |- in(t, f) <=> exists(c, exists(d, in(c, relationDomain(f)) /\ in(d, relationRange(f)) /\ (t === pair(c, d)) /\ (app(f, c) === d)))
  ) {
    // since f is a relation
    // t \in f <=> \exists c \in dom f, d \in ran f. t = (c, d)
    // we need to show that the app part of the conclusion is redundant by definition of app
    // have(functional(f) |- in(t, f) <=> exists(c, exists(d, in(c, relationDomain(f)) /\ in(d, relationRange(f)) /\ (t === pair(c, d))))) by Tautology.from(functional.definition, ???)
    sorry
  }

  val elemOfFunctionalOver = Theorem(
    functionalOver(f, a) |- in(t, f) <=> exists(c, exists(d, in(c, a) /\ in(d, relationRange(f)) /\ (t === pair(c, d)) /\ (app(f, c) === d)))
  ) {
    sorry
  }

  val elemOfFunctionFrom = Theorem(
    functionFrom(f, a, b) |- in(t, f) <=> exists(c, exists(d, in(c, a) /\ in(d, b) /\ (t === pair(c, d)) /\ (app(f, c) === d)))
  ) {
    sorry
  }

  val functionsEqualIfEqualOnDomain = Theorem(
    functionalOver(f, a) /\ functionalOver(g, a) |- forall(z, in(z, a) ==> (app(f, z) === app(g, z))) <=> (f === g)
  ) {
    assume(functionalOver(f, a))
    assume(functionalOver(g, a))

    sorry
  }

  val functionsSubsetIfEqualOnSubsetDomain = Theorem(
    functionalOver(f, a) /\ functionalOver(g, b) /\ subset(a, b) /\ forall(z, in(z, a) ==> (app(f, z) === app(g, z))) |- subset(f, g)
  ) {
    assume(functionalOver(f, a))
    assume(functionalOver(g, b))

    sorry
  }

  val restrictedFunctionUniqueness = Theorem(
    ∃!(g, ∀(t, in(t, g) <=> (in(t, f) /\ ∃(y, ∃(z, in(y, x) /\ (t === pair(y, z)))))))
  ) {
    have(∃!(g, ∀(t, in(t, g) <=> (in(t, f) /\ ∃(y, ∃(z, in(y, x) /\ (t === pair(y, z)))))))) by UniqueComprehension(
      f,
      lambda(t, ∃(y, ∃(z, in(y, x) /\ (t === pair(y, z)))))
    )
  }

  /**
   * Function Restriction ---  The restriction of a function f to a domain x,
   * also written as f_x.
   *
   *    `restrictedFunction(f, x) = {(y, f(y)) | y ∈ x}`
   *
   * @param f function (set)
   * @param x set to restrict to
   */
  val restrictedFunction = DEF(f, x) --> The(g, ∀(t, in(t, g) <=> (in(t, f) /\ ∃(y, ∃(z, in(y, x) /\ (t === pair(y, z)))))))(restrictedFunctionUniqueness)

  /**
   * Pair membership in a restricted function -- A pair `(t, a)` is in `f_x` iff `(t, a) ∈ f` and `t ∈ x`.
   *
   * This is a direct but painful corollary of the definition.
   */
  val restrictedFunctionPairMembership = Lemma(
    in(pair(t, a), restrictedFunction(f, x)) <=> (in(pair(t, a), f) /\ in(t, x))
  ) {
    val g = restrictedFunction(f, x)

    have(∀(t, in(t, g) <=> (in(t, f) /\ ∃(y, ∃(z, in(y, x) /\ (t === pair(y, z))))))) by Definition(
      restrictedFunction,
      restrictedFunctionUniqueness
    )(f, x)
    val pairMembership = thenHave(
      in(pair(t, a), g) <=> (in(pair(t, a), f) /\ ∃(y, ∃(z, in(y, x) /\ (pair(t, a) === pair(y, z)))))
    ) by InstantiateForall(pair(t, a))

    have((pair(t, a) === pair(y, z)) <=> ((t === y) /\ (a === z))) by Restate.from(pairExtensionality of (a -> t, b -> a, c -> y, d -> z))
    thenHave((in(y, x) /\ (pair(t, a) === pair(y, z))) <=> (in(y, x) /\ (t === y) /\ (a === z))) by Tautology
    thenHave(∀(z, (in(y, x) /\ (pair(t, a) === pair(y, z))) <=> (in(y, x) /\ (t === y) /\ (a === z)))) by RightForall

    val existentialEquiv1 = have(∃(z, in(y, x) /\ (pair(t, a) === pair(y, z))) <=> ∃(z, in(y, x) /\ (t === y) /\ (a === z))) by Cut(
      lastStep,
      existentialEquivalenceDistribution of (
        P -> lambda(z, in(y, x) /\ (pair(t, a) === pair(y, z))),
        Q -> lambda(z, in(y, x) /\ (t === y) /\ (a === z))
      )
    )

    have(∃(z, in(y, x) /\ (t === y) /\ (a === z)) <=> (in(y, x) /\ (t === y))) by Restate.from(
      equalityInExistentialQuantifier of (
        P -> lambda(z, in(y, x) /\ (t === y)),
        y -> a
      )
    )

    have(∃(z, in(y, x) /\ (pair(t, a) === pair(y, z))) <=> (in(y, x) /\ (t === y))) by Tautology.from(existentialEquiv1, lastStep)
    thenHave(∀(y, ∃(z, in(y, x) /\ (pair(t, a) === pair(y, z))) <=> (in(y, x) /\ (t === y)))) by RightForall

    val existentialEquiv2 = have(∃(y, ∃(z, in(y, x) /\ (pair(t, a) === pair(y, z)))) <=> ∃(y, in(y, x) /\ (t === y))) by Cut(
      lastStep,
      existentialEquivalenceDistribution of (
        P -> lambda(y, ∃(z, in(y, x) /\ (pair(t, a) === pair(y, z)))),
        Q -> lambda(y, in(y, x) /\ (t === y))
      )
    )

    have(∃(y, in(y, x) /\ (t === y)) <=> in(t, x)) by Restate.from(
      equalityInExistentialQuantifier of (
        P -> lambda(y, in(y, x)),
        y -> t
      )
    )

    have(∃(y, ∃(z, in(y, x) /\ (pair(t, a) === pair(y, z)))) <=> in(t, x)) by Tautology.from(existentialEquiv2, lastStep)
    thenHave((in(pair(t, a), f) /\ ∃(y, ∃(z, in(y, x) /\ (pair(t, a) === pair(y, z))))) <=> (in(pair(t, a), f) /\ in(t, x))) by Tautology

    have(thesis) by Tautology.from(lastStep, pairMembership)
  }

  /**
   * Restricted function domain -- For a function `f`, the domain of `f_x` is `x ∩ relationDomain(f)`.
   */
  val restrictedFunctionDomain = Theorem(
    relationDomain(restrictedFunction(f, x)) === (x ∩ relationDomain(f))
  ) {
    val D = variable
    val dom = x ∩ relationDomain(f)
    val g = restrictedFunction(f, x)

    // Characterize x ∩ relationDomain(f)
    val domCharacterization = have(∀(t, in(t, dom) <=> (∃(a, in(pair(t, a), f)) /\ in(t, x)))) subproof {
      // Use the definition of the intersection
      have(∀(t, in(t, dom) <=> (in(t, x) /\ in(t, relationDomain(f))))) by Definition(
        setIntersection,
        setIntersectionUniqueness
      )(x, relationDomain(f))
      val intersectionDef = thenHave(in(t, dom) <=> (in(t, x) /\ in(t, relationDomain(f)))) by InstantiateForall(t)

      // Use the definition of the relation domain
      have(∀(t, in(t, relationDomain(f)) <=> ∃(a, in(pair(t, a), f)))) by Definition(
        relationDomain,
        relationDomainUniqueness
      )(f)
      thenHave(in(t, relationDomain(f)) <=> ∃(a, in(pair(t, a), f))) by InstantiateForall(t)

      // Conclude
      have(in(t, dom) <=> (∃(a, in(pair(t, a), f)) /\ in(t, x))) by Tautology.from(intersectionDef, lastStep)
      thenHave(thesis) by RightForall
    }

    // Characterize the domain of g
    have(∀(D, (relationDomain(g) === D) <=> ∀(t, in(t, D) <=> ∃(a, in(pair(t, a), g))))) by Tautology.from(
      relationDomain.definition of (r -> g),
      relationDomainUniqueness
    )
    val characterization = thenHave((relationDomain(g) === dom) <=> ∀(t, in(t, dom) <=> ∃(a, in(pair(t, a), g)))) by InstantiateForall(dom)

    // Use the membership of a pair in the restricted function to derive a simpler characterization
    have(∀(a, in(pair(t, a), g) <=> (in(pair(t, a), f) /\ in(t, x)))) by RightForall(restrictedFunctionPairMembership)
    have(∃(a, in(pair(t, a), g)) <=> ∃(a, in(pair(t, a), f) /\ in(t, x))) by Tautology.from(
      lastStep,
      existentialEquivalenceDistribution of (
        P -> lambda(a, in(pair(t, a), g)),
        Q -> lambda(a, in(pair(t, a), f) /\ in(t, x))
      )
    )

    // Extract in(t, x) from the existential quantifier
    val p = formulaVariable // local shadowing to correctly use the theorem
    have(∃(a, in(pair(t, a), g)) <=> ∃(a, in(pair(t, a), f)) /\ in(t, x)) by Tautology.from(
      lastStep,
      existentialConjunctionWithClosedFormula of (
        P -> lambda(a, in(pair(t, a), f)),
        p -> in(t, x)
      )
    )

    thenHave((in(t, dom) <=> ∃(a, in(pair(t, a), g))) <=> (in(t, dom) <=> ∃(a, in(pair(t, a), f)) /\ in(t, x))) by Tautology
    thenHave(∀(t, (in(t, dom) <=> ∃(a, in(pair(t, a), g))) <=> (in(t, dom) <=> ∃(a, in(pair(t, a), f)) /\ in(t, x)))) by RightForall

    have(∀(t, in(t, dom) <=> ∃(a, in(pair(t, a), g))) <=> ∀(t, in(t, dom) <=> ∃(a, in(pair(t, a), f)) /\ in(t, x))) by Cut(
      lastStep,
      universalEquivalenceDistribution of (
        P -> lambda(t, in(t, dom) <=> ∃(a, in(pair(t, a), g))),
        Q -> lambda(t, in(t, dom) <=> ∃(a, in(pair(t, a), f)) /\ in(t, x))
      )
    )

    val simplerCharacterization = have((relationDomain(g) === dom) <=> ∀(t, in(t, dom) <=> ∃(a, in(pair(t, a), f)) /\ in(t, x))) by Tautology.from(characterization, lastStep)

    have(thesis) by Tautology.from(domCharacterization, simplerCharacterization)
  }

  val restrictedFunctionIsFunctionalOver = Lemma(
    functional(f) |- functionalOver(restrictedFunction(f, x), setIntersection(x, relationDomain(f)))
  ) {
    // restriction is a function

    // its domain is indeed x \cap dom f

    // it is functionalOver its domain

    sorry
  }

  val restrictedFunctionApplication = Lemma(
    in(y, x) |- app(f, y) === app(restrictedFunction(f, x), y)
  ) {
    sorry
  }

  /**
   * Restricted function cancellation --- Restricting a function to its relation domain does nothing.
   */
  val restrictedFunctionCancellation = Theorem(
    functional(f) |- restrictedFunction(f, relationDomain(f)) === f
  ) {
    val g = restrictedFunction(f, relationDomain(f))

    assume(functional(f))

    have(∀(t, in(t, relationDomain(f)) <=> ∃(a, in(pair(t, a), f)))) by Definition(relationDomain, relationDomainUniqueness)(f)
    thenHave(in(y, relationDomain(f)) <=> ∃(a, in(pair(y, a), f))) by InstantiateForall(y)

    have(∀(t, in(t, g) <=> (in(t, f) /\ ∃(y, ∃(z, in(y, relationDomain(f)) /\ (t === pair(y, z))))))) by Definition(
      restrictedFunction,
      restrictedFunctionUniqueness
    )(f, relationDomain(f))
    val equiv = thenHave(in(t, g) <=> (in(t, f) /\ ∃(y, ∃(z, in(y, relationDomain(f)) /\ (t === pair(y, z)))))) by InstantiateForall(t)

    // Prove that the second part of the conjunction is extraneous
    val hypo = have(in(t, f) |- in(t, f)) by Hypothesis
    have(in(t, f) |- ∃(y, ∃(z, in(y, relationDomain(f)) /\ (t === pair(y, z))))) by InstantiateForall(t)(functionalMembership)
    have(in(t, f) |- in(t, f) /\ ∃(y, ∃(z, in(y, relationDomain(f)) /\ (t === pair(y, z))))) by RightAnd(hypo, lastStep)
    val forward = thenHave(in(t, f) ==> (in(t, f) /\ ∃(y, ∃(z, in(y, relationDomain(f)) /\ (t === pair(y, z)))))) by Restate

    val backward = have(in(t, f) /\ ∃(y, ∃(z, in(y, relationDomain(f)) /\ (t === pair(y, z)))) ==> in(t, f)) by Tautology

    have(in(t, f) <=> (in(t, f) /\ ∃(y, ∃(z, in(y, relationDomain(f)) /\ (t === pair(y, z)))))) by RightIff(forward, backward)

    // Conclude by extensionnality
    have(in(t, g) <=> in(t, f)) by Tautology.from(equiv, lastStep)
    thenHave(∀(t, in(t, g) <=> in(t, f))) by RightForall

    have(g === f) by Tautology.from(extensionalityAxiom of (x -> g, y -> f), lastStep)
  }

  val restrictedFunctionAbsorption = Theorem(
    restrictedFunction(restrictedFunction(f, x), y) === restrictedFunction(f, setIntersection(x, y))
  ) {
    sorry
  }

  /**
   * Theorem --- if `f` is [[functional]] over `x`, then `x` is precisely its
   * domain as a relation.
   */
  val functionalOverImpliesDomain = Theorem(
    functionalOver(f, x) |- (relationDomain(f) === x)
  ) {
    have(thesis) by Tautology.from(functionalOver.definition)
  }

  /**
   * Theorem --- if `f` is a [[functionFrom]] `x` to `y`, i.e. `f ∈ x → y`,
   * then `x` is precisely its domain as a relation.
   */
  val functionFromImpliesDomainEq = Theorem(
    functionFrom(f, x, y) |- (relationDomain(f) === x)
  ) {
    have(∀(t, in(t, setOfFunctions(x, y)) <=> (in(t, powerSet(cartesianProduct(x, y))) /\ functionalOver(t, x)))) by InstantiateForall(setOfFunctions(x, y))(setOfFunctions.definition)
    val funSetDef = thenHave(in(f, setOfFunctions(x, y)) <=> (in(f, powerSet(cartesianProduct(x, y))) /\ functionalOver(f, x))) by InstantiateForall(f)

    have(thesis) by Tautology.from(functionFrom.definition, funSetDef, functionalOver.definition)
  }

  /**
   * Theorem --- the range of a function is a subset of its codomain.
   */
  val functionImpliesRangeSubsetOfCodomain = Theorem(
    functionFrom(f, x, y) |- subset(relationRange(f), y)
  ) {
    have(∀(t, in(t, setOfFunctions(x, y)) <=> (in(t, powerSet(cartesianProduct(x, y))) /\ functionalOver(t, x)))) by InstantiateForall(setOfFunctions(x, y))(setOfFunctions.definition)
    val funSetDef = thenHave(in(f, setOfFunctions(x, y)) <=> (in(f, powerSet(cartesianProduct(x, y))) /\ functionalOver(f, x))) by InstantiateForall(f)

    have(functionFrom(f, x, y) |- ∀(z, in(z, f) ==> in(z, cartesianProduct(x, y)))) by Tautology.from(
      functionFrom.definition,
      funSetDef,
      powerAxiom of (x -> f, y -> cartesianProduct(x, y)),
      subsetAxiom of (x -> f, y -> cartesianProduct(x, y))
    )
    thenHave(functionFrom(f, x, y) |- in(pair(a, t), f) ==> in(pair(a, t), cartesianProduct(x, y))) by InstantiateForall(pair(a, t))
    thenHave((functionFrom(f, x, y), in(pair(a, t), f)) |- in(pair(a, t), cartesianProduct(x, y))) by Restate
    andThen(Substitution.applySubst(pairInCartesianProduct of (b -> t)))
    thenHave((functionFrom(f, x, y), in(pair(a, t), f)) |- in(t, y)) by Weakening
    val funFromty = thenHave((functionFrom(f, x, y), ∃(a, in(pair(a, t), f))) |- in(t, y)) by LeftExists

    have(∀(t, in(t, relationRange(f)) <=> (∃(a, in(pair(a, t), f))))) by InstantiateForall(relationRange(f))(relationRange.definition of (r -> f))
    thenHave(in(t, relationRange(f)) <=> (∃(a, in(pair(a, t), f)))) by InstantiateForall(t)
    val ranat = thenHave(in(t, relationRange(f)) |- ∃(a, in(pair(a, t), f))) by Weakening

    have((functionFrom(f, x, y), in(t, relationRange(f))) |- in(t, y)) by Cut(ranat, funFromty)
    thenHave((functionFrom(f, x, y)) |- in(t, relationRange(f)) ==> in(t, y)) by Restate
    thenHave((functionFrom(f, x, y)) |- ∀(t, in(t, relationRange(f)) ==> in(t, y))) by RightForall
    andThen(Substitution.applySubst(subsetAxiom of (x -> relationRange(f))))
  }

  /**
   * Theorem --- if a set is in the range of a function, then there exists atleast
   * one element in the domain mapping to it.
   */
  val inRangeImpliesPullbackExists = Theorem(
    functional(f) /\ in(z, relationRange(f)) |- ∃(t, in(t, relationDomain(f)) /\ (app(f, t) === z))
  ) {
    val appIff = have(
      (z === app(f, t)) <=> ((functional(f) /\ in(t, relationDomain(f))) ==> in(pair(t, z), f)) /\ ((!functional(f) \/ !in(t, relationDomain(f))) ==> (z === ∅))
    ) by InstantiateForall(z)(app.definition of (x -> t))

    have(∀(t, in(t, relationRange(f)) <=> ∃(a, in(pair(a, t), f)))) by InstantiateForall(relationRange(f))(relationRange.definition of (r -> f))
    thenHave(in(z, relationRange(f)) <=> ∃(a, in(pair(a, z), f))) by InstantiateForall(z)
    val elementInDomainExists = thenHave(in(z, relationRange(f)) |- ∃(t, in(pair(t, z), f))) by Weakening

    val toApp = have(
      (functional(f), in(t, relationDomain(f)), in(pair(t, z), f)) |- ((functional(f) /\ in(t, relationDomain(f))) ==> in(pair(t, z), f)) /\ ((!functional(f) \/ !in(
        t,
        relationDomain(f)
      )) ==> (z === ∅))
    ) by Restate
    val zAppdom = have((functional(f), in(t, relationDomain(f)), in(pair(t, z), f)) |- (z === app(f, t))) by Tautology.from(toApp, appIff)

    val pairInDomain = have(in(pair(t, z), f) |- in(t, relationDomain(f))) subproof {
      have(∀(t, in(t, relationDomain(f)) <=> ∃(a, in(pair(t, a), f)))) by InstantiateForall(relationDomain(f))(relationDomain.definition of (r -> f))
      val domDef = thenHave(in(t, relationDomain(f)) <=> ∃(a, in(pair(t, a), f))) by InstantiateForall(t)

      have(in(pair(t, z), f) |- in(pair(t, z), f)) by Hypothesis
      val pairEx = thenHave(in(pair(t, z), f) |- ∃(a, in(pair(t, a), f))) by RightExists

      have(thesis) by Tautology.from(domDef, pairEx)
    }

    val zApp2 = have((functional(f), in(pair(t, z), f)) |- (z === app(f, t))) by Cut(pairInDomain, zAppdom)
    have((functional(f), in(pair(t, z), f)) |- in(t, relationDomain(f)) /\ (z === app(f, t))) by RightAnd(pairInDomain, zApp2)
    thenHave((functional(f), in(pair(t, z), f)) |- ∃(t, in(t, relationDomain(f)) /\ (z === app(f, t)))) by RightExists
    val zAppIfExists = thenHave((functional(f), ∃(t, in(pair(t, z), f))) |- ∃(t, in(t, relationDomain(f)) /\ (z === app(f, t)))) by LeftExists

    have((functional(f), in(z, relationRange(f))) |- ∃(t, in(t, relationDomain(f)) /\ (z === app(f, t)))) by Cut(elementInDomainExists, zAppIfExists)
    thenHave(thesis) by Restate
  }

  /**
   * Theorem --- Union of two functions is a function if they agree on the
   * intersection of their domains.
   *
   *    `functional(f) ∧ functional(g) ∧ ∀ x, y. x ∈ dom(f) ∧ x ∈ dom(g) ⟹ (x, y) ∈ f <=> (x, y) ∈ g ⊢ functional(f ∪ g)`
   */
  val unionOfFunctionsIsAFunction = Theorem(
    functional(f) /\ functional(g) /\ forall(x, forall(y, (in(x, relationDomain(f)) /\ in(x, relationDomain(g))) ==> (in(pair(x, y), f) <=> in(pair(x, y), g)))) |- functional(setUnion(f, g))
  ) {
    // some renaming for convenience
    val domF = relationDomain(f)
    val domG = relationDomain(g)

    val h = setUnion(f, g)
    val domH = setUnion(domF, domG)

    // is a relation
    val isRelation = have(functional(f) /\ functional(g) |- relation(h)) by Tautology.from(functional.definition, functional.definition of f -> g, unionOfTwoRelations)

    // has the uniqueness property
    val isFunctional = have(
      functional(f) /\ functional(g) /\ forall(x, forall(y, (in(x, relationDomain(f)) /\ in(x, relationDomain(g))) ==> (in(pair(x, y), f) <=> in(pair(x, y), g)))) |- forall(
        x,
        exists(y, in(pair(x, y), h)) ==> existsOne(y, in(pair(x, y), h))
      )
    ) subproof {
      // x in domH <=> x in domF \/ x in domG
      val domHDef = have(in(x, domH) <=> (in(x, domF) \/ in(x, domG))) by Restate.from(setUnionMembership of (z -> x, x -> domF, y -> domG))

      // x in domF/G <=> exists y. xy in F/G
      have(forall(t, in(t, domF) <=> exists(y, in(pair(t, y), f)))) by InstantiateForall(domF)(relationDomain.definition of r -> f)
      val xInDomF = thenHave(in(x, domF) <=> exists(y, in(pair(x, y), f))) by InstantiateForall(x)
      val xInDomG = xInDomF of f -> g

      val xInDomFOne = have((functional(f), in(x, domF)) |- existsOne(y, in(pair(x, y), f))) subproof {
        have(functional(f) |- forall(x, exists(y, in(pair(x, y), f)) ==> existsOne(y, in(pair(x, y), f)))) by Weakening(functional.definition)
        thenHave(functional(f) |- exists(y, in(pair(x, y), f)) ==> existsOne(y, in(pair(x, y), f))) by InstantiateForall(x)

        have(thesis) by Tautology.from(lastStep, xInDomF)
      }

      // x in domH <=> exists y. xy in H OR domH = relationDomain(h)
      val domHIsDomain = have(in(x, domH) <=> exists(y, in(pair(x, y), h))) subproof {
        have(exists(y, in(pair(x, y), h)) <=> (exists(y, in(pair(x, y), f)) \/ exists(y, in(pair(x, y), g)))) subproof {
          have(in(pair(x, y), h) <=> (in(pair(x, y), f) \/ in(pair(x, y), g))) by Restate.from(setUnionMembership of (z -> pair(x, y), x -> f, y -> g))
          thenHave(forall(y, in(pair(x, y), h) <=> (in(pair(x, y), f) \/ in(pair(x, y), g)))) by RightForall
          have(exists(y, in(pair(x, y), h)) <=> exists(y, in(pair(x, y), f) \/ in(pair(x, y), g))) by Tautology.from(
            lastStep,
            existentialEquivalenceDistribution of (P -> lambda(y, in(pair(x, y), h)), Q -> lambda(y, in(pair(x, y), f) \/ in(pair(x, y), g)))
          )
          // have(exists(y, in(pair(x, y), h)) <=> (exists(y, in(pair(x, y), f)) \/ exists(y, in(pair(x, y), g)))) by Tautology.from(lastStep, existentialDisjunctionCommutation of (P -> lambda(y, in(pair(x, y), f)), Q -> lambda(y, in(pair(x, y), g)))) // TODO: Possible Tautology Bug
          thenHave(exists(y, in(pair(x, y), h)) <=> (exists(y, in(pair(x, y), f)) \/ exists(y, in(pair(x, y), g)))) by Substitution.ApplyRules(
            existentialDisjunctionCommutation of (P -> lambda(y, in(pair(x, y), f)), Q -> lambda(y, in(pair(x, y), g))) // BUG: ?
          )
        }

        have(thesis) by Tautology.from(lastStep, domHDef, xInDomF, xInDomG)
      }

      // x in domF and x not in domG
      have(functional(f) |- forall(x, exists(y, in(pair(x, y), f)) ==> existsOne(y, in(pair(x, y), f)))) by Weakening(functional.definition)
      val exToExOne = thenHave((functional(f), exists(y, in(pair(x, y), f))) |- existsOne(y, in(pair(x, y), f))) by InstantiateForall(x)

      have(forall(y, !in(pair(x, y), g)) |- existsOne(y, in(pair(x, y), f)) <=> existsOne(y, in(pair(x, y), h))) subproof {
        val fwd = have(in(pair(x, y), f) |- in(pair(x, y), h)) by Tautology.from(setUnionMembership of (z -> pair(x, y), x -> f, y -> g))
        val notzg = have(forall(y, !in(pair(x, y), g)) |- !in(pair(x, y), g)) by InstantiateForall
        have(in(pair(x, y), h) <=> (in(pair(x, y), f) \/ in(pair(x, y), g))) by Restate.from(setUnionMembership of (z -> pair(x, y), x -> f, y -> g))

        have(forall(y, !in(pair(x, y), g)) |- in(pair(x, y), h) <=> (in(pair(x, y), f))) by Tautology.from(lastStep, notzg, fwd)
        thenHave(forall(y, !in(pair(x, y), g)) |- forall(y, in(pair(x, y), h) <=> (in(pair(x, y), f)))) by RightForall

        have(forall(y, !in(pair(x, y), g)) |- existsOne(y, in(pair(x, y), h)) <=> existsOne(y, in(pair(x, y), f))) by Tautology.from(
          lastStep,
          uniqueExistentialEquivalenceDistribution of (P -> lambda(z, in(pair(x, z), h)), Q -> lambda(z, in(pair(x, z), f)))
        )
      }

      val notInG = have((functional(f), in(x, domF), !in(x, domG)) |- existsOne(y, in(pair(x, y), h))) by Tautology.from(lastStep, xInDomFOne, xInDomG)

      // x not in domF and x in domG
      val notInF =
        have((functional(g), !in(x, domF), in(x, domG)) |- existsOne(y, in(pair(x, y), h))) by Substitution.ApplyRules(unionCommutativity)(notInG of (f -> g, g -> f))

      // x in domF and in domG
      have(
        forall(x, forall(y, (in(x, domF) /\ in(x, domG)) ==> (in(pair(x, y), f) <=> in(pair(x, y), g)))) |- forall(
          x,
          forall(y, (in(x, domF) /\ in(x, domG)) ==> (in(pair(x, y), f) <=> in(pair(x, y), g)))
        )
      ) by Hypothesis
      thenHave(
        forall(x, forall(y, (in(x, domF) /\ in(x, domG)) ==> (in(pair(x, y), f) <=> in(pair(x, y), g)))) |- (in(x, domF) /\ in(x, domG)) ==> (in(pair(x, y), f) <=> in(pair(x, y), g))
      ) by InstantiateForall(x, y)
      thenHave((forall(x, forall(y, (in(x, domF) /\ in(x, domG)) ==> (in(pair(x, y), f) <=> in(pair(x, y), g)))), in(x, domF), in(x, domG)) |- (in(pair(x, y), f) <=> in(pair(x, y), g))) by Restate
      val FToFG = thenHave(
        (forall(x, forall(y, (in(x, domF) /\ in(x, domG)) ==> (in(pair(x, y), f) <=> in(pair(x, y), g)))), in(x, domF), in(x, domG)) |- (in(pair(x, y), f) <=> (in(pair(x, y), g) \/ in(pair(x, y), f)))
      ) by Tautology

      have(in(pair(x, y), h) <=> (in(pair(x, y), f) \/ in(pair(x, y), g))) by Restate.from(setUnionMembership of (z -> pair(x, y), x -> f, y -> g))

      have((forall(x, forall(y, (in(x, domF) /\ in(x, domG)) ==> (in(pair(x, y), f) <=> in(pair(x, y), g)))), in(x, domF), in(x, domG)) |- (in(pair(x, y), f) <=> in(pair(x, y), h))) by Tautology.from(
        lastStep,
        FToFG
      )
      thenHave(
        (forall(x, forall(y, (in(x, domF) /\ in(x, domG)) ==> (in(pair(x, y), f) <=> in(pair(x, y), g)))), in(x, domF), in(x, domG)) |- forall(y, in(pair(x, y), f) <=> in(pair(x, y), h))
      ) by RightForall
      have(
        (forall(x, forall(y, (in(x, domF) /\ in(x, domG)) ==> (in(pair(x, y), f) <=> in(pair(x, y), g)))), in(x, domF), in(x, domG)) |- (existsOne(y, in(pair(x, y), f)) <=> existsOne(
          y,
          in(pair(x, y), h)
        ))
      ) by Tautology.from(lastStep, uniqueExistentialEquivalenceDistribution of (P -> lambda(z, in(pair(x, z), h)), Q -> lambda(z, in(pair(x, z), f))))
      val inFAndG = have(
        (functional(f), forall(x, forall(y, (in(x, domF) /\ in(x, domG)) ==> (in(pair(x, y), f) <=> in(pair(x, y), g)))), in(x, domF), in(x, domG)) |- (existsOne(y, in(pair(x, y), h)))
      ) by Tautology.from(lastStep, xInDomFOne)

      have(
        (functional(f), functional(g), forall(x, forall(y, (in(x, domF) /\ in(x, domG)) ==> (in(pair(x, y), f) <=> in(pair(x, y), g))))) |- in(x, domH) ==> existsOne(y, in(pair(x, y), h))
      ) by Tautology.from(inFAndG, notInF, notInG, domHDef)
      thenHave(
        (functional(f), functional(g), forall(x, forall(y, (in(x, domF) /\ in(x, domG)) ==> (in(pair(x, y), f) <=> in(pair(x, y), g))))) |- exists(y, in(pair(x, y), h)) ==> existsOne(
          y,
          in(pair(x, y), h)
        )
      ) by Substitution.ApplyRules(domHIsDomain)
      thenHave(
        (functional(f), functional(g), forall(x, forall(y, (in(x, domF) /\ in(x, domG)) ==> (in(pair(x, y), f) <=> in(pair(x, y), g))))) |- forall(
          x,
          exists(y, in(pair(x, y), h)) ==> existsOne(y, in(pair(x, y), h))
        )
      ) by RightForall
    }

    have(thesis) by Tautology.from(functional.definition of f -> h, isRelation, isFunctional)
  }

  val unionOfFunctionsWithDisjointDomains = Theorem(
    functionalOver(f, a) /\ functionalOver(g, b) /\ (setIntersection(a, b) === emptySet) |- functionalOver(setUnion(f, g), setUnion(a, b))
  ) {
    // union is functional

    // domain of union is union of domains

    sorry
  }

  /**
   * Theorem --- Union of a Set of Functions is a Function
   *
   * Given a set `z` of functions (weakly or [[reflexive]]ly) totally ordered by
   * the [[subset]] relation on the elements' domains ([[relationDomain]]), `∪
   * z` is [[functional]] (in particular, with domain as the union of the
   * elements' domains).
   */
  val unionOfFunctionSet = Theorem(
    forall(t, in(t, z) ==> functional(t)) /\ forall(x, forall(y, (in(x, z) /\ in(y, z)) ==> (subset(x, y) \/ subset(y, x)))) |- functional(union(z))
  ) {
    // add assumptions
    assume(forall(t, in(t, z) ==> functional(t)), forall(x, forall(y, (in(x, z) /\ in(y, z)) ==> (subset(x, y) \/ subset(y, x)))))

    // assume, towards a contradiction
    assume(!functional(union(z)))

    val u = union(z)

    // begin proof ----------------

    // u is a relation
    have(in(t, z) ==> functional(t)) by InstantiateForall
    have(in(t, z) ==> relation(t)) by Tautology.from(lastStep, functional.definition of f -> t)
    thenHave(forall(t, in(t, z) ==> relation(t))) by RightForall
    val relU = have(relation(u)) by Tautology.from(lastStep, unionOfRelationSet)

    // if u is not functional, there exists a violating pair in it
    val notFun = have(exists(x, exists(y, in(pair(x, y), u)) /\ !existsOne(y, in(pair(x, y), u)))) by Tautology.from(relU, functional.definition of f -> u)

    // the violating pairs must each come from a function in z
    val exfg = have((in(pair(x, y), u), in(pair(x, w), u), !(y === w)) |- exists(f, in(f, z) /\ in(pair(x, y), f)) /\ exists(g, in(g, z) /\ in(pair(x, w), g))) by Tautology.from(
      unionAxiom of (x -> z, z -> pair(x, y)),
      unionAxiom of (x -> z, z -> pair(x, w))
    )

    have((exists(f, in(f, z) /\ in(pair(x, y), f)), exists(g, in(g, z) /\ in(pair(x, w), g)), !(y === w)) |- ()) subproof {
      have(forall(x, forall(y, (in(x, z) /\ in(y, z)) ==> (subset(x, y) \/ subset(y, x))))) by Restate
      val subfg = thenHave((in(f, z) /\ in(g, z)) ==> (subset(f, g) \/ subset(g, f))) by InstantiateForall(f, g)

      have(forall(t, in(t, z) ==> functional(t))) by Restate
      val funF = thenHave(in(f, z) ==> functional(f)) by InstantiateForall(f)
      val funG = funF of f -> g

      val fg = have((in(f, z) /\ in(pair(x, y), f), in(g, z) /\ in(pair(x, w), g), !(y === w), subset(f, g)) |- ()) subproof {
        have(subset(f, g) |- forall(t, in(t, f) ==> in(t, g))) by Weakening(subsetAxiom of (x -> f, y -> g))
        thenHave(subset(f, g) |- in(pair(x, y), f) ==> in(pair(x, y), g)) by InstantiateForall(pair(x, y))
        thenHave((in(f, z) /\ in(pair(x, y), f), in(g, z) /\ in(pair(x, w), g), !(y === w), subset(f, g)) |- in(pair(x, y), g) /\ in(pair(x, w), g) /\ !(y === w)) by Tautology
        have(thesis) by Tautology.from(lastStep, funG, violatingPairInFunction of (f -> g, z -> w))
      }

      val gf = have((in(f, z) /\ in(pair(x, y), f), in(g, z) /\ in(pair(x, w), g), !(y === w), subset(g, f)) |- ()) subproof {
        have(subset(g, f) |- forall(t, in(t, g) ==> in(t, f))) by Weakening(subsetAxiom of (x -> g, y -> f))
        thenHave(subset(g, f) |- in(pair(x, w), g) ==> in(pair(x, w), f)) by InstantiateForall(pair(x, w))
        thenHave((in(f, z) /\ in(pair(x, y), f), in(g, z) /\ in(pair(x, w), g), !(y === w), subset(g, f)) |- in(pair(x, w), f) /\ in(pair(x, y), f) /\ !(y === w)) by Tautology
        have(thesis) by Tautology.from(lastStep, funF, violatingPairInFunction of (f -> f, z -> w))
      }

      have((in(f, z) /\ in(pair(x, y), f), in(g, z) /\ in(pair(x, w), g), !(y === w)) |- ()) by Tautology.from(subfg, fg, gf)
      thenHave((exists(f, in(f, z) /\ in(pair(x, y), f)), (in(g, z) /\ in(pair(x, w), g)), !(y === w)) |- ()) by LeftExists
      thenHave(thesis) by LeftExists
    }

    have((in(pair(x, y), u) /\ in(pair(x, w), u) /\ !(y === w)) |- ()) by Tautology.from(lastStep, exfg)
    thenHave(exists(w, in(pair(x, y), u) /\ in(pair(x, w), u) /\ !(y === w)) |- ()) by LeftExists
    thenHave(exists(y, exists(w, in(pair(x, y), u) /\ in(pair(x, w), u) /\ !(y === w))) |- ()) by LeftExists

    have(exists(y, in(pair(x, y), u)) /\ !existsOne(y, in(pair(x, y), u)) |- ()) by Tautology.from(lastStep, atleastTwoExist of P -> lambda(y, in(pair(x, y), u)))
    thenHave(exists(x, exists(y, in(pair(x, y), u)) /\ !existsOne(y, in(pair(x, y), u))) |- ()) by LeftExists

    // contradiction
    have(thesis) by Tautology.from(lastStep, notFun)
  }

  /**
   * Theorem --- Domain of Functional Union
   *
   * If the unary union of a set is functional, then its domain is defined
   * precisely by the union of the domains of its elements.
   *
   *    functional(\cup z) |- \forall t. t \in dom(U z) <=> \exists y \in z. t
   *    \in dom(y)
   *
   * This holds, particularly, as the elements of z must be functions
   * themselves, which follows from the assumption.
   */
  val domainOfFunctionalUnion = Theorem(
    functional(union(z)) |- forall(t, in(t, relationDomain(union(z))) <=> exists(y, in(y, z) /\ in(t, relationDomain(y))))
  ) {
    assume(functional(union(z)))
    have(relation(union(z))) by Tautology.from(functional.definition of f -> union(z))
    have(thesis) by Tautology.from(lastStep, domainOfRelationalUnion)
  }
}
