package lisa.maths.settheory

import lisa.maths.SetTheory.Base.Predef.*

/** Set Theory Library
  *
  * Develops Zermelo-Fraenkel Set Theory.
  * Uses the following book as the main reference:
  *
  * Jech, Thomas. Set theory: The third millennium edition, revised and expanded.
  * Springer Berlin Heidelberg, 2003.
  * [[https://link.springer.com/book/10.1007/3-540-44761-X]]
  */
object SetTheory extends lisa.Main {

  // Variables
  private val a, b, c, d = variable[Ind]
  private val x, y, z = variable[Ind]
  private val h = variable[Prop]
  private val w, t = variable[Ind]

  // Set relations and function symbols
  private val r = variable[Ind]
  private val p = variable[Ind]
  private val f, g = variable[Ind]

  private val P, Q = variable[Ind >>: Prop]
  private val R = variable[Ind >>: Ind >>: Prop]

  /** A set is an arbitrary term of the theory.
    */
  type Set = Expr[Ind]

  /** Chapter 1
    */

  /** Axioms of Set Theory
    *
    * See [[SetTheoryLibrary]].
    */

  /** Theorem --- Russel's Paradox
    *
    * Consider a set `x`, that contains every set that is not a member of itself.
    * The existence of `x` leads to a contradiction, for we get that
    *
    *   `x ∈ x <=> x ∉ x`.
    *
    * This paradox forces the current form of the comprehension schema, i.e. `{x ∈ S | φ(x)}`
    * instead of `{x | φ(x)}`.
    */
  val `Russel's paradox` = Theorem(
    ∃(y, ∀(x, x ∈ y <=> x ∉ x)) |- ()
  ) {
    have(y ∈ y <=> y ∉ y |- ()) by Tautology
    thenHave(∀(x, x ∈ y <=> x ∉ x) |- ()) by LeftForall
    thenHave(∃(y, ∀(x, x ∈ y <=> x ∉ x)) |- ()) by LeftExists
  }


  //////////////////////////////////////////////////////////////////////////////
  section("Inductive sets")

  // TODO: This should be moved to its own file.

  /** Successor Function --- Maps a set to its 'successor' in the sense required
    * for an inductive set.
    *
    * `successor: x ↦ x ∪ {x}`
    *
    * @param x set
    */
  val successor = DEF(λ(x, x ∪ singleton(x)))

  /** Inductive set --- A set is inductive if it contains the empty set, and the
    * [[successor]]s of each of its elements.
    *
    * `inductive(x) ⇔ (∅ ∈ x ⋀ ∀ y. y ∈ x ⇒ successor(y) ∈ x)`
    *
    * @param x set
    */
  val inductive = DEF(λ(x, (∅ ∈ x) /\ ∀(y, (y ∈ x) ==> (successor(y) ∈ x))))

  /** Theorem --- There exists an inductive set.
    *
    *    `∃ x. inductive(x)`
    *
    * Equivalent to the Axiom of Infinity ([[infinityAxiom]]). The proof shows
    * that the set obtained by the axiom of infinity is in fact inductive.
    */
  val inductiveSetExists = Theorem(
    ∃(x, inductive(x))
  ) {
    def S(y: Set) = ⋃(unorderedPair(y, unorderedPair(y, y)))
    def infinite(x: Set) = ∅ ∈ x /\ ∀(y, y ∈ x ==> S(y) ∈ x)

    have(y ∈ x ==> successor(y) ∈ x |- y ∈ x ==> successor(y) ∈ x) by Restate
    thenHave(y ∈ x ==> (y ∪ singleton(y)) ∈ x |- y ∈ x ==> successor(y) ∈ x) by Substitute(successor.definition of (x := y))
    thenHave(y ∈ x ==> (y ∪ unorderedPair(y, y)) ∈ x |- y ∈ x ==> successor(y) ∈ x) by Substitute(singleton.definition of (x := y))
    thenHave(y ∈ x ==> S(y) ∈ x |- y ∈ x ==> successor(y) ∈ x) by Substitute(∪.definition of (x := y, y := unorderedPair(y, y)))
    thenHave(∀(y, y ∈ x ==> S(y) ∈ x) |- y ∈ x ==> successor(y) ∈ x) by LeftForall
    thenHave(∀(y, y ∈ x ==> S(y) ∈ x) |- ∀(y, y ∈ x ==> successor(y) ∈ x)) by RightForall
    thenHave(infinite(x) |- inductive(x)) by Tautology.fromLastStep(inductive.definition)
    thenHave(infinite(x) |- ∃(x, inductive(x))) by RightExists
    thenHave(∃(x, infinite(x)) |- ∃(x, inductive(x))) by LeftExists

    have(thesis) by Cut(infinityAxiom, lastStep)
  }

  /*
  /**
   * Theorem --- Intersection of a non-empty Class is a Set
   *
   * There exists a set that is the intersection of all sets satisfying a given
   * formula. With classes, this means that the unary intersection of a class
   * defined by a predicate is a set.
   *
   *    `∃ x. P(x) ⊢ ∃ z. t ∈ z ⇔ ∀ x. P(x) ⇒ t ∈ x`
   */
  val intersectionOfPredicateClassExists = Theorem(
    ∃(x, P(x)) |- ∃(z, ∀(t, in(t, z) <=> ∀(y, P(y) ==> in(t, y))))
  ) {
    have(∃(z, ∀(t, in(t, z) <=> (in(t, x) /\ φ(t))))) by InstSchema(ScalaMap(z -> x))(comprehensionSchema)

    val conjunction = thenHave(∃(z, ∀(t, in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))))) by InstSchema(ScalaMap(φ -> lambda(t, ∀(y, P(y) ==> in(t, y)))))

    have(∀(y, P(y) ==> in(t, y)) |- ∀(y, P(y) ==> in(t, y))) by Hypothesis
    thenHave(∀(y, P(y) ==> in(t, y)) /\ P(x) |- ∀(y, P(y) ==> in(t, y))) by Weakening
    thenHave(∀(y, P(y) ==> in(t, y)) /\ P(x) |- P(x) ==> in(t, x)) by InstantiateForall(x)
    thenHave(∀(y, P(y) ==> in(t, y)) /\ P(x) |- in(t, x) /\ ∀(y, P(y) ==> in(t, y))) by Tautology
    val fwd = thenHave(P(x) |- ∀(y, P(y) ==> in(t, y)) ==> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))) by Restate

    have((in(t, x) /\ ∀(y, P(y) ==> in(t, y))) |- (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))) by Hypothesis
    val bwd = thenHave((in(t, x) /\ ∀(y, P(y) ==> in(t, y))) ==> (∀(y, P(y) ==> in(t, y)))) by Restate

    val lhs = have(P(x) |- ∀(y, P(y) ==> in(t, y)) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))) by RightIff(fwd, bwd)

    val form = formulaVariable
    have((in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))) |- in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))) by Hypothesis
    val rhs = thenHave(
      Set((in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))), (∀(y, P(y) ==> in(t, y)) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y))))) |- (in(t, z) <=> (∀(y, P(y) ==> in(t, y))))
    ) by RightSubstIff.withParametersSimple(List((∀(y, P(y) ==> in(t, y)), (in(t, x) /\ ∀(y, P(y) ==> in(t, y))))), lambda(form, in(t, z) <=> (form)))

    have((P(x), (in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y))))) |- in(t, z) <=> (∀(y, P(y) ==> in(t, y)))) by Cut(lhs, rhs)
    thenHave((P(x), ∀(t, (in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))))) |- in(t, z) <=> (∀(y, P(y) ==> in(t, y)))) by LeftForall
    thenHave((P(x), ∀(t, (in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))))) |- ∀(t, in(t, z) <=> (∀(y, P(y) ==> in(t, y))))) by RightForall
    thenHave((P(x), ∀(t, (in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y)))))) |- ∃(z, ∀(t, in(t, z) <=> (∀(y, P(y) ==> in(t, y)))))) by RightExists
    val cutRhs = thenHave((P(x), ∃(z, ∀(t, (in(t, z) <=> (in(t, x) /\ ∀(y, P(y) ==> in(t, y))))))) |- ∃(z, ∀(t, in(t, z) <=> (∀(y, P(y) ==> in(t, y)))))) by LeftExists

    have(P(x) |- ∃(z, ∀(t, in(t, z) <=> (∀(y, P(y) ==> in(t, y)))))) by Cut(conjunction, cutRhs)
    thenHave(∃(x, P(x)) |- ∃(z, ∀(t, in(t, z) <=> (∀(y, P(y) ==> in(t, y)))))) by LeftExists

  }


    val xSecond = have(() |- (cartesianProduct(emptySet, x) === emptySet)) subproof {
      have(
        forall(t, in(t, cartesianProduct(emptySet, y)) <=> (in(t, powerSet(powerSet(setUnion(emptySet, y)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, emptySet) /\ in(b, y)))))
      ) by InstantiateForall(cartesianProduct(emptySet, y))(cartesianProduct.definition of (x -> emptySet))
      val impl = thenHave(
        in(t, cartesianProduct(emptySet, y)) <=> (in(t, powerSet(powerSet(setUnion(emptySet, y)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, emptySet) /\ in(b, y))))
      ) by InstantiateForall(t)

      val elemEmpty = have(in(t, emptySet) <=> (in(t, powerSet(powerSet(setUnion(emptySet, y)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, emptySet) /\ in(b, y))))) subproof {
        val lhs = have(in(t, emptySet) |- (in(t, powerSet(powerSet(setUnion(emptySet, y)))) /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, emptySet) /\ in(b, y))))) by Weakening(
          emptySet.definition of (x -> t)
        )

        have((t === pair(a, b)) /\ in(a, emptySet) /\ in(b, y) |- in(t, emptySet)) by Weakening(emptySet.definition of (x -> a))
        thenHave(exists(b, (t === pair(a, b)) /\ in(a, emptySet) /\ in(b, y)) |- in(t, emptySet)) by LeftExists
        thenHave(exists(a, exists(b, (t === pair(a, b)) /\ in(a, emptySet) /\ in(b, y))) |- in(t, emptySet)) by LeftExists
        val rhs = thenHave(in(t, powerSet(powerSet(setUnion(emptySet, y)))) /\ exists(a, exists(b, (t === pair(a, b)) /\ in(a, emptySet) /\ in(b, y))) |- in(t, emptySet)) by Weakening

        have(thesis) by Tautology.from(lhs, rhs)
      }

      have(in(t, cartesianProduct(emptySet, y)) <=> in(t, emptySet)) by Tautology.from(impl, elemEmpty)
      val ext = thenHave(forall(t, in(t, cartesianProduct(emptySet, y)) <=> in(t, emptySet))) by RightForall

      have(thesis) by Tautology.from(ext of (y -> x), extensionalityAxiom of (x -> cartesianProduct(emptySet, x), y -> emptySet))
    }

    have(thesis) by RightAnd(xFirst, xSecond)
  }


  /**
   * Theorem --- If `r` is a relation, then `r` is a relation between its domain and its range.
   */
  val relationImpliesRelationBetweenDomainAndRange = Theorem(
    relation(r) |- relationBetween(r, relationDomain(r), relationRange(r))
  ) {
    // Lay out the definitions to apply them later
    have(∀(t, in(t, relationDomain(r)) <=> ∃(b, in(pair(t, b), r)))) by Definition(relationDomain, relationDomainUniqueness)(r)
    val relationDomainDef = thenHave(in(t, relationDomain(r)) <=> ∃(b, in(pair(t, b), r))) by InstantiateForall(t)

    have(∀(t, in(t, relationRange(r)) <=> ∃(a, in(pair(a, t), r)))) by Definition(relationRange, relationRangeUniqueness)(r)
    val relationRangeDef = thenHave(in(t, relationRange(r)) <=> ∃(a, in(pair(a, t), r))) by InstantiateForall(t)

    // Start the proof
    have(relation(r) |- ∃(x, ∃(y, relationBetween(r, x, y)))) by Tautology.from(relation.definition)

    have(relationBetween(r, x, y) |- subset(r, cartesianProduct(x, y))) by Tautology.from(relationBetween.definition of (a -> x, b -> y))
    have(relationBetween(r, x, y) |- ∀(t, in(t, r) ==> in(t, cartesianProduct(x, y)))) by Tautology.from(
      lastStep,
      subset.definition of (x -> r, y -> cartesianProduct(x, y))
    )
    thenHave(relationBetween(r, x, y) |- in(t, r) ==> in(t, cartesianProduct(x, y))) by InstantiateForall(t)
    thenHave((relationBetween(r, x, y), in(t, r)) |- in(t, cartesianProduct(x, y))) by Restate

    // Apply the definition of the cartesian product
    val relationDef = have((relationBetween(r, x, y), in(t, r)) |- ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y)))) by Tautology.from(
      lastStep,
      elemOfCartesianProduct
    )

    // Show that x ⊇ relationDomain(r) and y ⊇ relationRange(r)
    val memberships = have((in(t, r), (t === pair(a, b))) |- in(a, relationDomain(r)) /\ in(b, relationRange(r))) subproof {
      have(in(t, r) |- in(t, r)) by Hypothesis
      val membership = thenHave((in(t, r), (t === pair(a, b))) |- in(pair(a, b), r)) by Substitution.ApplyRules(t === pair(a, b))

      assume(in(t, r))
      assume(t === pair(a, b))
      have(∃(b, in(pair(a, b), r))) by RightExists(membership)
      val left = have(in(a, relationDomain(r))) by Tautology.from(lastStep, relationDomainDef of (t -> a))

      have(∃(a, in(pair(a, b), r))) by RightExists(membership)
      val right = have(in(b, relationRange(r))) by Tautology.from(lastStep, relationRangeDef of (t -> b))

      have(thesis) by RightAnd(left, right)
    }

    // We can now reconstruct the definition of relationBetween(r, relationDomain(r), relationRange(r))
    have((t === pair(a, b)) |- (t === pair(a, b))) by Hypothesis
    val toCut = have((in(t, r), (t === pair(a, b))) |- (t === pair(a, b)) /\ in(a, relationDomain(r)) /\ in(b, relationRange(r))) by RightAnd(lastStep, memberships)

    have((t === pair(a, b)) /\ in(a, x) /\ in(b, y) |- (t === pair(a, b))) by Tautology
    have((in(t, r), (t === pair(a, b)) /\ in(a, x) /\ in(b, y)) |- (t === pair(a, b)) /\ in(a, relationDomain(r)) /\ in(b, relationRange(r))) by Cut(lastStep, toCut)

    // Re-add the existential quantifiers
    thenHave((in(t, r), (t === pair(a, b)) /\ in(a, x) /\ in(b, y)) |- ∃(b, (t === pair(a, b)) /\ in(a, relationDomain(r)) /\ in(b, relationRange(r)))) by RightExists
    thenHave((in(t, r), (t === pair(a, b)) /\ in(a, x) /\ in(b, y)) |- ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, relationDomain(r)) /\ in(b, relationRange(r))))) by RightExists
    thenHave((in(t, r), ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y))) |- ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, relationDomain(r)) /\ in(b, relationRange(r))))) by LeftExists
    thenHave((in(t, r), ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y)))) |- ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, relationDomain(r)) /\ in(b, relationRange(r))))) by LeftExists

    // Cut and rewrap the definition
    have((in(t, r), relationBetween(r, x, y)) |- ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, relationDomain(r)) /\ in(b, relationRange(r))))) by Cut(
      relationDef,
      lastStep
    )
    have((in(t, r), relationBetween(r, x, y)) |- in(t, cartesianProduct(relationDomain(r), relationRange(r)))) by Tautology.from(
      lastStep,
      elemOfCartesianProduct of (x -> relationDomain(r), y -> relationRange(r))
    )
    thenHave(relationBetween(r, x, y) |- in(t, r) ==> in(t, cartesianProduct(relationDomain(r), relationRange(r)))) by Restate
    thenHave(relationBetween(r, x, y) |- ∀(t, in(t, r) ==> in(t, cartesianProduct(relationDomain(r), relationRange(r))))) by RightForall
    have(relationBetween(r, x, y) |- subset(r, cartesianProduct(relationDomain(r), relationRange(r)))) by Tautology.from(
      lastStep,
      subset.definition of (x -> r, y -> cartesianProduct(relationDomain(r), relationRange(r)))
    )
    have(relationBetween(r, x, y) |- relationBetween(r, relationDomain(r), relationRange(r))) by Tautology.from(
      lastStep,
      relationBetween.definition of (a -> relationDomain(r), b -> relationRange(r))
    )

    // Add the existential quantifier to finish the proofs
    thenHave(∃(y, relationBetween(r, x, y)) |- relationBetween(r, relationDomain(r), relationRange(r))) by LeftExists
    thenHave(∃(x, ∃(y, relationBetween(r, x, y))) |- relationBetween(r, relationDomain(r), relationRange(r))) by LeftExists

    have(thesis) by Tautology.from(lastStep, relation.definition)
  }


  /**
   * Theorem --- the union of two relations is a relation, with domains and codomains
   * unions of the constituents.
   *
   * Effectively,
   *
   *    `f ⊆ a * b; g ⊆ c * d ⊢ (f ∪ g) ⊆ (a ∪ c) * (b ∪ d)`
   */
  val unionOfTwoRelationsWithField = Theorem(
    relationBetween(f, a, b) /\ relationBetween(g, c, d) |- relationBetween(setUnion(f, g), setUnion(a, c), setUnion(b, d))
  ) {
    val fab = have(relationBetween(f, a, b) <=> subset(f, cartesianProduct(a, b))) by Restate.from(relationBetween.definition of r -> f)
    val gcd = fab of (f -> g, a -> c, b -> d)
    val fug = fab of (f -> setUnion(f, g), a -> setUnion(a, c), b -> setUnion(b, d))

    have(subset(f, cartesianProduct(a, b)) /\ subset(g, cartesianProduct(c, d)) |- subset(setUnion(f, g), cartesianProduct(setUnion(a, c), setUnion(b, d)))) by Tautology.from(
      unionOfCartesianProducts,
      unionOfSubsetsOfDifferentSets of (a -> f, b -> g, c -> cartesianProduct(a, b), d -> cartesianProduct(c, d)),
      subsetTransitivity of (a -> setUnion(f, g), b -> setUnion(cartesianProduct(a, b), cartesianProduct(c, d)), c -> cartesianProduct(setUnion(a, c), setUnion(b, d)))
    )

    have(thesis) by Tautology.from(lastStep, fab, gcd, fug)
  }

  /**
   * Theorem --- the union of two relations is a relation. (weaker form)
   *
   * Weakening of [[unionOfTwoRelationsWithField]] to unknown fields.
   */
  val unionOfTwoRelations = Theorem(
    relation(f) /\ relation(g) |- relation(setUnion(f, g))
  ) {
    val relf = have(relation(f) <=> exists(x, exists(y, relationBetween(f, x, y)))) by Restate.from(relation.definition of r -> f)
    val relg = relf of f -> g
    val relfug = relf of f -> setUnion(f, g)

    have((relationBetween(f, a, b), relationBetween(g, c, d)) |- relationBetween(setUnion(f, g), setUnion(a, c), setUnion(b, d))) by Restate.from(unionOfTwoRelationsWithField)
    thenHave((relationBetween(f, a, b), relationBetween(g, c, d)) |- exists(y, relationBetween(setUnion(f, g), setUnion(a, c), y))) by RightExists
    thenHave((relationBetween(f, a, b), relationBetween(g, c, d)) |- exists(x, exists(y, relationBetween(setUnion(f, g), x, y)))) by RightExists
    thenHave((relationBetween(f, a, b), exists(d, relationBetween(g, c, d))) |- exists(x, exists(y, relationBetween(setUnion(f, g), x, y)))) by LeftExists
    thenHave((relationBetween(f, a, b), exists(c, exists(d, relationBetween(g, c, d)))) |- exists(x, exists(y, relationBetween(setUnion(f, g), x, y)))) by LeftExists
    thenHave((exists(b, relationBetween(f, a, b)), exists(c, exists(d, relationBetween(g, c, d)))) |- exists(x, exists(y, relationBetween(setUnion(f, g), x, y)))) by LeftExists
    thenHave((exists(a, exists(b, relationBetween(f, a, b))), exists(c, exists(d, relationBetween(g, c, d)))) |- exists(x, exists(y, relationBetween(setUnion(f, g), x, y)))) by LeftExists

    thenHave((relation(f), relation(g)) |- relation(setUnion(f, g))) by Substitution.ApplyRules(relf, relg, relfug)
  }

  // TODO: any subset of a functional is functional
  // TODO: a functional over something restricted to x is still functional


  /**
   * Theorem --- a set containing only pairs is a relation, and vice versa.
   *
   *    `(\forall t \in z. \exists a, b. t = (a, b)) <=> relation(z)`
   *
   * The domain and codomain of this relation can be obtained constructively by applying
   * the [[replacementSchema]] with the [[firstInPair]] and [[secondInPair]] projection
   * functions.
   *
   * Here, it is sufficient to deal with them abstractly through the definitions of
   * [[relationDomain]] and [[relationRange]].
   */
  val setOfPairsIsRelation = Theorem(
    forall(t, in(t, z) ==> exists(a, exists(b, (t === pair(a, b))))) <=> relation(z)
  ) {
    // if the set contains only pairs, it is a relation
    val fwd = have(forall(t, in(t, z) ==> exists(a, exists(b, (t === pair(a, b))))) ==> relation(z)) subproof {
      val dom = relationDomain(z)
      val ran = relationRange(z)

      val inst = have(forall(t, in(t, z) ==> exists(a, exists(b, (t === pair(a, b))))) |- (in(t, z) ==> exists(a, exists(b, (t === pair(a, b)))))) by InstantiateForall

      // unfold defs
      have(forall(t, in(t, dom) <=> exists(a, in(pair(t, a), z)))) by InstantiateForall(dom)(relationDomain.definition of r -> z)
      val inDom = thenHave((in(a, dom) <=> exists(b, in(pair(a, b), z)))) by InstantiateForall(a)
      have(forall(t, in(t, ran) <=> exists(a, in(pair(a, t), z)))) by InstantiateForall(ran)(relationRange.definition of r -> z)
      val inRan = thenHave((in(b, ran) <=> exists(a, in(pair(a, b), z)))) by InstantiateForall(b)

      have((in(t, z)) |- in(t, z)) by Restate
      val abz = thenHave((in(t, z), (t === pair(a, b))) |- in(pair(a, b), z)) by Substitution.ApplyRules(t === pair(a, b))

      val exa = have((in(t, z), (t === pair(a, b))) |- exists(a, in(pair(a, b), z))) by RightExists(abz)
      val exb = have((in(t, z), (t === pair(a, b))) |- exists(b, in(pair(a, b), z))) by RightExists(abz)

      have((in(t, z), (t === pair(a, b))) |- (t === pair(a, b)) /\ in(a, dom) /\ in(b, ran)) by Tautology.from(exa, exb, inDom, inRan)
      thenHave((in(t, z), (t === pair(a, b))) |- exists(b, (t === pair(a, b)) /\ in(a, dom) /\ in(b, ran))) by RightExists
      thenHave((in(t, z), (t === pair(a, b))) |- exists(a, exists(b, (t === pair(a, b)) /\ in(a, dom) /\ in(b, ran)))) by RightExists

      have((in(t, z), (t === pair(a, b))) |- in(t, cartesianProduct(dom, ran))) by Tautology.from(lastStep, elemOfCartesianProduct of (x -> dom, y -> ran))
      thenHave((in(t, z), exists(b, t === pair(a, b))) |- in(t, cartesianProduct(dom, ran))) by LeftExists
      thenHave((in(t, z), exists(a, exists(b, t === pair(a, b)))) |- in(t, cartesianProduct(dom, ran))) by LeftExists

      have(forall(t, in(t, z) ==> exists(a, exists(b, (t === pair(a, b))))) |- in(t, z) ==> in(t, cartesianProduct(dom, ran))) by Tautology.from(lastStep, inst)
      thenHave(forall(t, in(t, z) ==> exists(a, exists(b, (t === pair(a, b))))) |- forall(t, in(t, z) ==> in(t, cartesianProduct(dom, ran)))) by RightForall

      have(forall(t, in(t, z) ==> exists(a, exists(b, (t === pair(a, b))))) |- relationBetween(z, dom, ran)) by Tautology.from(
        lastStep,
        subsetAxiom of (x -> z, y -> cartesianProduct(dom, ran)),
        relationBetween.definition of (r -> z, a -> dom, b -> ran)
      )
      thenHave(forall(t, in(t, z) ==> exists(a, exists(b, (t === pair(a, b))))) |- exists(b, relationBetween(z, dom, b))) by RightExists
      thenHave(forall(t, in(t, z) ==> exists(a, exists(b, (t === pair(a, b))))) |- exists(a, exists(b, relationBetween(z, a, b)))) by RightExists

      have(thesis) by Tautology.from(lastStep, relation.definition of r -> z)
    }

    // if the set is a relation, it contains only pairs
    val bwd = have(relation(z) ==> forall(t, in(t, z) ==> exists(a, exists(b, (t === pair(a, b)))))) subproof {
      have(subset(z, cartesianProduct(c, d)) |- forall(t, in(t, z) ==> in(t, cartesianProduct(c, d)))) by Weakening(subsetAxiom of (x -> z, y -> cartesianProduct(c, d)))
      val tz = thenHave(subset(z, cartesianProduct(c, d)) |- (in(t, z) ==> in(t, cartesianProduct(c, d)))) by InstantiateForall(t)

      have(in(t, cartesianProduct(c, d)) |- exists(a, exists(b, (t === pair(a, b))))) subproof {
        have(((t === pair(a, b)) /\ in(a, c) /\ in(a, b)) ==> (t === pair(a, b))) by Restate
        thenHave(forall(b, ((t === pair(a, b)) /\ in(a, c) /\ in(a, b)) ==> (t === pair(a, b)))) by RightForall
        have(exists(b, ((t === pair(a, b)) /\ in(a, c) /\ in(a, b))) ==> exists(b, (t === pair(a, b)))) by Cut(
          lastStep,
          existentialImplicationDistribution of (P -> lambda(b, ((t === pair(a, b)) /\ in(a, c) /\ in(a, b))), Q -> lambda(b, (t === pair(a, b))))
        )
        thenHave(forall(a, exists(b, ((t === pair(a, b)) /\ in(a, c) /\ in(a, b))) ==> exists(b, (t === pair(a, b))))) by RightForall
        val elemCart = have(exists(a, exists(b, ((t === pair(a, b)) /\ in(a, c) /\ in(a, b)))) ==> exists(a, exists(b, (t === pair(a, b))))) by Cut(
          lastStep,
          existentialImplicationDistribution of (P -> lambda(a, exists(b, (t === pair(a, b)) /\ in(a, c) /\ in(a, b))), Q -> lambda(a, exists(b, t === pair(a, b))))
        )

        // TODO: Tautology bug
        have(thesis) by Tautology.from(lastStep, elemOfCartesianProduct of (x -> c, y -> d, z -> t))
      }

      have(relationBetween(z, c, d) |- in(t, z) ==> exists(a, exists(b, (t === pair(a, b))))) by Tautology.from(lastStep, tz, relationBetween.definition of (r -> z, a -> c, b -> d))
      thenHave(exists(d, relationBetween(z, c, d)) |- in(t, z) ==> exists(a, exists(b, (t === pair(a, b))))) by LeftExists
      thenHave(exists(c, exists(d, relationBetween(z, c, d))) |- in(t, z) ==> exists(a, exists(b, (t === pair(a, b))))) by LeftExists

      have(relation(z) |- in(t, z) ==> exists(a, exists(b, (t === pair(a, b))))) by Tautology.from(lastStep, relation.definition of r -> z)
      thenHave(relation(z) |- forall(t, in(t, z) ==> exists(a, exists(b, (t === pair(a, b)))))) by RightForall
      thenHave(thesis) by Restate
    }

    have(thesis) by Tautology.from(fwd, bwd)
  }

   */
}
