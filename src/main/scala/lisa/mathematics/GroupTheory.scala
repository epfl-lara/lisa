package lisa.mathematics

import lisa.automation.kernel.CommonTactics.Cases
import lisa.automation.kernel.CommonTactics.Definition
import lisa.automation.kernel.CommonTactics.Equalities
import lisa.automation.kernel.CommonTactics.ExistenceAndUniqueness
import lisa.automation.kernel.OLPropositionalSolver.Tautology
import lisa.automation.settheory.SetTheoryTactics.UniqueComprehension
import lisa.kernel.proof.SequentCalculus.Hypothesis
import lisa.mathematics.FirstOrderLogic.equalityTransitivity
import lisa.mathematics.FirstOrderLogic.existsOneImpliesExists
import lisa.mathematics.FirstOrderLogic.substitutionInUniquenessQuantifier
import lisa.mathematics.SetTheory.*

/**
 * Group theory, developed following Chapter 2 of S. Lang "Undergraduate Algebra".
 *
 * Book : [[https://link.springer.com/book/10.1007/978-1-4684-9234-7]]
 */
object GroupTheory extends lisa.Main {
  // Groups
  private val G, H = variable

  // Group laws
  private val * = variable

  // Group elements
  private val a, b, c, d = variable
  private val x, y, z = variable
  private val t, u, v, w = variable

  // Identity elements
  private val e, f = variable

  // Predicates
  private val P, Q = predicate(1)

  //
  // 0. Notation
  //

  /**
   * Defines the element that is uniquely given by the uniqueness theorem, or falls back to the error element if the
   * assumptions of the theorem are not satisfied.
   *
   * This is useful in defining specific elements in groups, where their uniqueness (and existence) strongly rely
   * on the assumption of the group structure.
   */
  def TheConditional(u: VariableLabel, f: Formula)(just: runningSetTheory.Theorem, defaultValue: Term = ∅): The = {
    val seq = just.proposition

    if (seq.left.isEmpty) {
      The(u, f)(just)
    } else {
      val prem = if (seq.left.size == 1) seq.left.head else And(seq.left.toSeq: _*)
      val completeDef = (prem ==> f) /\ (!prem ==> (u === defaultValue))
      val substF = substituteVariables(completeDef, Map[VariableLabel, Term](u -> defaultValue), Seq())
      val substDef = substituteVariables(completeDef, Map[VariableLabel, Term](u -> v), Seq())

      val completeUniquenessTheorem = Lemma(
        ∃!(u, completeDef)
      ) {
        val case1 = have(prem |- ∃!(u, completeDef)) subproof {
          // We prove the equivalence f <=> completeDef so that we can substitute it in the uniqueness quantifier
          val equiv = have(prem |- ∀(u, f <=> completeDef)) subproof {
            have(f |- f) by Hypothesis
            thenHave((prem, f) |- f) by Weakening
            val left = thenHave(f |- (prem ==> f)) by Restate

            have(prem |- prem) by Hypothesis
            thenHave((prem, !prem) |- ()) by LeftNot
            thenHave((prem, !prem) |- (u === defaultValue)) by Weakening
            val right = thenHave(prem |- (!prem ==> (u === defaultValue))) by Restate

            have((prem, f) |- completeDef) by RightAnd(left, right)
            val forward = thenHave(prem |- f ==> completeDef) by Restate

            have(completeDef |- completeDef) by Hypothesis
            thenHave((prem, completeDef) |- completeDef) by Weakening
            thenHave((prem, completeDef) |- f) by Tautology
            val backward = thenHave(prem |- completeDef ==> f) by Restate

            have(prem |- f <=> completeDef) by RightIff(forward, backward)
            thenHave(thesis) by RightForall
          }

          val substitution = have((∃!(u, f), ∀(u, f <=> completeDef)) |- ∃!(u, completeDef)) by Restate.from(
            substitutionInUniquenessQuantifier of (P -> lambda(u, f), Q -> lambda(u, completeDef))
          )

          val implication = have((prem, ∃!(u, f)) |- ∃!(u, completeDef)) by Cut(equiv, substitution)
          val uniqueness = have(prem |- ∃!(u, f)) by Restate.from(just)
          have(prem |- ∃!(u, completeDef)) by Cut(uniqueness, implication)
        }

        val case2 = have(!prem |- ∃!(u, completeDef)) subproof {
          val existence = have(!prem |- ∃(u, completeDef)) subproof {
            have(!prem |- !prem) by Hypothesis
            thenHave((prem, !prem) |- ()) by LeftNot
            thenHave((prem, !prem) |- substF) by Weakening
            val left = thenHave(!prem |- (prem ==> substF)) by Restate

            have(defaultValue === defaultValue) by RightRefl
            thenHave(!prem |- defaultValue === defaultValue) by Weakening
            val right = thenHave(!prem ==> (defaultValue === defaultValue)) by Restate

            have(!prem |- (prem ==> substF) /\ (!prem ==> (defaultValue === defaultValue))) by RightAnd(left, right)
            thenHave(thesis) by RightExists.withParameters(defaultValue)
          }

          val uniqueness = have((!prem, completeDef, substDef) |- (u === v)) subproof {
            assume(!prem)
            assume(completeDef)
            assume(substDef)

            val eq1 = have(u === defaultValue) by Tautology
            val eq2 = have(defaultValue === v) by Tautology
            val p = have((u === defaultValue) /\ (defaultValue === v)) by RightAnd(eq1, eq2)

            val transitivity = equalityTransitivity of (x -> u, y -> defaultValue, z -> v)
            have(thesis) by Cut(p, transitivity)
          }

          have(thesis) by ExistenceAndUniqueness(completeDef)(existence, uniqueness)
        }

        have(thesis) by Cases(case1, case2)
      }

      The(u, completeDef)(completeUniquenessTheorem)
    }
  }

  //
  // 1. Basic definitions and results
  //

  /**
   * Binary operation --- `*` is a binary operation on `G` if it associates to each pair of elements of `G`
   * a unique element in `G`. In other words, `*` is a function `G × G -> G`.
   */
  val binaryOperation = DEF(G, *) --> functionFrom(*, cartesianProduct(G, G), G)

  /**
   * Short-hand alias for `x * y`.
   */
  inline def op(x: Term, * : Term, y: Term) = app(*, pair(x, y))

  /**
   * Associativity --- `*` is associative (in `G`) if `(x * y) * z = x * (y * z)` for all `x, y, z` in `G`.
   */
  val associativityAxiom = DEF(G, *) -->
    ∀(x, x ∈ G ==> ∀(y, y ∈ G ==> ∀(z, z ∈ G ==> (op(op(x, *, y), *, z) === op(x, *, op(y, *, z))))))

  /**
   * Neutral element --- We say that an element `e` in `G` is neutral if `e * x = x * e = x` for all `x` in `G`.
   */
  val isNeutral = DEF(e, G, *) --> (e ∈ G /\ ∀(x, (x ∈ G) ==> ((op(e, *, x) === x) /\ (op(x, *, e) === x))))

  /**
   * Identity existence --- There exists a neutral element `e` in `G`.
   */
  val identityExistence = DEF(G, *) --> ∃(e, isNeutral(e, G, *))

  /**
   * Inverse element --- `y` is called an inverse of `x` if `x * y = y * x = e`.
   */
  val isInverse = DEF(y, x, G, *) --> (y ∈ G) /\ isNeutral(op(x, *, y), G, *) /\ isNeutral(op(y, *, x), G, *)

  /**
   * Inverse existence --- For all `x` in G, there exists an element `y` in G such that `x * y = y * x = e`.
   */
  val inverseExistence = DEF(G, *) --> ∀(x, (x ∈ G) ==> ∃(y, isInverse(y, x, G, *)))

  /**
   * Group --- A group (G, *) is a set along with a law of composition `*`, satisfying [[associativityAxiom]], [[identityExistence]]
   * and [[inverseExistence]].
   */
  val group = DEF(G, *) --> binaryOperation(G, *) /\ associativityAxiom(G, *) /\ identityExistence(G, *) /\ inverseExistence(G, *)

  /**
   * Commutativity --- `*` is said to be commutative on `G` if `x * y = y * x` for all `x, y ∈ G`.
   */
  val commutativityAxiom = DEF(G, *) --> ∀(x, x ∈ G ==> ∀(y, y ∈ G ==> (op(x, *, y) === op(y, *, x))))

  /**
   * Abelian group --- A group is said to be <emph>abelian</emph> (or commutative) if every element commutes,
   * i.e. it satisfies [[commutativityAxiom]].
   */
  val abelianGroup = DEF(G, *) --> group(G, *) /\ commutativityAxiom(G, *)

  /**
   * Alias for abelian group.
   */
  val commutativeGroup = abelianGroup

  /**
   * Lemma --- For elements `x, y, z` in a group `(G, *)`, we have `(xy)z = x(yz)`.
   *
   * Practical reformulation of the [[associativityAxiom]].
   */
  val associativity = Lemma(
    (group(G, *), x ∈ G, y ∈ G, z ∈ G) |- op(op(x, *, y), *, z) === op(x, *, op(y, *, z))
  ) {
    assume(group(G, *))

    have(∀(x, x ∈ G ==> ∀(y, y ∈ G ==> ∀(z, z ∈ G ==> (op(op(x, *, y), *, z) === op(x, *, op(y, *, z))))))) by Tautology.from(
      group.definition,
      associativityAxiom.definition
    )
    thenHave(x ∈ G ==> ∀(y, y ∈ G ==> ∀(z, z ∈ G ==> (op(op(x, *, y), *, z) === op(x, *, op(y, *, z)))))) by InstantiateForall(x)
    thenHave(x ∈ G |- ∀(y, y ∈ G ==> ∀(z, z ∈ G ==> (op(op(x, *, y), *, z) === op(x, *, op(y, *, z)))))) by Restate
    thenHave(x ∈ G |- y ∈ G ==> ∀(z, z ∈ G ==> (op(op(x, *, y), *, z) === op(x, *, op(y, *, z))))) by InstantiateForall(y)
    thenHave((x ∈ G, y ∈ G) |- ∀(z, z ∈ G ==> (op(op(x, *, y), *, z) === op(x, *, op(y, *, z))))) by Restate
    thenHave((x ∈ G, y ∈ G) |- z ∈ G ==> (op(op(x, *, y), *, z) === op(x, *, op(y, *, z)))) by InstantiateForall(z)
    thenHave((x ∈ G, y ∈ G, z ∈ G) |- (op(op(x, *, y), *, z) === op(x, *, op(y, *, z)))) by Restate
  }

  /**
   * Lemma --- For elements `x, y` in an abelian group `(G, *)`, we have `xy = yx`.
   *
   * Practical reformulation of [[commutativityAxiom]].
   */
  val commutativity = Lemma(
    (abelianGroup(G, *), x ∈ G, y ∈ G) |- op(x, *, y) === op(y, *, x)
  ) {
    assume(abelianGroup(G, *))

    have(∀(x, x ∈ G ==> ∀(y, y ∈ G ==> (op(x, *, y) === op(y, *, x))))) by Tautology.from(
      abelianGroup.definition,
      commutativityAxiom.definition
    )
    thenHave(x ∈ G ==> ∀(y, y ∈ G ==> (op(x, *, y) === op(y, *, x)))) by InstantiateForall(x)
    thenHave(x ∈ G |- ∀(y, y ∈ G ==> (op(x, *, y) === op(y, *, x)))) by Restate
    thenHave(x ∈ G |- (y ∈ G ==> (op(x, *, y) === op(y, *, x)))) by InstantiateForall(y)
    thenHave((x ∈ G, y ∈ G) |- ((op(x, *, y) === op(y, *, x)))) by Restate
  }

  /**
   * Group operation is functional -- The group operation `*` is functional.
   */
  val groupOperationIsFunctional = Lemma(
    group(G, *) |- functional(*)
  ) {
    have(thesis) by Tautology.from(
      group.definition,
      binaryOperation.definition,
      functionFromImpliesFunctional of (f -> *, x -> cartesianProduct(G, G), y -> G)
    )
  }

  /**
   * Group operation domain -- The domain of a group law is the cartesian product of the group `G` with itself.
   *
   * Follows directly from the definition of `binaryRelation`.
   */
  val groupOperationDomain = Lemma(
    group(G, *) |- relationDomain(*) === cartesianProduct(G, G)
  ) {
    have(thesis) by Tautology.from(
      group.definition,
      binaryOperation.definition,
      functionFromImpliesDomainEq of (f -> *, x -> cartesianProduct(G, G), y -> G)
    )
  }

  /**
   * Lemma --- If `x` and `y` are two elements of the group, the pair `(x, y)` is in the relation domain of `*.
   */
  val groupPairInOperationDomain = Lemma(
    (group(G, *), x ∈ G, y ∈ G) |- pair(x, y) ∈ relationDomain(*)
  ) {
    assume(group(G, *))
    assume(x ∈ G)
    assume(y ∈ G)

    have(x ∈ G /\ y ∈ G) by Tautology
    have(pair(x, y) ∈ cartesianProduct(G, G)) by Tautology.from(
      lastStep,
      pairInCartesianProduct of (a -> x, b -> y, x -> G, y -> G)
    )
    thenHave((relationDomain(*) === cartesianProduct(G, G)) |- pair(x, y) ∈ relationDomain(*)) by RightSubstEq(
      List((relationDomain(*), cartesianProduct(G, G))),
      lambda(z, pair(x, y) ∈ z)
    )

    have(thesis) by Cut(groupOperationDomain, lastStep)
  }

  /**
   * Lemma --- If `x, y ∈ G`, then `x * y ∈ G`.
   */
  val groupIsClosedByProduct = Lemma(
    (group(G, *), x ∈ G, y ∈ G) |- op(x, *, y) ∈ G
  ) {
    have(∀(t, (t ∈ relationRange(*)) <=> ∃(a, pair(a, t) ∈ *))) by Definition(relationRange, relationRangeUniqueness)(*)
    val relationRangeDef = thenHave((op(x, *, y) ∈ relationRange(*)) <=> ∃(a, pair(a, op(x, *, y)) ∈ *)) by InstantiateForall(op(x, *, y))

    val appDef = have(
      (functional(*), pair(x, y) ∈ relationDomain(*)) |- pair(pair(x, y), op(x, *, y)) ∈ *
    ) by Definition(app, functionApplicationUniqueness)(*, pair(x, y))

    assume(group(G, *))
    assume(x ∈ G)
    assume(y ∈ G)

    // Show that x * y is in relation range
    have(pair(pair(x, y), op(x, *, y)) ∈ *) by Tautology.from(
      appDef,
      groupOperationIsFunctional,
      groupPairInOperationDomain
    )
    thenHave(∃(a, pair(a, op(x, *, y)) ∈ *)) by RightExists

    val productInRelationRange = have(op(x, *, y) ∈ relationRange(*)) by Tautology.from(lastStep, relationRangeDef)

    // Conclude by [[functionImpliesRangeSubsetOfCodomain]]
    have(∀(t, t ∈ relationRange(*) ==> t ∈ G)) by Tautology.from(
      group.definition,
      binaryOperation.definition,
      functionImpliesRangeSubsetOfCodomain of (f -> *, x -> cartesianProduct(G, G), y -> G),
      subset.definition of (x -> relationRange(*), y -> G)
    )
    thenHave(op(x, *, y) ∈ relationRange(*) ==> op(x, *, y) ∈ G) by InstantiateForall(op(x, *, y))
    thenHave(op(x, *, y) ∈ relationRange(*) |- op(x, *, y) ∈ G) by Restate

    have(thesis) by Cut(productInRelationRange, lastStep)
  }

  /**
   * Identity uniqueness --- In a group (G, *), an identity element is unique, i.e. if both `e * x = x * e = x` and
   * `f * x = x * f = x` for all `x`, then `e = f`.
   *
   * This justifies calling `e` <i>the</i> identity element.
   */
  val identityUniqueness = Theorem(
    group(G, *) |- ∃!(e, isNeutral(e, G, *))
  ) {
    val existence = have(group(G, *) |- ∃(e, isNeutral(e, G, *))) by Tautology.from(group.definition, identityExistence.definition)

    // We prove that if e and f are neutral elements then ef = f = e, where the first equality comes from e's left neutrality,
    // and the second equality from f's right neutrality
    val uniqueness = have((isNeutral(e, G, *), isNeutral(f, G, *)) |- (e === f)) subproof {
      // We prove that neutral elements are elements of G, such that * can be applied.
      val membership = have(isNeutral(e, G, *) |- e ∈ G) by Tautology.from(isNeutral.definition)

      assume(isNeutral(e, G, *))
      assume(isNeutral(f, G, *))

      // 1. ef = f
      have(∀(x, x ∈ G ==> ((op(e, *, x) === x) /\ (op(x, *, e) === x)))) by Tautology.from(isNeutral.definition)
      thenHave(f ∈ G ==> ((op(e, *, f) === f) /\ (op(f, *, e) === f))) by InstantiateForall(f)
      val neutrality = thenHave(f ∈ G |- ((op(e, *, f) === f) /\ (op(f, *, e) === f))) by Restate

      have((op(e, *, f) === f) /\ (op(f, *, e) === f)) by Cut(membership of (e -> f), neutrality)
      val firstEq = thenHave(op(e, *, f) === f) by Tautology

      // 2. ef = e
      have((op(f, *, e) === e) /\ (op(e, *, f) === e)) by Cut(membership of (e -> e), neutrality of (e -> f, f -> e))
      val secondEq = thenHave(e === op(e, *, f)) by Tautology

      // 3. Conclude by transitivity
      have(e === f) by Equalities(firstEq, secondEq)
    }

    have(group(G, *) |- ∃!(e, isNeutral(e, G, *))) by ExistenceAndUniqueness(isNeutral(e, G, *))(existence, uniqueness)
  }

  /**
   * Defines the identity element of `(G, *)`.
   */
  val identity = DEF(G, *) --> TheConditional(e, isNeutral(e, G, *))(identityUniqueness)

  /**
   * Lemma --- The identity element is neutral by definition.
   */
  private val identityIsNeutral = Lemma(
    group(G, *) |- isNeutral(identity(G, *), G, *)
  ) {
    have(thesis) by Definition(identity, identityUniqueness)(G, *)
  }

  /**
   * Lemma --- For any element `x` in a group `(G, *)`, we have `x * e = e * x = x`.
   *
   * Practical reformulation of [[identityIsNeutral]].
   */
  val identityNeutrality = Lemma(
    (group(G, *), x ∈ G) |- (op(identity(G, *), *, x) === x) /\ (op(x, *, identity(G, *)) === x)
  ) {
    have(group(G, *) |- ∀(x, (x ∈ G) ==> ((op(identity(G, *), *, x) === x) /\ (op(x, *, identity(G, *)) === x)))) by Tautology.from(
      identityIsNeutral,
      isNeutral.definition of (e -> identity(G, *))
    )
    thenHave(group(G, *) |- (x ∈ G) ==> ((op(identity(G, *), *, x) === x) /\ (op(x, *, identity(G, *)) === x))) by InstantiateForall(x)
    thenHave(thesis) by Restate
  }

  /**
   * Theorem --- The identity element belongs to the group.
   *
   * This simple theorem has unexpected consequences, such as [[groupNonEmpty]].
   */
  val identityInGroup = Theorem(
    group(G, *) |- identity(G, *) ∈ G
  ) {
    have(thesis) by Tautology.from(
      identityIsNeutral,
      isNeutral.definition of (e -> identity(G, *))
    )
  }

  /**
   * Theorem --- A group is non-empty.
   *
   * Direct corollary of [[identityInGroup]].
   */
  val groupNonEmpty = Theorem(
    group(G, *) |- (G !== ∅)
  ) {
    have(thesis) by Cut(identityInGroup, setWithElementNonEmpty of (x -> G, y -> identity(G, *)))
  }

  /**
   * Theorem --- The inverse of an element `x` (i.e. `y` such that `x * y = y * x = e`) in `G` is unique.
   */
  val inverseUniqueness = Theorem(
    (group(G, *), x ∈ G) |- ∃!(y, isInverse(y, x, G, *))
  ) {
    have(group(G, *) |- ∀(x, x ∈ G ==> ∃(y, isInverse(y, x, G, *)))) by Tautology.from(group.definition, inverseExistence.definition)
    thenHave(group(G, *) |- (x ∈ G ==> ∃(y, isInverse(y, x, G, *)))) by InstantiateForall(x)
    val existence = thenHave((group(G, *), x ∈ G) |- ∃(y, isInverse(y, x, G, *))) by Restate

    // Assume y and z are inverses of x.
    // We prove the following chain of equalities:
    //   z === (yx)z === y(xz) === y
    // where equalities come from
    //   1. Left neutrality of yx
    //   2. Associativity
    //   3. Right neutrality of xz
    val uniqueness = have((group(G, *), x ∈ G, isInverse(y, x, G, *), isInverse(z, x, G, *)) |- (y === z)) subproof {
      val inverseMembership = have(isInverse(y, x, G, *) |- y ∈ G) by Tautology.from(isInverse.definition)

      // 1. (yx)z = z
      val leftNeutrality = have((group(G, *), x ∈ G, isInverse(y, x, G, *), z ∈ G) |- (op(op(y, *, x), *, z) === z)) subproof {
        assume(group(G, *))
        assume(x ∈ G)
        assume(isInverse(y, x, G, *))
        assume(z ∈ G)

        have(∀(u, u ∈ G ==> ((op(op(y, *, x), *, u) === u) /\ (op(u, *, op(y, *, x)) === u)))) by Tautology.from(isInverse.definition, isNeutral.definition of (e -> op(y, *, x)))
        thenHave(z ∈ G ==> ((op(op(y, *, x), *, z) === z) /\ (op(z, *, op(y, *, x)) === z))) by InstantiateForall(z)
        thenHave(op(op(y, *, x), *, z) === z) by Tautology
      }
      val firstEq = have((group(G, *), x ∈ G, isInverse(y, x, G, *), isInverse(z, x, G, *)) |- op(op(y, *, x), *, z) === z) by Cut(inverseMembership of (y -> z), leftNeutrality)

      // 2. (yx)z = y(xz)
      val associativityCut = have((group(G, *), x ∈ G /\ y ∈ G /\ z ∈ G) |- (op(op(y, *, x), *, z) === op(y, *, op(x, *, z)))) by Restate.from(
        associativity of (x -> y, y -> x)
      )
      val memberships = have((x ∈ G, isInverse(y, x, G, *), isInverse(z, x, G, *)) |- x ∈ G /\ y ∈ G /\ z ∈ G) by Tautology.from(inverseMembership of (y -> y), inverseMembership of (y -> z))
      val secondEq = have((group(G, *), x ∈ G, isInverse(y, x, G, *), isInverse(z, x, G, *)) |- op(op(y, *, x), *, z) === op(y, *, op(x, *, z))) by Cut(memberships, associativityCut)

      // 3. y(xz) = y
      val rightNeutrality = have((group(G, *), x ∈ G, y ∈ G, isInverse(z, x, G, *)) |- (op(y, *, op(x, *, z)) === y)) subproof {
        assume(group(G, *))
        assume(x ∈ G)
        assume(y ∈ G)
        assume(isInverse(z, x, G, *))

        have(∀(u, u ∈ G ==> ((op(op(x, *, z), *, u) === u) /\ (op(u, *, op(x, *, z)) === u)))) by Tautology.from(isInverse.definition of (y -> z), isNeutral.definition of (e -> op(x, *, z)))
        thenHave(y ∈ G ==> ((op(op(x, *, z), *, y) === y) /\ (op(y, *, op(x, *, z)) === y))) by InstantiateForall(y)
        thenHave(op(y, *, op(x, *, z)) === y) by Tautology
      }
      val thirdEq = have((group(G, *), x ∈ G, isInverse(y, x, G, *), isInverse(z, x, G, *)) |- op(y, *, op(x, *, z)) === y) by Cut(inverseMembership of (y -> y), rightNeutrality)

      // 4. z = y
      have((group(G, *), x ∈ G, isInverse(y, x, G, *), isInverse(z, x, G, *)) |- z === y) by Equalities(firstEq, secondEq, thirdEq)
    }

    have(thesis) by ExistenceAndUniqueness(isInverse(y, x, G, *))(existence, uniqueness)
  }

  /**
   * Defines the inverse of an element `x` in a group `(G, *)`.
   */
  val inverse = DEF(x, G, *) --> TheConditional(y, isInverse(y, x, G, *))(inverseUniqueness)

  /**
   * Lemma --- The inverse of `x` is an inverse of `x` (by definition).
   */
  private val inverseIsInverse = Lemma(
    (group(G, *), x ∈ G) |- isInverse(inverse(x, G, *), x, G, *)
  ) {
    have(thesis) by Definition(inverse, inverseUniqueness)(x, G, *)
  }

  /**
   * Lemma --- The inverse element `y` of `x` is in `G`.
   */
  val inverseInGroup = Lemma(
    (group(G, *), x ∈ G) |- inverse(x, G, *) ∈ G
  ) {
    have(thesis) by Tautology.from(
      inverseIsInverse,
      isInverse.definition of (y -> inverse(x, G, *))
    )
  }

  /**
   * Theorem --- For any element `x`, we have `x * inverse(x) = inverse(x) * x = e`.
   */
  val inverseCancellation = Theorem(
    (group(G, *), x ∈ G) |- (op(x, *, inverse(x, G, *)) === identity(G, *)) /\ (op(inverse(x, G, *), *, x) === identity(G, *))
  ) {
    assume(group(G, *))

    have(∀(y, (y === identity(G, *)) <=> isNeutral(y, G, *))) by Tautology.from(
      identity.definition,
      identityUniqueness
    )
    val idCharacterization = thenHave((y === identity(G, *)) <=> isNeutral(y, G, *)) by InstantiateForall(y)

    assume(x ∈ G)
    val inverseDef = have((inverse(x, G, *) ∈ G) /\ isNeutral(op(x, *, inverse(x, G, *)), G, *) /\ isNeutral(op(inverse(x, G, *), *, x), G, *)) by Tautology.from(
      inverseIsInverse,
      isInverse.definition of (y -> inverse(x, G, *))
    )

    val left = have(op(x, *, inverse(x, G, *)) === identity(G, *)) by Tautology.from(
      inverseDef,
      idCharacterization of (y -> op(x, *, inverse(x, G, *)))
    )
    val right = have(op(inverse(x, G, *), *, x) === identity(G, *)) by Tautology.from(
      inverseDef,
      idCharacterization of (y -> op(inverse(x, G, *), *, x))
    )

    have(thesis) by RightAnd(left, right)
  }

  /**
   * Theorem --- `y` is the inverse of `x` iff `x` is the inverse of `y`
   */
  val inverseSymmetry = Theorem(
    (group(G, *), x ∈ G, y ∈ G) |- (y === inverse(x, G, *)) <=> (x === inverse(y, G, *))
  ) {
    assume(group(G, *))

    val inverseCharacterization = have(x ∈ G |- ((y === inverse(x, G, *)) <=> isInverse(y, x, G, *))) subproof {
      have(x ∈ G |- ∀(y, (y === inverse(x, G, *)) <=> isInverse(y, x, G, *))) by Tautology.from(inverseUniqueness, inverse.definition)
      thenHave(thesis) by InstantiateForall(y)
    }

    val forward = have(x ∈ G |- isInverse(y, x, G, *) ==> isInverse(x, y, G, *)) subproof {
      assume(x ∈ G)
      have(isInverse(y, x, G, *) |- y ∈ G /\ isNeutral(op(x, *, y), G, *) /\ isNeutral(op(y, *, x), G, *)) by Tautology.from(isInverse.definition)
      thenHave(isInverse(y, x, G, *) |- isNeutral(op(y, *, x), G, *) /\ isNeutral(op(x, *, y), G, *)) by Tautology
      thenHave(isInverse(y, x, G, *) |- x ∈ G /\ isNeutral(op(y, *, x), G, *) /\ isNeutral(op(x, *, y), G, *)) by Tautology

      have(isInverse(y, x, G, *) |- isInverse(x, y, G, *)) by Tautology.from(lastStep, isInverse.definition of (y -> x, x -> y))
      thenHave(thesis) by Restate
    }

    val backward = forward of (x -> y, y -> x)

    have((x ∈ G, y ∈ G) |- isInverse(y, x, G, *) <=> isInverse(x, y, G, *)) by RightIff(forward, backward)

    have(thesis) by Tautology.from(
      inverseCharacterization,
      lastStep,
      inverseCharacterization of (x -> y, y -> x)
    )
  }

  /**
   * Involution of the inverse -- For all `x`, `inverse(inverse(x)) = x`.
   *
   * Direct corollary of [[inverseSymmetry]].
   */
  val inverseIsInvolutive = Theorem(
    (group(G, *), x ∈ G) |- (inverse(inverse(x, G, *), G, *) === x)
  ) {
    have(thesis) by Tautology.from(
      inverseSymmetry of (y -> inverse(x, G, *)),
      inverseInGroup
    )
  }

  /**
   * Theorem --- In a group `(G, *)`, we have `xy = xz ==> y = z`.
   */
  val leftCancellation = Theorem(
    (group(G, *), x ∈ G, y ∈ G, z ∈ G) |- (op(x, *, y) === op(x, *, z)) ==> (y === z)
  ) {
    val i = inverse(x, G, *)

    // 1. Prove that i * (xy) = y and i * (xz) = z
    val cancellation = have((group(G, *), x ∈ G, y ∈ G) |- op(i, *, op(x, *, y)) === y) subproof {
      // (ix)y = i(xy)
      val eq1 = have((group(G, *), x ∈ G, y ∈ G) |- op(op(i, *, x), *, y) === op(i, *, op(x, *, y))) by Cut(
        inverseInGroup,
        associativity of (x -> i, y -> x, z -> y)
      )

      // (ix)y = y
      have((group(G, *), x ∈ G) |- ∀(y, (y ∈ G) ==> ((op(op(i, *, x), *, y) === y) /\ (op(y, *, op(i, *, x)) === y)))) by Tautology.from(
        inverseIsInverse,
        isInverse.definition of (y -> i),
        isNeutral.definition of (e -> op(i, *, x))
      )
      thenHave((group(G, *), x ∈ G) |- (y ∈ G) ==> ((op(op(i, *, x), *, y) === y) /\ (op(y, *, op(i, *, x)) === y))) by InstantiateForall(y)
      val eq2 = thenHave((group(G, *), x ∈ G, y ∈ G) |- op(op(i, *, x), *, y) === y) by Tautology

      // i(xy) = y
      have(thesis) by Equalities(eq1, eq2)
    }

    // 2. By substitution, xy = xz implies i(xy) = i(xz)
    have(op(i, *, op(x, *, y)) === op(i, *, op(x, *, y))) by RightRefl
    val substitution = thenHave(op(x, *, y) === op(x, *, z) |- op(i, *, op(x, *, y)) === op(i, *, op(x, *, z))) by RightSubstEq(
      List((op(x, *, y), op(x, *, z))),
      lambda(z, op(i, *, op(x, *, y)) === op(i, *, z))
    )

    // 3. Conclude that xy = xz ==> y === z
    have((group(G, *), x ∈ G, y ∈ G, z ∈ G, op(x, *, y) === op(x, *, z)) |- y === z) by Equalities(cancellation, cancellation of (y -> z), substitution)
    thenHave(thesis) by Restate
  }

  /**
   * Theorem --- In a group `(G, *)`, we have `yx = zx ==> y = z`.
   *
   * Analoguous to [[leftCancellation]].
   */
  val rightCancellation = Theorem(
    (group(G, *), x ∈ G, y ∈ G, z ∈ G) |- (op(y, *, x) === op(z, *, x)) ==> (y === z)
  ) {
    val i = inverse(x, G, *)

    // 1. Prove that (yx)i = y and (zx)i = z
    val cancellation = have((group(G, *), x ∈ G, y ∈ G) |- op(op(y, *, x), *, i) === y) subproof {
      // (xy)i = y(xi)
      val eq1 = have((group(G, *), x ∈ G, y ∈ G) |- op(op(y, *, x), *, i) === op(y, *, op(x, *, i))) by Cut(
        inverseInGroup,
        associativity of (x -> y, y -> x, z -> i)
      )

      // y(xi) = y
      have((group(G, *), x ∈ G) |- ∀(y, (y ∈ G) ==> ((op(op(x, *, i), *, y) === y) /\ (op(y, *, op(x, *, i)) === y)))) by Tautology.from(
        inverseIsInverse,
        isInverse.definition of (y -> i),
        isNeutral.definition of (e -> op(x, *, i))
      )
      thenHave((group(G, *), x ∈ G) |- (y ∈ G) ==> ((op(op(x, *, i), *, y) === y) /\ (op(y, *, op(x, *, i)) === y))) by InstantiateForall(y)
      val eq2 = thenHave((group(G, *), x ∈ G, y ∈ G) |- op(y, *, op(x, *, i)) === y) by Tautology

      // (yx)i = y
      have(thesis) by Equalities(eq1, eq2)
    }

    // 2. By substitution, yx = zx implies (yx)i = (zx)i
    have(op(op(y, *, x), *, i) === op(op(y, *, x), *, i)) by RightRefl
    val substitution = thenHave(op(y, *, x) === op(z, *, x) |- op(op(y, *, x), *, i) === op(op(z, *, x), *, i)) by RightSubstEq(
      List((op(y, *, x), op(z, *, x))),
      lambda(z, op(op(y, *, x), *, i) === op(z, *, i))
    )

    // 3. Conclude that yx = zx ==> y === z
    have((group(G, *), x ∈ G, y ∈ G, z ∈ G, op(y, *, x) === op(z, *, x)) |- y === z) by Equalities(cancellation, cancellation of (y -> z), substitution)
    thenHave(thesis) by Restate
  }

  /**
   * Theorem --- An element `x` of a group `(G, *)` is idempotent if and only if `x` is the identity element.
   */
  val identityIdempotence = Theorem(
    (group(G, *), x ∈ G) |- (op(x, *, x) === x) <=> (x === identity(G, *))
  ) {
    assume(group(G, *))
    assume(x ∈ G)

    val neutralityEquality = have(op(identity(G, *), *, x) === x) by Tautology.from(identityNeutrality)

    // Forward direction, using the equality x * x = x = e * x
    // and concluding by right cancellation
    have(op(x, *, x) === x |- x === identity(G, *)) subproof {
      have(op(x, *, x) === x |- op(x, *, x) === x) by Hypothesis
      have(op(x, *, x) === x |- op(x, *, x) === op(identity(G, *), *, x)) by Equalities(lastStep, neutralityEquality)
      have((op(x, *, x) === x, identity(G, *) ∈ G) |- x === identity(G, *)) by Tautology.from(
        lastStep,
        rightCancellation of (x -> x, y -> x, z -> identity(G, *))
      )
      have(thesis) by Cut(identityInGroup, lastStep)
    }
    val forward = thenHave((op(x, *, x) === x) ==> (x === identity(G, *))) by Restate

    have(x === identity(G, *) |- op(x, *, x) === x) by RightSubstEq(
      List((x, identity(G, *))),
      lambda(z, op(z, *, x) === x)
    )(neutralityEquality)
    val backward = thenHave((x === identity(G, *)) ==> (op(x, *, x) === x)) by Restate

    have(thesis) by RightIff(forward, backward)
  }

  /**
   * Theorem --- If `x * y = e` then `y = inverse(x)`.
   *
   * This also implies that `x = inverse(y)` by [[inverseSymmetry]].
   */
  val inverseTest = Theorem(
    (group(G, *), x ∈ G, y ∈ G) |- (op(x, *, y) === identity(G, *)) ==> (y === inverse(x, G, *))
  ) {
    assume(group(G, *))
    assume(x ∈ G)
    assume(y ∈ G)

    val e = identity(G, *)

    // 1. e = x * inverse(x)
    val eq1 = have(op(x, *, inverse(x, G, *)) === e) by Tautology.from(
      identityInGroup,
      inverseCancellation
    )

    // 2. x * y = x * inverse(x)
    have((op(x, *, y) === e) |- (op(x, *, y) === e)) by Hypothesis
    val eq2 = have((op(x, *, y) === e) |- op(x, *, y) === op(x, *, inverse(x, G, *))) by Equalities(eq1, lastStep)

    // Conclude by left cancellation
    have((op(x, *, y) === e, inverse(x, G, *) ∈ G) |- (y === inverse(x, G, *))) by Tautology.from(
      lastStep,
      leftCancellation of (z -> inverse(x, G, *))
    )
    have((op(x, *, y) === e) |- (y === inverse(x, G, *))) by Cut(inverseInGroup, lastStep)
    thenHave(thesis) by Restate
  }

  /**
   * Theorem --- The inverse of the identity element is itself.
   */
  val inverseOfIdentityIsIdentity = Theorem(
    group(G, *) |- inverse(identity(G, *), G, *) === identity(G, *)
  ) {
    assume(group(G, *))

    val e = identity(G, *)

    have(x ∈ G |- ∀(y, (y === inverse(x, G, *)) <=> isInverse(y, x, G, *))) by Tautology.from(
      inverseUniqueness,
      inverse.definition
    )
    thenHave(x ∈ G |- (e === inverse(x, G, *)) <=> isInverse(e, x, G, *)) by InstantiateForall(e)
    val characterization = have((e === inverse(e, G, *)) <=> isInverse(e, e, G, *)) by Cut(identityInGroup, lastStep of (x -> e))

    // Prove that e is an inverse of e
    val satisfaction = have(isInverse(e, e, G, *)) subproof {
      val neutrality = have(op(e, *, e) === e) by Cut(identityInGroup, identityNeutrality of (x -> e))

      have((op(e, *, e) === e) |- isNeutral(op(e, *, e), G, *)) by RightSubstEq(
        List((op(e, *, e), e)),
        lambda(z, isNeutral(z, G, *))
      )(identityIsNeutral)

      have(isNeutral(op(e, *, e), G, *)) by Cut(neutrality, lastStep)

      have(e ∈ G /\ isNeutral(op(e, *, e), G, *) /\ isNeutral(op(e, *, e), G, *)) by RightAnd(identityInGroup, lastStep, lastStep)
      have(thesis) by Tautology.from(lastStep, isInverse.definition of (x -> e, y -> e))
    }

    have(thesis) by Tautology.from(characterization, satisfaction)
  }

  // TODO Direct product group
  // TODO Permutation group

  //
  // 2. Subgroups
  //

  // By convention, this will always refer to the restricted operation.
  private val ★ = restrictedFunction(*, cartesianProduct(H, H))

  /**
   * Subgroup --- `H` is a subgroup of `(G, *)` if `H` is a subset of `G`, such that the restriction of `*` to `H` is
   * a group law for `H`, i.e. `(H, *_H)` is a group.
   *
   * We denote `H <= G` for `H` a subgroup of `G`.
   */
  val subgroup = DEF(H, G, *) --> group(G, *) /\ subset(H, G) /\ group(H, restrictedFunction(*, cartesianProduct(H, H)))

  /**
   * Lemma --- A group is a subgroup of itself, i.e. the subgroup relationship is reflexive.
   */
  val groupIsSubgroupOfItself = Theorem(
    group(G, *) |- subgroup(G, G, *)
  ) {
    val condition1 = have(group(G, *) |- group(G, *)) by Hypothesis
    val condition2 = have(subset(G, G)) by Restate.from(subsetReflexivity of (x -> G))

    // For condition 3, we need to substitute everything using the 3 following equalities:
    // 1. restrictedFunction(*, relationDomain(*)) === *       (restrictedFunctionCancellation)
    // 2. relationDomain(*) === cartesianProduct(G, G)         (groupOperationDomain)
    // 3. restrictedFunction(*, cartesianProduct(G, G)) === *  (derived from 1. and 2.)

    val substitution = have((group(G, *), restrictedFunction(*, cartesianProduct(G, G)) === *) |- group(G, restrictedFunction(*, cartesianProduct(G, G)))) by RightSubstEq(
      List((restrictedFunction(*, cartesianProduct(G, G)), *)),
      lambda(z, group(G, z))
    )(condition1)

    val eq3 = have(group(G, *) |- restrictedFunction(*, cartesianProduct(G, G)) === *) subproof {
      assume(group(G, *))
      val eq1 = have(restrictedFunction(*, relationDomain(*)) === *) by Cut(
        groupOperationIsFunctional,
        restrictedFunctionCancellation of (f -> *)
      )
      thenHave((relationDomain(*) === cartesianProduct(G, G)) |- restrictedFunction(*, cartesianProduct(G, G)) === *) by RightSubstEq(
        List((relationDomain(*), cartesianProduct(G, G))),
        lambda(z, restrictedFunction(*, z) === *)
      )

      have(thesis) by Cut(groupOperationDomain, lastStep)
    }

    val condition3 = have(group(G, *) |- group(G, restrictedFunction(*, cartesianProduct(G, G)))) by Cut(eq3, substitution)

    have(group(G, *) |- group(G, *) /\ subset(G, G) /\ group(G, restrictedFunction(*, cartesianProduct(G, G)))) by RightAnd(condition1, condition2, condition3)
    have(thesis) by Tautology.from(lastStep, subgroup.definition of (G -> G, H -> G))
  }

  /**
   * Proper subgroup --- `H` is a proper subgroup of `(G, *)` if `H` is a subgroup of `G` and `H != G`.
   */
  val properSubgroup = DEF(H, G, *) --> subgroup(H, G, *) /\ (H !== G)

  /**
   * Lemma --- If `x` and `y` are two elements of the subgroup `H` of `(G, *)`, the pair belongs to the relation domain
   * of the parent group's operation `*`.
   *
   * Analogous to [[groupPairInOperationDomain]], except that the considered relation is different.
   */
  val subgroupPairInParentOperationDomain = Lemma(
    (subgroup(H, G, *), x ∈ H, y ∈ H) |- pair(x, y) ∈ relationDomain(*)
  ) {
    assume(subgroup(H, G, *))
    assume(x ∈ H)
    assume(y ∈ H)

    have(subset(H, G)) by Tautology.from(subgroup.definition)
    have(∀(x, x ∈ H ==> x ∈ G)) by Tautology.from(lastStep, subset.definition of (x -> H, y -> G))
    val subsetDef = thenHave(x ∈ H ==> x ∈ G) by InstantiateForall(x)

    val left = have(x ∈ G) by Tautology.from(subsetDef)
    val right = have(y ∈ G) by Tautology.from(subsetDef of (x -> y))

    have(group(G, *)) by Tautology.from(subgroup.definition)

    have(thesis) by Tautology.from(lastStep, left, right, groupPairInOperationDomain)
  }

  /**
   * Theorem --- The subgroup operation is exactly the same as in the above group, i.e. if `(G, *)` is a group, `H` a
   * subgroup of `G`, then for elements `x, y ∈ H` we have `x ★ y = x * y`, where `★ = *_H`.
   */
  val subgroupOperation = Theorem(
    (subgroup(H, G, *), x ∈ H, y ∈ H) |- (op(x, ★, y) === op(x, *, y))
  ) {
    assume(subgroup(H, G, *))
    val groupG = have(group(G, *)) by Tautology.from(subgroup.definition)
    val groupH = have(group(H, ★)) by Tautology.from(subgroup.definition)

    have((x ∈ H, y ∈ H) |- pair(x, y) ∈ relationDomain(★)) by Tautology.from(
      groupH,
      groupPairInOperationDomain of (G -> H, * -> ★)
    )
    have((functional(*), x ∈ H, y ∈ H) |- op(x, ★, y) === op(x, *, y)) by Cut(
      lastStep,
      restrictedFunctionApplication of (f -> *, d -> cartesianProduct(H, H), x -> pair(x, y))
    )
    have(thesis) by Tautology.from(
      lastStep,
      groupOperationIsFunctional,
      groupG
    )
  }

  /**
   * Lemma --- If `H` is a subgroup of `G`, then `e_H ∈ G`.
   */
  val subgroupIdentityInParent = Lemma(
    subgroup(H, G, *) |- identity(H, ★) ∈ G
  ) {
    val identityInH = have(subgroup(H, G, *) |- identity(H, ★) ∈ H) by Tautology.from(
      subgroup.definition,
      identityInGroup of (G -> H, * -> ★)
    )

    have(subgroup(H, G, *) |- ∀(x, x ∈ H ==> x ∈ G)) by Tautology.from(
      subgroup.definition,
      subset.definition of (x -> H, y -> G)
    )
    thenHave(subgroup(H, G, *) |- identity(H, ★) ∈ H ==> identity(H, ★) ∈ G) by InstantiateForall(identity(H, ★))
    thenHave((subgroup(H, G, *), identity(H, ★) ∈ H) |- identity(H, ★) ∈ G) by Restate

    have(thesis) by Cut(identityInH, lastStep)
  }

  /**
   * Identity in subgroup --- The identity element `e_H` of a subgroup `H` of `G` is exactly the identity element `e_G` of
   * the parent group `(G, *)`.
   */
  val subgroupIdentity = Theorem(
    subgroup(H, G, *) |- identity(H, ★) === identity(G, *)
  ) {
    val e_G = identity(G, *)
    val e_H = identity(H, ★)

    val groupG = have(subgroup(H, G, *) |- group(G, *)) by Tautology.from(subgroup.definition)
    val groupH = have(subgroup(H, G, *) |- group(H, ★)) by Tautology.from(subgroup.definition)

    val subgroupIdentityInH = have(subgroup(H, G, *) |- identity(H, ★) ∈ H) by Tautology.from(
      subgroup.definition,
      identityInGroup of (G -> H, * -> ★)
    )

    // 1. e_H ★ e_H = e_H
    val eq1 = have(subgroup(H, G, *) |- op(e_H, ★, e_H) === e_H) subproof {
      have(group(H, ★) |- (op(e_H, ★, e_H) === e_H)) by Cut(
        identityInGroup of (G -> H, * -> ★),
        identityNeutrality of (G -> H, * -> ★, x -> e_H)
      )

      have(thesis) by Cut(groupH, lastStep)
    }

    // 2. e_H * e_H = e_H
    have(subgroup(H, G, *) |- op(e_H, ★, e_H) === op(e_H, *, e_H)) by Cut(
      subgroupIdentityInH,
      subgroupOperation of (x -> e_H, y -> e_H)
    )
    val eq2 = have(subgroup(H, G, *) |- op(e_H, *, e_H) === e_H) by Equalities(eq1, lastStep)

    // 3. e_G * e_H = e_H
    val eq3 = have(subgroup(H, G, *) |- op(e_G, *, e_H) === e_H) subproof {
      have((group(G, *), e_H ∈ G) |- op(e_G, *, e_H) === e_H) by Tautology.from(identityNeutrality of (x -> e_H))
      have((subgroup(H, G, *), e_H ∈ G) |- op(e_G, *, e_H) === e_H) by Cut(groupG, lastStep)
      have(thesis) by Cut(subgroupIdentityInParent, lastStep)
    }

    // Conclude by right cancellation
    val eq4 = have(subgroup(H, G, *) |- op(e_H, *, e_H) === op(e_G, *, e_H)) by Equalities(eq2, eq3)
    have((group(G, *), e_H ∈ G, e_G ∈ G, op(e_H, *, e_H) === op(e_G, *, e_H)) |- e_H === e_G) by Restate.from(
      rightCancellation of (x -> e_H, y -> e_H, z -> e_G)
    )
    have((subgroup(H, G, *), e_H ∈ G, e_G ∈ G, op(e_H, *, e_H) === op(e_G, *, e_H)) |- e_H === e_G) by Cut(groupG, lastStep)
    have((subgroup(H, G, *), e_H ∈ G, e_G ∈ G) |- e_H === e_G) by Cut(eq4, lastStep)

    val finalStep = have((subgroup(H, G, *), e_G ∈ G) |- e_H === e_G) by Cut(subgroupIdentityInParent, lastStep)

    have(subgroup(H, G, *) |- e_G ∈ G) by Cut(groupG, identityInGroup)
    have(thesis) by Cut(lastStep, finalStep)
  }

  /**
   * Theorem --- If `H` is a subgroup of `G`, then the inverse is the same as in the parent group.
   */
  val subgroupInverse = Theorem(
    (subgroup(H, G, *), x ∈ H) |- inverse(x, H, ★) === inverse(x, G, *)
  ) {
    assume(subgroup(H, G, *))
    assume(x ∈ H)

    have(∀(x, (x ∈ H) ==> (x ∈ G))) by Tautology.from(
      subgroup.definition,
      subset.definition of (x -> H, y -> G)
    )
    val subsetDef = thenHave((x ∈ H) ==> (x ∈ G)) by InstantiateForall(x)
    val xInG = thenHave(x ∈ G) by Tautology

    val groupG = have(group(G, *)) by Tautology.from(subgroup.definition)
    val groupH = have(group(H, ★)) by Tautology.from(subgroup.definition)

    val eG = identity(G, *)
    val eH = identity(H, ★)

    val inverseHInH = have(inverse(x, H, ★) ∈ H) by Cut(groupH, inverseInGroup of (G -> H, * -> ★))
    val inverseHInG = have(inverse(x, H, ★) ∈ G) by Tautology.from(inverseHInH, subsetDef of (x -> inverse(x, H, ★)))

    // 1. x * inverse(x, H, ★) = e_H
    have((inverse(x, H, ★) ∈ H) |- (op(x, ★, inverse(x, H, ★)) === eH)) by Tautology.from(
      groupH,
      inverseCancellation of (G -> H, * -> ★)
    )
    have((inverse(x, H, ★) ∈ H) |- (op(x, *, inverse(x, H, ★)) === eH)) by Equalities(
      lastStep,
      subgroupOperation of (y -> inverse(x, H, ★))
    )

    val eq1 = have(op(x, *, inverse(x, H, ★)) === eH) by Cut(inverseHInH, lastStep)

    // 2. e_H = e_G
    val eq2 = have(eH === eG) by Tautology.from(subgroupIdentity)

    // 3. x * inverse(x, G, *) = e_G
    val eq3 = have(op(x, *, inverse(x, G, *)) === eG) by Tautology.from(
      groupG,
      xInG,
      inverseInGroup,
      inverseCancellation
    )

    // 4. x * inverse(x, H, ★) === x * inverse(x, G, *)
    have(op(x, *, inverse(x, H, ★)) === op(x, *, inverse(x, G, *))) by Equalities(eq1, eq2, eq3)

    // Conclude by left cancellation
    have(thesis) by Tautology.from(
      lastStep,
      groupG,
      xInG,
      inverseHInG,
      inverseInGroup,
      leftCancellation of (y -> inverse(x, H, ★), z -> inverse(x, G, *))
    )
  }

  //
  // 2.1 Main subgroup test
  //
  // We define several useful lemmas to attack this easy, but long theorem to formalize
  //

  private val nonEmpty = H !== ∅
  private val closedByProducts = ∀(x, ∀(y, (x ∈ H /\ y ∈ H) ==> (op(x, *, y) ∈ H)))
  private val closedByInverses = ∀(x, x ∈ H ==> (inverse(x, G, *) ∈ H))
  private val subgroupConditions = nonEmpty /\ closedByProducts /\ closedByInverses

  /**
   * Lemma --- Reformulation of the subset definition.
   */
  private val subgroupConditionsSubset = Lemma(
    (subset(H, G), x ∈ H) |- x ∈ G
  ) {
    assume(subset(H, G))
    have(∀(x, x ∈ H ==> x ∈ G)) by Tautology.from(subset.definition of (x -> H, y -> G))
    thenHave(x ∈ H ==> x ∈ G) by InstantiateForall(x)
    thenHave(x ∈ H |- x ∈ G) by Restate
  }

  /**
   * Lemma --- The subgroup conditions imply that `relationDomain(★) === cartesianProduct(H, H)`.
   */
  private val subgroupConditionsDomain = Lemma(
    (group(G, *), subset(H, G), subgroupConditions) |- relationDomain(★) === cartesianProduct(H, H)
  ) {
    val H2 = cartesianProduct(H, H)
    val G2 = cartesianProduct(G, G)

    assume(group(G, *))
    assume(subset(H, G))
    assume(subgroupConditions)

    have(relationDomain(★) === (H2 ∩ relationDomain(*))) by Tautology.from(restrictedFunctionDomain of (f -> *, x -> H2))
    thenHave((relationDomain(*) === G2) |- relationDomain(★) === (H2 ∩ G2)) by RightSubstEq(
      List((relationDomain(*), G2)),
      lambda(z, relationDomain(★) === (H2 ∩ z))
    )
    val eq1 = have(relationDomain(★) === (H2 ∩ G2)) by Cut(groupOperationDomain, lastStep)

    // Prove that (H2 ∩ G2) = H2
    have(subset(H2, G2)) by Tautology.from(subsetsCartesianProduct of (a -> H, b -> G, c -> H, d -> G))
    val eq2 = have((H2 ∩ G2) === H2) by Cut(
      lastStep,
      setIntersectionSubset of (x -> H2, y -> G2)
    )

    have(thesis) by Equalities(eq1, eq2)
  }

  /**
   * Lemma --- The subgroup conditions imply that `(x, y)` is in the relation domain of `★`.
   *
   * Analogous to [[groupPairInOperationDomain]].
   */
  private val subgroupConditionsPairInDomain = Lemma(
    (group(G, *), subset(H, G), subgroupConditions, x ∈ H, y ∈ H) |- pair(x, y) ∈ relationDomain(★)
  ) {
    assume(group(G, *))
    assume(subset(H, G))
    assume(subgroupConditions)
    assume(x ∈ H)
    assume(y ∈ H)

    have(pair(x, y) ∈ cartesianProduct(H, H)) by Tautology.from(
      pairInCartesianProduct of (a -> x, b -> y, x -> H, y -> H)
    )
    thenHave((relationDomain(★) === cartesianProduct(H, H)) |- pair(x, y) ∈ relationDomain(★)) by RightSubstEq(
      List((relationDomain(★), cartesianProduct(H, H))),
      lambda(z, pair(x, y) ∈ z)
    )

    have(thesis) by Cut(subgroupConditionsDomain, lastStep)
  }

  /**
   * Lemma --- The subgroup conditions imply that `x ★ y = x * y`.
   *
   * Analogous to [[subgroupOperation]].
   */
  private val subgroupConditionsOperation = Lemma(
    (group(G, *), subset(H, G), subgroupConditions, x ∈ H, y ∈ H) |- op(x, ★, y) === op(x, *, y)
  ) {
    have(thesis) by Tautology.from(
      subgroupConditionsPairInDomain,
      groupOperationIsFunctional,
      restrictedFunctionIsFunctional of (f -> *, x -> cartesianProduct(H, H)),
      restrictedFunctionApplication of (f -> *, d -> cartesianProduct(H, H), x -> pair(x, y))
    )
  }

  /**
   * Lemma --- The subgroup conditions imply that `x ★ y ∈ H`.
   */
  private val subgroupConditionsProductClosure = Lemma(
    (group(G, *), subset(H, G), subgroupConditions, x ∈ H, y ∈ H) |- op(x, ★, y) ∈ H
  ) {
    assume(group(G, *))
    assume(subset(H, G))
    assume(subgroupConditions)

    have(closedByProducts) by Tautology
    thenHave(∀(y, (x ∈ H /\ y ∈ H) ==> (op(x, *, y) ∈ H))) by InstantiateForall(x)
    thenHave((x ∈ H /\ y ∈ H) ==> (op(x, *, y) ∈ H)) by InstantiateForall(y)
    thenHave((x ∈ H, y ∈ H) |- (op(x, *, y) ∈ H)) by Restate
    thenHave((x ∈ H, y ∈ H, op(x, ★, y) === op(x, *, y)) |- (op(x, ★, y) ∈ H)) by RightSubstEq(
      List((op(x, ★, y), op(x, *, y))),
      lambda(z, z ∈ H)
    )

    have(thesis) by Cut(subgroupConditionsOperation, lastStep)
  }

  /**
   * Lemma --- The subgroup conditions imply that `★` is a binary relation on `H`.
   */
  private val subgroupConditionsBinaryRelation = Lemma(
    (group(G, *), subset(H, G), subgroupConditions) |- binaryOperation(H, ★)
  ) {
    assume(group(G, *))
    assume(subset(H, G))
    assume(subgroupConditions)

    val H2 = cartesianProduct(H, H)
    val r = variable

    have(∀(t, (t ∈ setOfFunctions(H2, H)) <=> (t ∈ powerSet(cartesianProduct(H2, H)) /\ functionalOver(t, H2)))) by Definition(setOfFunctions, setOfFunctionsUniqueness)(H2, H)
    val setOfFunDef = thenHave((★ ∈ setOfFunctions(H2, H)) <=> (★ ∈ powerSet(cartesianProduct(H2, H)) /\ functionalOver(★, H2))) by InstantiateForall(★)

    val fun = have(functional(★)) by Tautology.from(
      groupOperationIsFunctional,
      restrictedFunctionIsFunctional of (f -> *, x -> H2)
    )
    have(functional(★) /\ (relationDomain(★) === H2)) by RightAnd(fun, subgroupConditionsDomain)
    val funOver = have(functionalOver(★, H2)) by Tautology.from(lastStep, functionalOver.definition of (f -> ★, x -> H2))

    have(subset(★, cartesianProduct(relationDomain(★), relationRange(★)))) by Tautology.from(
      fun,
      functional.definition of (f -> ★),
      relation.definition of (r -> ★),
      relationImpliesRelationBetweenDomainAndRange of (r -> ★),
      relationBetween.definition of (r -> ★, a -> relationDomain(★), b -> relationRange(★))
    )
    thenHave((relationDomain(★) === H2) |- subset(★, cartesianProduct(H2, relationRange(★)))) by RightSubstEq(
      List((relationDomain(★), H2)),
      lambda(z, subset(★, cartesianProduct(z, relationRange(★))))
    )

    val subsetDomRange = have(subset(★, cartesianProduct(H2, relationRange(★)))) by Cut(
      subgroupConditionsDomain,
      lastStep
    )

    // Prove that ★ is a subset of H2 x H
    val left = have(subset(H2, H2)) by Tautology.from(subsetReflexivity of (x -> H2))
    val right = have(subset(relationRange(★), H)) subproof {
      // Use pullback to characterize t
      val pullback = have(t ∈ relationRange(★) |- ∃(x, (x ∈ relationDomain(★)) /\ (app(★, x) === t))) by Tautology.from(
        groupOperationIsFunctional,
        restrictedFunctionIsFunctional of (f -> *, x -> H2),
        inRangeImpliesPullbackExists of (f -> ★, z -> t)
      )

      have((x ∈ relationDomain(★)) <=> (x ∈ relationDomain(★))) by Restate
      thenHave((relationDomain(★) === H2) |- (x ∈ relationDomain(★)) <=> (x ∈ H2)) by RightSubstEq(
        List((relationDomain(★), H2)),
        lambda(z, (x ∈ relationDomain(★)) <=> (x ∈ z))
      )
      val equiv1 = have((x ∈ relationDomain(★)) <=> (x ∈ H2)) by Cut(subgroupConditionsDomain, lastStep)
      val equiv2 = have((x ∈ H2) <=> ∃(a, ∃(b, (x === pair(a, b)) /\ in(a, H) /\ in(b, H)))) by Tautology.from(
        elemOfCartesianProduct of (t -> x, x -> H, y -> H)
      )

      // Use closure by products to show that app(★, x) ∈ H
      have(closedByProducts) by Tautology
      thenHave(∀(y, (a ∈ H /\ y ∈ H) ==> (op(a, *, y) ∈ H))) by InstantiateForall(a)
      thenHave((a ∈ H /\ b ∈ H) ==> (op(a, *, b) ∈ H)) by InstantiateForall(b)
      thenHave((a ∈ H, b ∈ H) |- (op(a, *, b) ∈ H)) by Restate
      thenHave((a ∈ H, b ∈ H, op(a, ★, b) === op(a, *, b)) |- (op(a, ★, b) ∈ H)) by RightSubstEq(
        List((op(a, ★, b), op(a, *, b))),
        lambda(z, z ∈ H)
      )

      have((a ∈ H, b ∈ H) |- (op(a, ★, b) ∈ H)) by Cut(
        subgroupConditionsOperation of (x -> a, y -> b),
        lastStep
      )
      thenHave((x === pair(a, b), a ∈ H, b ∈ H) |- (app(★, x) ∈ H)) by RightSubstEq(
        List((x, pair(a, b))),
        lambda(z, app(★, z) ∈ H)
      )
      thenHave(((x === pair(a, b)) /\ a ∈ H /\ b ∈ H) |- (app(★, x) ∈ H)) by Restate
      thenHave(∃(b, (x === pair(a, b)) /\ a ∈ H /\ b ∈ H) |- (app(★, x) ∈ H)) by LeftExists
      thenHave(∃(a, ∃(b, (x === pair(a, b)) /\ a ∈ H /\ b ∈ H)) |- (app(★, x) ∈ H)) by LeftExists

      have((x ∈ relationDomain(★)) |- (app(★, x) ∈ H)) by Tautology.from(lastStep, equiv1, equiv2)
      thenHave((x ∈ relationDomain(★), app(★, x) === t) |- (t ∈ H)) by RightSubstEq(
        List((app(★, x), t)),
        lambda(z, z ∈ H)
      )
      thenHave((x ∈ relationDomain(★) /\ (app(★, x) === t)) |- (t ∈ H)) by Restate
      thenHave(∃(x, x ∈ relationDomain(★) /\ (app(★, x) === t)) |- (t ∈ H)) by LeftExists

      have(t ∈ relationRange(★) |- t ∈ H) by Cut(pullback, lastStep)
      thenHave(t ∈ relationRange(★) ==> t ∈ H) by Restate
      thenHave(∀(t, t ∈ relationRange(★) ==> t ∈ H)) by RightForall

      have(thesis) by Tautology.from(lastStep, subset.definition of (x -> relationRange(★), y -> H))
    }

    have(subset(cartesianProduct(H2, relationRange(★)), cartesianProduct(H2, H))) by Tautology.from(
      left,
      right,
      subsetsCartesianProduct of (a -> H2, b -> H2, c -> relationRange(★), d -> H)
    )
    have(subset(★, cartesianProduct(H2, H))) by Tautology.from(
      lastStep,
      subsetDomRange,
      subsetTransitivity of (a -> ★, b -> cartesianProduct(H2, relationRange(★)), c -> cartesianProduct(H2, H))
    )
    have(★ ∈ powerSet(cartesianProduct(H2, H))) by Tautology.from(
      lastStep,
      powerSet.definition of (x -> ★, y -> cartesianProduct(H2, H))
    )

    have(★ ∈ powerSet(cartesianProduct(H2, H)) /\ functionalOver(★, H2)) by RightAnd(lastStep, funOver)

    have(thesis) by Tautology.from(
      lastStep,
      setOfFunDef,
      functionFrom.definition of (f -> ★, x -> H2, y -> H),
      binaryOperation.definition of (G -> H, * -> ★)
    )
  }

  /**
   * Lemma --- The subgroup conditions imply associativity on `H`.
   *
   * This directly follows from associativity on `G` and [[subgroupConditionsOperation]].
   */
  private val subgroupConditionsAssociativity = Lemma(
    (group(G, *), subset(H, G), subgroupConditions) |- associativityAxiom(H, ★)
  ) {
    assume(group(G, *))
    assume(subset(H, G))
    assume(subgroupConditions)

    have((x ∈ H, y ∈ H, z ∈ H) |- op(op(x, ★, y), ★, z) === op(x, ★, op(y, ★, z))) subproof {
      assume(x ∈ H)
      assume(y ∈ H)
      assume(z ∈ H)

      have(op(op(x, *, y), *, z) === op(x, *, op(y, *, z))) by Tautology.from(
        associativity,
        subgroupConditionsSubset,
        subgroupConditionsSubset of (x -> y),
        subgroupConditionsSubset of (x -> z)
      )
      thenHave((op(x, ★, y) === op(x, *, y), op(y, ★, z) === op(y, *, z)) |- (op(op(x, ★, y), *, z) === op(x, *, op(y, ★, z)))) by RightSubstEq(
        List((op(x, ★, y), op(x, *, y)), (op(y, ★, z), op(y, *, z))),
        lambda(Seq(a, b), op(a, *, z) === op(x, *, b))
      )

      have(op(op(x, ★, y), *, z) === op(x, *, op(y, ★, z))) by Tautology.from(
        lastStep,
        subgroupConditionsOperation,
        subgroupConditionsOperation of (x -> y, y -> z)
      )
      thenHave((op(op(x, ★, y), ★, z) === op(op(x, ★, y), *, z), op(x, ★, op(y, ★, z)) === op(x, *, op(y, ★, z))) |- (op(op(x, ★, y), ★, z) === op(x, ★, op(y, ★, z)))) by RightSubstEq(
        List((op(op(x, ★, y), ★, z), op(op(x, ★, y), *, z)), (op(x, ★, op(y, ★, z)), op(x, *, op(y, ★, z)))),
        lambda(Seq(a, b), a === b)
      )

      have(op(op(x, ★, y), ★, z) === op(x, ★, op(y, ★, z))) by Tautology.from(
        lastStep,
        subgroupConditionsOperation of (x -> op(x, ★, y), y -> z),
        subgroupConditionsOperation of (x -> x, y -> op(y, ★, z)),
        subgroupConditionsProductClosure,
        subgroupConditionsProductClosure of (x -> y, y -> z)
      )
    }

    // Reconstruct the axiom in its closed form
    thenHave((x ∈ H, y ∈ H) |- (z ∈ H) ==> (op(op(x, ★, y), ★, z) === op(x, ★, op(y, ★, z)))) by Restate
    thenHave((x ∈ H, y ∈ H) |- ∀(z, (z ∈ H) ==> (op(op(x, ★, y), ★, z) === op(x, ★, op(y, ★, z))))) by RightForall
    thenHave((x ∈ H) |- (y ∈ H) ==> ∀(z, (z ∈ H) ==> (op(op(x, ★, y), ★, z) === op(x, ★, op(y, ★, z))))) by Restate
    thenHave((x ∈ H) |- ∀(y, (y ∈ H) ==> ∀(z, (z ∈ H) ==> (op(op(x, ★, y), ★, z) === op(x, ★, op(y, ★, z)))))) by RightForall
    thenHave((x ∈ H) ==> ∀(y, (y ∈ H) ==> ∀(z, (z ∈ H) ==> (op(op(x, ★, y), ★, z) === op(x, ★, op(y, ★, z)))))) by Restate
    thenHave(∀(x, (x ∈ H) ==> ∀(y, (y ∈ H) ==> ∀(z, (z ∈ H) ==> (op(op(x, ★, y), ★, z) === op(x, ★, op(y, ★, z))))))) by RightForall

    have(thesis) by Tautology.from(lastStep, associativityAxiom.definition of (G -> H, * -> ★))
  }

  /**
   * Lemma --- The subgroup conditions imply the existence of an identity element on `H`.
   *
   * We show in particular that identity(G, *) is neutral on `H`.
   */
  private val subgroupConditionsIdentityExistence = Lemma(
    (group(G, *), subset(H, G), subgroupConditions) |- identityExistence(H, ★)
  ) {
    assume(group(G, *))
    assume(subset(H, G))
    assume(subgroupConditions)

    // We show that for an element x ∈ H:
    // 1. inverse(x) ∈ H                   [[closedByInverses]]
    // 2. x * inverse(x) ∈ H               [[closedByProducts]]
    // 3. x * inverse(x) = identity(G, *)  [[inverseCancellation]]
    // 4. identity(G, *) ∈ H               Substitution of 3. in 2.
    // 5. isNeutral(identity(G, *), H, ★)  [[identityNeutrality]]
    // 6. identityExistence(H, ★)          [[identityExistence]]
    // We finally conclude by [[nonEmpty]].

    // 1. inverse(x) ∈ H
    have(closedByInverses) by Tautology
    thenHave(((x ∈ H) ==> (inverse(x, G, *) ∈ H))) by InstantiateForall(x)
    val step1 = thenHave((x ∈ H) |- (inverse(x, G, *) ∈ H)) by Restate

    // 2. x * inverse(x) ∈ H
    have(closedByProducts) by Tautology
    thenHave(∀(y, (x ∈ H /\ y ∈ H) ==> (op(x, *, y) ∈ H))) by InstantiateForall(x)
    thenHave((x ∈ H /\ inverse(x, G, *) ∈ H) ==> (op(x, *, inverse(x, G, *)) ∈ H)) by InstantiateForall(inverse(x, G, *))
    thenHave((x ∈ H, inverse(x, G, *) ∈ H) |- (op(x, *, inverse(x, G, *)) ∈ H)) by Restate

    val step2 = have((x ∈ H) |- (op(x, *, inverse(x, G, *)) ∈ H)) by Cut(step1, lastStep)

    // 3. x * inverse(x) = identity(G, *)
    val step3 = have((x ∈ H) |- op(x, *, inverse(x, G, *)) === identity(G, *)) by Tautology.from(
      subgroupConditionsSubset,
      inverseCancellation
    )

    // 4. identity(G, *) ∈ H
    have((x ∈ H, op(x, *, inverse(x, G, *)) === identity(G, *)) |- (identity(G, *) ∈ H)) by RightSubstEq(
      List((op(x, *, inverse(x, G, *)), identity(G, *))),
      lambda(z, z ∈ H)
    )(step2)
    val step4 = have((x ∈ H) |- (identity(G, *) ∈ H)) by Cut(step3, lastStep)

    // 5. isNeutral(identity(G, *), H, ★)
    have((x ∈ H) |- (op(identity(G, *), *, x) === x) /\ (op(x, *, identity(G, *)) === x)) by Tautology.from(
      subgroupConditionsSubset,
      identityNeutrality
    )
    thenHave(
      (x ∈ H, op(identity(G, *), ★, x) === op(identity(G, *), *, x), op(x, ★, identity(G, *)) === op(x, *, identity(G, *))) |- (op(identity(G, *), ★, x) === x) /\ (op(x, ★, identity(G, *)) === x)
    ) by RightSubstEq(
      List((op(identity(G, *), ★, x), op(identity(G, *), *, x)), (op(x, ★, identity(G, *)), op(x, *, identity(G, *)))),
      lambda(Seq(a, b), (a === x) /\ (b === x))
    )

    have(x ∈ H |- (op(identity(G, *), ★, x) === x) /\ (op(x, ★, identity(G, *)) === x)) by Tautology.from(
      lastStep,
      step4,
      subgroupConditionsOperation of (x -> identity(G, *), y -> x),
      subgroupConditionsOperation of (x -> x, y -> identity(G, *))
    )

    thenHave((x ∈ H) ==> (op(identity(G, *), ★, x) === x) /\ (op(x, ★, identity(G, *)) === x)) by Restate
    thenHave(∀(x, (x ∈ H) ==> (op(identity(G, *), ★, x) === x) /\ (op(x, ★, identity(G, *)) === x))) by RightForall
    val step5 = have((x ∈ H) |- isNeutral(identity(G, *), H, ★)) by Tautology.from(
      lastStep,
      step4,
      isNeutral.definition of (e -> identity(G, *), G -> H, * -> ★)
    )

    // 6. identityExistence(H, ★)
    thenHave((x ∈ H) |- ∃(e, isNeutral(e, H, ★))) by RightExists
    val step6 = have((x ∈ H) |- identityExistence(H, ★)) by Tautology.from(lastStep, identityExistence.definition of (G -> H, * -> ★))

    // Conclude by [[nonEmpty]]
    thenHave(∃(x, x ∈ H) |- identityExistence(H, ★)) by LeftExists

    have(thesis) by Tautology.from(lastStep, nonEmptySetHasElement of (x -> H))
  }

  /**
   * Lemma --- The subgroup conditions imply that for all elements `x` in `H`, there exists an inverse in `H`.
   */
  private val subgroupConditionsInverseExistence = Lemma(
    (group(G, *), subset(H, G), subgroupConditions) |- inverseExistence(H, ★)
  ) {
    assume(group(G, *))
    assume(subset(H, G))
    assume(subgroupConditions)

    val i = inverse(x, G, *)

    have(closedByInverses) by Tautology
    thenHave(x ∈ H ==> i ∈ H) by InstantiateForall(x)
    val inverseInH = thenHave(x ∈ H |- i ∈ H) by Restate

    // Show that a neutral element of G is also neutral in H
    val neutralityInheritance = have((e ∈ H, isNeutral(e, G, *)) |- isNeutral(e, H, ★)) subproof {
      assume(isNeutral(e, G, *))
      have(∀(x, (x ∈ G) ==> ((op(e, *, x) === x) /\ (op(x, *, e) === x)))) by Tautology.from(isNeutral.definition)
      thenHave((x ∈ G) ==> ((op(e, *, x) === x) /\ (op(x, *, e) === x))) by InstantiateForall(x)
      thenHave(x ∈ G |- (op(e, *, x) === x) /\ (op(x, *, e) === x)) by Restate

      have(x ∈ H |- (op(e, *, x) === x) /\ (op(x, *, e) === x)) by Cut(subgroupConditionsSubset, lastStep)
      thenHave((x ∈ H, op(e, ★, x) === op(e, *, x), op(x, ★, e) === op(x, *, e)) |- (op(e, ★, x) === x) /\ (op(x, ★, e) === x)) by RightSubstEq(
        List((op(e, ★, x), op(e, *, x)), (op(x, ★, e), op(x, *, e))),
        lambda(Seq(a, b), (a === x) /\ (b === x))
      )

      have((x ∈ H, e ∈ H) |- (op(e, ★, x) === x) /\ (op(x, ★, e) === x)) by Tautology.from(
        lastStep,
        subgroupConditionsOperation of (x -> e, y -> x),
        subgroupConditionsOperation of (x -> x, y -> e)
      )
      thenHave(e ∈ H |- (x ∈ H) ==> (op(e, ★, x) === x) /\ (op(x, ★, e) === x)) by Restate
      thenHave(e ∈ H |- ∀(x, (x ∈ H) ==> (op(e, ★, x) === x) /\ (op(x, ★, e) === x))) by RightForall

      have(e ∈ H |- isNeutral(e, H, ★)) by Tautology.from(lastStep, isNeutral.definition of (G -> H, * -> ★))
    }

    // Show that i is neutral in H
    have(x ∈ H |- isNeutral(op(x, *, i), G, *) /\ isNeutral(op(i, *, x), G, *)) by Tautology.from(
      subgroupConditionsSubset,
      inverseIsInverse,
      isInverse.definition of (y -> inverse(x, G, *))
    )
    thenHave((x ∈ H, op(x, ★, i) === op(x, *, i), op(i, ★, x) === op(i, *, x)) |- isNeutral(op(x, ★, i), G, *) /\ isNeutral(op(i, ★, x), G, *)) by RightSubstEq(
      List((op(x, ★, i), op(x, *, i)), (op(i, ★, x), op(i, *, x))),
      lambda(Seq(a, b), isNeutral(a, G, *) /\ isNeutral(b, G, *))
    )

    have((x ∈ H, i ∈ H) |- isNeutral(op(x, ★, i), G, *) /\ isNeutral(op(i, ★, x), G, *)) by Tautology.from(
      lastStep,
      subgroupConditionsOperation of (x -> x, y -> i),
      subgroupConditionsOperation of (x -> i, y -> x)
    )

    have((x ∈ H, i ∈ H) |- isNeutral(op(x, ★, i), H, ★) /\ isNeutral(op(i, ★, x), H, ★)) by Tautology.from(
      lastStep,
      neutralityInheritance of (e -> op(x, ★, i)),
      neutralityInheritance of (e -> op(i, ★, x)),
      subgroupConditionsProductClosure of (x -> x, y -> i),
      subgroupConditionsProductClosure of (x -> i, y -> x)
    )

    have(x ∈ H |- (i ∈ H) /\ isNeutral(op(x, ★, i), H, ★) /\ isNeutral(op(i, ★, x), H, ★)) by Tautology.from(inverseInH, lastStep)
    have(x ∈ H |- isInverse(i, x, H, ★)) by Tautology.from(lastStep, isInverse.definition of (y -> i, G -> H, * -> ★))
    thenHave(x ∈ H |- ∃(y, isInverse(y, x, H, ★))) by RightExists
    thenHave(x ∈ H ==> ∃(y, isInverse(y, x, H, ★))) by Restate
    thenHave(∀(x, x ∈ H ==> ∃(y, isInverse(y, x, H, ★)))) by RightForall

    have(thesis) by Tautology.from(lastStep, inverseExistence.definition of (G -> H, * -> ★))
  }

  /**
   * Theorem (Main subgroup test) --- A subset `H ⊆ G` of a group `(G, *)` is a subgroup if and only if:
   *   1. `H` is non-empty,
   *   2. `H` is closed by products, and
   *   3. `H` is closed by inversion.
   *
   * It is often easier to prove the 3 conditions independently than using the definition directly.
   *
   * Note that in the case where H is finite, conditions 1 and 2 are sufficient.
   */
  val subgroupTest = Theorem(
    (group(G, *), subset(H, G)) |- (subgroup(H, G, *) <=> subgroupConditions)
  ) {
    assume(group(G, *))
    assume(subset(H, G))

    // The forward direction follow directly:
    // 1. nonEmpty --> [[groupNonEmpty]]
    // 2. closedByProducts --> [[subgroupOperation]] and [[groupIsClosedByProduct]]
    // 3. closedByInverses --> [[subgroupInverse]] and [[inverseInGroup]]
    have(subgroup(H, G, *) |- subgroupConditions) subproof {
      assume(subgroup(H, G, *))
      val groupH = have(group(H, ★)) by Tautology.from(subgroup.definition)

      val condition1 = have(nonEmpty) by Cut(groupH, groupNonEmpty of (G -> H, * -> ★))

      have((x ∈ H, y ∈ H) |- op(x, ★, y) ∈ H) by Cut(groupH, groupIsClosedByProduct of (G -> H, * -> ★))
      thenHave((x ∈ H, y ∈ H, op(x, ★, y) === op(x, *, y)) |- op(x, *, y) ∈ H) by RightSubstEq(
        List((op(x, ★, y), op(x, *, y))),
        lambda(z, z ∈ H)
      )

      have((x ∈ H, y ∈ H) |- op(x, *, y) ∈ H) by Cut(subgroupOperation, lastStep)
      thenHave((x ∈ H /\ y ∈ H) ==> (op(x, *, y) ∈ H)) by Restate
      thenHave(∀(y, (x ∈ H /\ y ∈ H) ==> (op(x, *, y) ∈ H))) by RightForall
      val condition2 = thenHave(closedByProducts) by RightForall

      have((x ∈ H) |- (inverse(x, H, ★) ∈ H)) by Cut(groupH, inverseInGroup of (G -> H, * -> ★))
      thenHave((x ∈ H, inverse(x, H, ★) === inverse(x, G, *)) |- inverse(x, G, *) ∈ H) by RightSubstEq(
        List((inverse(x, H, ★), inverse(x, G, *))),
        lambda(z, z ∈ H)
      )

      have((x ∈ H) |- (inverse(x, G, *) ∈ H)) by Cut(subgroupInverse, lastStep)
      thenHave((x ∈ H) ==> (inverse(x, G, *) ∈ H)) by Restate
      val condition3 = thenHave(closedByInverses) by RightForall

      have(subgroupConditions) by RightAnd(condition1, condition2, condition3)
    }
    val forward = thenHave(subgroup(H, G, *) ==> subgroupConditions) by Restate

    // For the backward direction, we must prove that the conditions make (H, ★) satisfy the axioms of a group:
    // 1. Closure by products (i.e. ★'s codomain is H): [[closedByProducts]]
    // 2. Associativity: follows from G's associativity
    // 3. Identity existence: follows from [[nonEmpty]], [[closedByProducts]] and [[closedByInverses]]
    // 4. Inverse existence: [[closedByInverse]]
    //
    // This direction is quite painful to prove. Each step is presented in its own lemma for easier legibility.
    have(subgroupConditions |- subgroup(H, G, *)) subproof {
      assume(subgroupConditions)
      have(binaryOperation(H, ★) /\ associativityAxiom(H, ★) /\ identityExistence(H, ★) /\ inverseExistence(H, ★)) by RightAnd(
        subgroupConditionsBinaryRelation,
        subgroupConditionsAssociativity,
        subgroupConditionsIdentityExistence,
        subgroupConditionsInverseExistence
      )
      have(group(H, ★)) by Tautology.from(lastStep, group.definition of (G -> H, * -> ★))
      thenHave(group(G, *) /\ subset(H, G) /\ group(H, ★)) by Tautology
      have(thesis) by Tautology.from(lastStep, subgroup.definition)
    }
    val backward = thenHave(subgroupConditions ==> subgroup(H, G, *)) by Restate

    have(thesis) by RightIff(forward, backward)
  }

  // TODO Trivial subgroup

  //
  // 3. Homomorphisms
  //

  // Extra group composition law
  val ** = variable

  /**
   * Definition --- A group homomorphism is a mapping `f: G -> H` from structures `G` and `H` equipped with binary operations `*` and `★` respectively,
   * such that for all `x, y ∈ G`, we have* `f(x * y) = f(x) ** f(y)`.
   *
   * In the following, "homomorphism" always stands for "group homomorphism", i.e. `(G, *)` and `(H, **)` are groups.
   */
  val homomorphism = DEF(f, G, *, H, **) --> group(G, *) /\ group(H, **) /\ functionFrom(f, G, H) /\ ∀(x, x ∈ G ==> ∀(y, y ∈ G ==> (app(f, op(x, *, y)) === op(app(f, x), **, app(f, y)))))

  /**
   * Lemma --- Practical reformulation of the homomorphism definition.
   */
  val homomorphismApplication = Lemma(
    (homomorphism(f, G, *, H, **), x ∈ G, y ∈ G) |- app(f, op(x, *, y)) === op(app(f, x), **, app(f, y))
  ) {
    assume(homomorphism(f, G, *, H, **))
    have(∀(x, x ∈ G ==> ∀(y, y ∈ G ==> (app(f, op(x, *, y)) === op(app(f, x), **, app(f, y)))))) by Tautology.from(homomorphism.definition)
    thenHave(x ∈ G ==> ∀(y, y ∈ G ==> (app(f, op(x, *, y)) === op(app(f, x), **, app(f, y))))) by InstantiateForall(x)
    thenHave((x ∈ G) |- ∀(y, y ∈ G ==> (app(f, op(x, *, y)) === op(app(f, x), **, app(f, y))))) by Restate
    thenHave((x ∈ G) |- y ∈ G ==> (app(f, op(x, *, y)) === op(app(f, x), **, app(f, y)))) by InstantiateForall(y)
    thenHave(thesis) by Restate
  }

  /**
   * Lemma --- If `f` is a homomorphism, then `f(x) ∈ H` for all `x ∈ G`.
   */
  private val homomorphismAppInH = Lemma(
    (homomorphism(f, G, *, H, **), x ∈ G) |- app(f, x) ∈ H
  ) {
    have(homomorphism(f, G, *, H, **) |- functionFrom(f, G, H)) by Tautology.from(homomorphism.definition)
    have(thesis) by Cut(
      lastStep,
      functionAppInCodomain of (VariableLabel("t") -> x, VariableLabel("x") -> G, y -> H)
    )
  }

  /**
   * Theorem --- If `f` is a group-homomorphism between `G` and `H`, then `f(e_G) = e_H`.
   */
  val homomorphismMapsIdentityToIdentity = Theorem(
    homomorphism(f, G, *, H, **) |- app(f, identity(G, *)) === identity(H, **)
  ) {
    val e = identity(G, *)

    val groupG = have(homomorphism(f, G, *, H, **) |- group(G, *)) by Tautology.from(homomorphism.definition)
    val groupH = have(homomorphism(f, G, *, H, **) |- group(H, **)) by Tautology.from(homomorphism.definition)

    val identityInG = have(homomorphism(f, G, *, H, **) |- e ∈ G) by Cut(groupG, identityInGroup)
    val appInH = have(homomorphism(f, G, *, H, **) |- app(f, e) ∈ H) by Cut(identityInG, homomorphismAppInH of (x -> e))

    // 0. e * e = e (to apply substitution)
    have(group(G, *) |- op(e, *, e) === e) by Cut(
      identityInGroup,
      identityIdempotence of (x -> e)
    )
    val eq0 = have(homomorphism(f, G, *, H, **) |- op(e, *, e) === e) by Cut(groupG, lastStep)

    // 1. f(e * e) = f(e)
    have(app(f, e) === app(f, e)) by RightRefl
    thenHave(op(e, *, e) === e |- app(f, op(e, *, e)) === app(f, e)) by RightSubstEq(
      List((op(e, *, e), e)),
      lambda(z, app(f, z) === app(f, e))
    )
    val eq1 = have(homomorphism(f, G, *, H, **) |- app(f, op(e, *, e)) === app(f, e)) by Cut(eq0, lastStep)

    // 2. f(e * e) = f(e) ** f(e)
    val eq2 = have(homomorphism(f, G, *, H, **) |- app(f, op(e, *, e)) === op(app(f, e), **, app(f, e))) by Cut(
      identityInG,
      homomorphismApplication of (x -> e, y -> e)
    )

    // 3. f(e) ** f(e) = f(e)
    val eq3 = have(homomorphism(f, G, *, H, **) |- op(app(f, e), **, app(f, e)) === app(f, e)) by Equalities(eq1, eq2)

    // Conclude by idempotence
    have((homomorphism(f, G, *, H, **), app(f, e) ∈ H) |- (op(app(f, e), **, app(f, e)) === app(f, e)) <=> (app(f, e) === identity(H, **))) by Cut(
      groupH,
      identityIdempotence of (x -> app(f, e), G -> H, * -> **)
    )
    have(homomorphism(f, G, *, H, **) |- (op(app(f, e), **, app(f, e)) === app(f, e)) <=> (app(f, e) === identity(H, **))) by Cut(
      appInH,
      lastStep
    )

    have(thesis) by Tautology.from(lastStep, eq3)
  }

  /**
   * Theorem --- If `f: G -> H` is a group homomorphism, then `f(inverse(x, G, *)) = inverse(f(x), H, **)`.
   */
  val homomorphismMapsInverseToInverse = Theorem(
    (homomorphism(f, G, *, H, **), x ∈ G) |- app(f, inverse(x, G, *)) === inverse(app(f, x), H, **)
  ) {
    assume(homomorphism(f, G, *, H, **))
    assume(x ∈ G)

    val groupG = have(group(G, *)) by Tautology.from(homomorphism.definition)
    val groupH = have(group(H, **)) by Tautology.from(homomorphism.definition)

    val eG = identity(G, *)
    val eH = identity(H, **)
    val i = inverse(x, G, *)
    val iInG = have(i ∈ G) by Cut(groupG, inverseInGroup)

    // 1. f(x * inverse(x)) = f(x) f(inverse(x))
    val eq1 = have(app(f, op(x, *, i)) === op(app(f, x), **, app(f, i))) by Cut(
      iInG,
      homomorphismApplication of (y -> i)
    )

    // 2. f(x * inverse(x)) = f(e)
    val cancellation = have(op(x, *, i) === eG) by Tautology.from(
      groupG,
      inverseCancellation
    )

    have(app(f, op(x, *, i)) === app(f, op(x, *, i))) by RightRefl
    thenHave((op(x, *, i) === eG) |- (app(f, op(x, *, i)) === app(f, eG))) by RightSubstEq(
      List((op(x, *, i), eG)),
      lambda(z, app(f, op(x, *, i)) === app(f, z))
    )

    val eq2 = have(app(f, op(x, *, i)) === app(f, eG)) by Cut(cancellation, lastStep)

    // 3. f(e) = e'
    val eq3 = have(app(f, eG) === eH) by Tautology.from(homomorphismMapsIdentityToIdentity)

    // 4. f(x)f(inverse(x)) = e'
    val eq4 = have(op(app(f, x), **, app(f, i)) === eH) by Equalities(eq1, eq2, eq3)

    // Conclude
    val conclusion = have((app(f, i) ∈ H) |- (app(f, i) === inverse(app(f, x), H, **))) by Tautology.from(
      groupH,
      inverseTest of (G -> H, * -> **, x -> app(f, x), y -> app(f, i)),
      eq4,
      homomorphismAppInH
    )
    have(app(f, i) ∈ H) by Cut(iInG, homomorphismAppInH of (x -> i))

    have(thesis) by Cut(lastStep, conclusion)
  }

  // TODO Homomorphism composition once we have function composition

  /**
   * Kernel uniqueness --- The kernel of a homomorphism is well-defined.
   */
  val kernelUniqueness = Theorem(
    homomorphism(f, G, *, H, **) |- ∃!(z, ∀(t, (t ∈ z) <=> (t ∈ G /\ (app(f, t) === identity(H, **)))))
  ) {
    // We apply the comprehension axiom here.
    // It might seem odd that the homomorphism assumption is not needed for the set to be defined,
    // but remember that [[app]] and [[identity]] default to the empty set when the assumptions are not met.
    // We add the assumption of `f` being a homomorphism to discard any value when the assumptions do not hold.
    have(∃!(z, ∀(t, (t ∈ z) <=> (t ∈ G /\ (app(f, t) === identity(H, **)))))) by UniqueComprehension(
      G,
      lambda(Seq(t, G), app(f, t) === identity(H, **))
    )
    thenHave(thesis) by Weakening
  }

  /**
   * Kernel --- The kernel of a homomorphism `f: G -> H` is the set of elements `t ∈ G` such that `f(t) = e_H`.
   */
  val kernel = DEF(f, G, *, H, **) --> TheConditional(z, ∀(t, (t ∈ z) <=> (t ∈ G /\ (app(f, t) === identity(H, **)))))(kernelUniqueness)

  // Shortcut alias
  private val K = kernel(f, G, *, H, **)

  /**
   * Lemma --- Reformulation of the kernel definition.
   */
  private val kernelDef = Lemma(
    homomorphism(f, G, *, H, **) |- (x ∈ K) <=> (x ∈ G /\ (app(f, x) === identity(H, **)))
  ) {
    assume(homomorphism(f, G, *, H, **))
    have(∀(t, (t ∈ K) <=> (t ∈ G /\ (app(f, t) === identity(H, **))))) by Definition(kernel, kernelUniqueness)(f, G, *, H, **)
    thenHave(thesis) by InstantiateForall(x)
  }

  /**
   * Lemma --- The kernel is closed by products, i.e. if `x, y ∈ K`, then `x * y ∈ K`.
   */
  val kernelIsClosedByProducts = Lemma(
    (homomorphism(f, G, *, H, **), x ∈ K, y ∈ K) |- op(x, *, y) ∈ K
  ) {
    assume(homomorphism(f, G, *, H, **))
    assume(x ∈ K)
    assume(y ∈ K)

    val elemInG = have(x ∈ G) by Tautology.from(kernelDef)

    val groupG = have(group(G, *)) by Tautology.from(homomorphism.definition)
    val groupH = have(group(H, **)) by Tautology.from(homomorphism.definition)

    val e = identity(H, **)
    val eInH = have(e ∈ H) by Cut(groupH, identityInGroup of (G -> H, * -> **))

    // 1. f(x) ** f(y) = f(x * y)
    val eq1 = have(app(f, op(x, *, y)) === op(app(f, x), **, app(f, y))) by Tautology.from(
      homomorphismApplication,
      elemInG,
      elemInG of (x -> y)
    )

    // 2. f(x) ** f(y) = e ** e
    val appValue = have(app(f, x) === e) by Tautology.from(kernelDef)
    have(op(app(f, x), **, app(f, y)) === op(app(f, x), **, app(f, y))) by RightRefl
    thenHave((app(f, x) === e, app(f, y) === e) |- op(app(f, x), **, app(f, y)) === op(e, **, e)) by RightSubstEq(
      List((app(f, x), e), (app(f, y), e)),
      lambda(Seq(a, b), op(app(f, x), **, app(f, y)) === op(a, **, b))
    )

    val eq2 = have(op(app(f, x), **, app(f, y)) === op(e, **, e)) by Tautology.from(
      lastStep,
      appValue,
      appValue of (x -> y)
    )

    // 3. e ** e = e
    val eq3 = have(op(e, **, e) === e) by Tautology.from(
      identityNeutrality of (G -> H, * -> **, x -> e),
      groupH,
      eInH
    )

    // 4. f(x * y) = e
    val eq4 = have(app(f, op(x, *, y)) === e) by Equalities(eq1, eq2, eq3)

    // Conclude that x * y ∈ K
    have(op(x, *, y) ∈ G) by Tautology.from(
      groupG,
      elemInG,
      elemInG of (x -> y),
      groupIsClosedByProduct
    )

    have(op(x, *, y) ∈ G /\ (app(f, op(x, *, y)) === e)) by RightAnd(lastStep, eq4)
    have(thesis) by Tautology.from(lastStep, kernelDef of (x -> op(x, *, y)))
  }

  /**
   * Lemma --- The kernel is closed by inversion, i.e. if `x ∈ K` then `inverse(x, G, *) ∈ K`.
   */
  val kernelIsClosedByInversion = Lemma(
    (homomorphism(f, G, *, H, **), x ∈ K) |- inverse(x, G, *) ∈ K
  ) {
    assume(homomorphism(f, G, *, H, **))
    assume(x ∈ K)

    val groupG = have(group(G, *)) by Tautology.from(homomorphism.definition)
    val groupH = have(group(H, **)) by Tautology.from(homomorphism.definition)
    val elemInG = have(x ∈ G) by Tautology.from(kernelDef)

    val e = identity(H, **)
    val appValue = have(app(f, x) === e) by Tautology.from(kernelDef)

    // 1. f(inverse(x)) = inverse(f(x)) = inverse(e)
    have(app(f, inverse(x, G, *)) === inverse(app(f, x), H, **)) by Tautology.from(
      homomorphismMapsInverseToInverse,
      elemInG
    )
    thenHave((app(f, x) === e) |- (app(f, inverse(x, G, *)) === inverse(e, H, **))) by RightSubstEq(
      List((app(f, x), e)),
      lambda(z, app(f, inverse(x, G, *)) === inverse(z, H, **))
    )

    val eq1 = have(app(f, inverse(x, G, *)) === inverse(e, H, **)) by Cut(appValue, lastStep)

    // 2. inverse(e) = e
    val eq2 = have(inverse(e, H, **) === e) by Cut(groupH, inverseOfIdentityIsIdentity of (G -> H, * -> **))

    // 3. Conclude
    val eq3 = have(app(f, inverse(x, G, *)) === e) by Equalities(eq1, eq2)
    have(inverse(x, G, *) ∈ G) by Tautology.from(
      groupG,
      elemInG,
      inverseInGroup
    )

    have((inverse(x, G, *) ∈ G) /\ (app(f, inverse(x, G, *)) === e)) by RightAnd(lastStep, eq3)

    have(thesis) by Tautology.from(lastStep, kernelDef of (x -> inverse(x, G, *)))
  }

  /**
   * Theorem --- The kernel of a homomorphism `f: G -> H` is a subgroup of `G`.
   */
  val kernelIsSubgroup = Theorem(
    homomorphism(f, G, *, H, **) |- subgroup(kernel(f, G, *, H, **), G, *)
  ) {
    assume(homomorphism(f, G, *, H, **))
    val groupG = have(group(G, *)) by Tautology.from(homomorphism.definition)

    // We show that the kernel satisfies all requirements of [[subgroupTest]]
    have((x ∈ K) ==> (x ∈ G)) by Tautology.from(kernelDef)
    thenHave(∀(x, x ∈ K ==> x ∈ G)) by RightForall
    val kernelIsSubset = have(subset(K, G)) by Tautology.from(lastStep, subsetAxiom of (x -> K, y -> G))

    // 1. kernel != ∅
    have(identity(G, *) ∈ G) by Cut(groupG, identityInGroup)
    have(identity(G, *) ∈ G /\ (app(f, identity(G, *)) === identity(H, **))) by RightAnd(
      lastStep,
      homomorphismMapsIdentityToIdentity
    )
    have(identity(G, *) ∈ K) by Tautology.from(
      lastStep,
      kernelDef of (x -> identity(G, *))
    )
    val condition1 = have(K !== ∅) by Cut(lastStep, setWithElementNonEmpty of (y -> identity(G, *), x -> K))

    // 2. The kernel is closed by products
    have((x ∈ K /\ y ∈ K) ==> op(x, *, y) ∈ K) by Restate.from(kernelIsClosedByProducts)
    thenHave(∀(y, (x ∈ K /\ y ∈ K) ==> op(x, *, y) ∈ K)) by RightForall
    val condition2 = thenHave(∀(x, ∀(y, (x ∈ K /\ y ∈ K) ==> op(x, *, y) ∈ K))) by RightForall

    // 3. The kernel is closed by inversion
    have((x ∈ K) ==> (inverse(x, G, *) ∈ K)) by Restate.from(kernelIsClosedByInversion)
    val condition3 = thenHave(∀(x, (x ∈ K) ==> (inverse(x, G, *) ∈ K))) by RightForall

    // Conclude
    have((K !== ∅) /\ ∀(x, ∀(y, (x ∈ K /\ y ∈ K) ==> op(x, *, y) ∈ K)) /\ ∀(x, (x ∈ K) ==> (inverse(x, G, *) ∈ K))) by RightAnd(
      condition1,
      condition2,
      condition3
    )

    have(subgroup(K, G, *)) by Tautology.from(
      lastStep,
      subgroupTest of (H -> K),
      groupG,
      kernelIsSubset
    )
  }

  // TODO Kernel injectivity
  // TODO Image is subgroup

  /**
   * Isomorphism --- An isomorphism `f: G -> H` is a bijective homomorphism.
   *
   * In some sense, isomorphic groups are equivalent, up to relabelling their elements.
   */
  val isomorphism = DEF(f, G, *, H, **) --> homomorphism(f, G, *, H, **) /\ bijective(f, G, H)

  /**
   * Automorphism --- An automorphism is an isomorphism from a group to itself.
   */
  val automorphism = DEF(f, G, *) --> isomorphism(f, G, *, G, *)
}
