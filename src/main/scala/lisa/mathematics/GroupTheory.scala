package lisa.mathematics

import lisa.automation.grouptheory.GroupTheoryTactics.ExistenceAndUniqueness
import lisa.automation.kernel.SimpleSimplifier.Substitution
import lisa.automation.kernel.OLPropositionalSolver.Tautology
import lisa.mathematics.FirstOrderLogic.equalityTransitivity
import lisa.mathematics.GroupTheory.*
import lisa.mathematics.SetTheory.*
import lisa.utils.KernelHelpers.{∀, ∃}

/**
 * Group theory, following Chapter 2 of S. Lang "Undergraduate Algebra".
 *
 * Book : [[https://link.springer.com/book/10.1007/978-1-4684-9234-7]]
 */
object GroupTheory extends lisa.Main {

  private val G, * = variable
  private val x, y, z = variable
  private val u, v, w = variable
  private val e, f = variable

  /**
   * Bounded quantifiers --- These express the usual `∀x ∈ G ϕ` and `∃x ∈ G ϕ`, for some variables (sets) `x` and `G`, which
   * are shorthands for `∀x (x ∈ G ==> ϕ)` and `∃x (x ∈ G /\ ϕ)`, respectively.
   */
  def ∀(x: VariableLabel, range: VariableLabel, inner: Formula): Formula = forall(x, in(x, range) ==> inner)

  def ∃(x: VariableLabel, range: VariableLabel, inner: Formula): Formula = exists(x, in(x, range) /\ inner)

  def ∃!(x: VariableLabel, range: VariableLabel, inner: Formula): Formula = existsOne(x, in(x, range) /\ inner)

  /**
   * Binary relation --- `*` is a binary relation on `G` if it associates to each pair of elements of `G`
   * a unique element in `G`. In other words, `*` is a function `G x G -> G`.
   */
  val binaryRelation = DEF(G, *) --> functionFrom(*, cartesianProduct(G, G), G)

  /**
   * Shorthand for `x * y`.
   */
  val op = DEF(*, x, y) --> app(*, pair(x, y))

  /**
   * Associativity --- `*` is associative (in G) if `(x * y) * z = x * (y * z)` for all `x, y, z` in G.
   */
  val associativity = DEF(G, *) -->
    ∀(x, G, ∀(y, G, ∀(z, G, op(*, op(*, x, y), z) === op(*, x, op(*, y, z)))))

  /**
   * Neutral element --- We say that an element `e` in G is neutral if `e * x = x * e = x` for all `x` in G.
   */
  val isNeutral = DEF(G, *, e) --> (in(e, G) /\ ∀(x, G, (op(*, e, x) === x) /\ (op(*, x, e) === x)))

  /**
   * Identity existence --- There exists a neutral element `e` in G.
   */
  val identityExistence = DEF(G, *) --> ∃(e, isNeutral(G, *, e))

  /**
   * Inverse existence --- For all `x` in G, there exists an element `y` in G such that `x * y = y * x = e`.
   */
  val inverseExistence = DEF(G, *) --> ∀(x, G, ∃(y, G, isNeutral(G, *, op(*, x, y)) /\ isNeutral(G, *, op(*, y, x))))

  /**
   * Group --- A group (G, *) is a set along with a law of composition `*`, satisfying [[associativity]], [[identityExistence]]
   * and [[inverseExistence]].
   */
  val group = DEF(G, *) --> binaryRelation(G, *) /\ associativity(G, *) /\ identityExistence(G, *) /\ inverseExistence(G, *)

  /**
   * Identity uniqueness --- In a group (G, *), an identity element is unique, i.e. if both `e * x = x * e = x` and
   * `f * x = x * f = x` for all `x`, then `e = f`.
   * This justifies calling `e` <i>the</i> identity element.
   */
  val identityUniqueness = Theorem(
    group(G, *) |- ∃!(e, isNeutral(G, *, e))
  ) {
    // We prove that if e and f are neutral elements then ef = f = e, where the first equality comes from e's left neutrality,
    // and the second equality from f's right neutrality
    val uniqueness = have((isNeutral(G, *, e), isNeutral(G, *, f)) |- (e === f)) subproof {
      // We prove that neutral elements are elements of G, such that * can be applied.
      val eMembership = have(isNeutral(G, *, e) |- in(e, G)) subproof {
        assume(isNeutral(G, *, e))
        have(thesis) by Tautology.from(isNeutral.definition)
      }
      val fMembership = have(isNeutral(G, *, f) |- in(f, G)) by Tautology.from(eMembership of e -> f)

      assume(isNeutral(G, *, e))
      assume(isNeutral(G, *, f))

      // First equality : ef = f
      have(∀(x, G, (op(*, e, x) === x) /\ (op(*, x, e) === x))) by Tautology.from(isNeutral.definition)
      thenHave(in(f, G) ==> ((op(*, e, f) === f) /\ (op(*, f, e) === f))) by InstantiateForall(f)
      val cut1 = thenHave(in(f, G) |- ((op(*, e, f) === f) /\ (op(*, f, e) === f))) by Restate

      have((op(*, e, f) === f) /\ (op(*, f, e) === f)) by Cut(fMembership, cut1)
      val firstEq = thenHave(op(*, e, f) === f) by Tautology

      // Second equality : ef = e
      val cut2 = have(in(e, G) |- ((op(*, f, e) === e) /\ (op(*, e, f) === e))) by InstFunSchema(Map(e -> f, f -> e))(cut1)
      have((op(*, f, e) === e) /\ (op(*, e, f) === e)) by Cut(eMembership, cut2)
      val secondEq = thenHave(op(*, e, f) === e) by Tautology

      val eqs = have((op(*, e, f) === f) /\ (op(*, e, f) === e)) by RightAnd(firstEq, secondEq)
      val cut3 = have(((op(*, e, f) === f) /\ (op(*, e, f) === e)) |- (e === f)) by Tautology.from(equalityTransitivity of (x -> f, y -> op(*, e, f), z -> e))
      have(e === f) by Cut(eqs, cut3)
    }

    val existence = have(group(G, *) |- ∃(e, isNeutral(G, *, e))) by Tautology.from(group.definition, identityExistence.definition)

    have(group(G, *) |- ∃!(e, isNeutral(G, *, e))) by ExistenceAndUniqueness(isNeutral(G, *, e))(existence, uniqueness)
  }

  /**
   * Theorem --- The inverse of an element `x` (i.e. `y` such that `x * y = y * x = e`) in `G` is unique.
   */
  val inverseUniqueness = Theorem(
    group(G, *) |- ∀(x, G, ∃!(y, G, isNeutral(G, *, op(*, x, y)) /\ isNeutral(G, *, op(*, y, x))))
  ) {
    have(group(G, *) |- ∀(x, G, ∃(y, G, isNeutral(G, *, op(*, x, y)) /\ isNeutral(G, *, op(*, y, x))))) by Tautology.from(group.definition, inverseExistence.definition)
    thenHave(group(G, *) |- (in(x, G) ==> ∃(y, G, isNeutral(G, *, op(*, x, y)) /\ isNeutral(G, *, op(*, y, x))))) by InstantiateForall(x)
    val existence = thenHave((group(G, *), in(x, G)) |- ∃(y, G, isNeutral(G, *, op(*, x, y)) /\ isNeutral(G, *, op(*, y, x)))) by Restate

    val phi = in(y, G) /\ (isNeutral(G, *, op(*, x, y)) /\ isNeutral(G, *, op(*, y, x)))
    val substPhi = substituteVariables(phi, Map[VariableLabel, Term](y -> z))

    val uniqueness = have((group(G, *), in(x, G), phi, substPhi) |- (y === z)) subproof {
      assume(group(G, *))
      assume(in(x, G))
      assume(phi)
      assume(substPhi)

      // We prove the following chain of equalities:
      //   z = (yx)z = y(xz) = y
      // where the first and last equalities come from neutrality, and the second equality from associativity

      // z = (yx)z
      have(∀(u, G, (op(*, op(*, y, x), u) === u) /\ (op(*, u, op(*, y, x)) === u))) by Tautology.from(isNeutral.definition of (e -> op(*, y, x)))
      thenHave(in(z, G) ==> ((op(*, op(*, y, x), z) === z) /\ (op(*, z, op(*, y, x)) === z))) by InstantiateForall(z)
      val eq1 = thenHave(op(*, op(*, y, x), z) === z) by Tautology

      // (yx)z = y(xz)
      have(∀(u, G, ∀(v, G, ∀(w, G, op(*, op(*, u, v), w) === op(*, u, op(*, v, w)))))) by Tautology.from(group.definition, associativity.definition)
      thenHave(in(y, G) ==> ∀(v, G, ∀(w, G, op(*, op(*, y, v), w) === op(*, y, op(*, v, w))))) by InstantiateForall(y)
      thenHave(∀(v, G, ∀(w, G, op(*, op(*, y, v), w) === op(*, y, op(*, v, w))))) by Tautology
      thenHave(in(x, G) ==> ∀(w, G, op(*, op(*, y, x), w) === op(*, y, op(*, x, w)))) by InstantiateForall(x)
      thenHave(∀(w, G, op(*, op(*, y, x), w) === op(*, y, op(*, x, w)))) by Tautology
      thenHave(in(z, G) ==> (op(*, op(*, y, x), z) === op(*, y, op(*, x, z)))) by InstantiateForall(z)
      val eq2 = thenHave(op(*, op(*, y, x), z) === op(*, y, op(*, x, z))) by Tautology

      // y(xz) = y
      have(∀(u, G, (op(*, op(*, x, z), u) === u) /\ (op(*, u, op(*, x, z)) === u))) by Tautology.from(isNeutral.definition of (e -> op(*, x, z)))
      thenHave(in(y, G) ==> ((op(*, op(*, x, z), y) === y) /\ (op(*, y, op(*, x, z)) === y))) by InstantiateForall(y)
      val eq3 = thenHave(op(*, y, op(*, x, z)) === y) by Tautology

      // z = y(xz)
      val eq4 = have(z === op(*, y, op(*, x, z))) by Tautology.from(
        eq1, eq2, equalityTransitivity of (x -> z, y -> op(*, op(*, y, x), z), z -> op(*, y, op(*, x, z)))
      )

      have(z === y) by Tautology.from(
        eq3, eq4, equalityTransitivity of (x -> z, y -> op(*, y, op(*, x, z)), z -> y)
      )
    }
    
    have((group(G, *), in(x, G)) |- ∃!(y, phi)) by ExistenceAndUniqueness.withParameters(phi, y, z)(existence, uniqueness)
    thenHave(group(G, *) |- (in(x, G) ==> ∃!(y, phi))) by Restate
    thenHave(thesis) by RightForall
  }
}
