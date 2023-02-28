package lisa.mathematics

import lisa.automation.kernel.SimpleSimplifier.Substitution
import lisa.automation.kernel.OLPropositionalSolver.Tautology
import lisa.mathematics.GroupTheory.*
import lisa.mathematics.SetTheory.*

/**
 * Group theory, following Chapter 2 of S. Lang "Undergraduate Algebra".
 *
 * Book : [[https://link.springer.com/book/10.1007/978-1-4684-9234-7]]
 */
object GroupTheory extends lisa.Main {

  private val G, * = variable
  private val x, y, z = variable
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
  val identityExistence = DEF(G, *) --> ∃(e, G, isNeutral(G, *, e))

  /**
   * Inverse existence --- For all `x` in G, there exists an element `y` in G such that `x * y = y * x = e`.
   */
  val inverseExistence = DEF(G, *) --> ∀(x, G, ∃(y, G, isNeutral(G, *, op(*, x, y)) /\ isNeutral(G, *, op(*, y, x))))

  /**
   * Group --- A group (G, *) is a set along with a law of composition `*`, satisfying [[associativity]], [[identityExistence]]
   * and [[inverseExistence]].
   */
  val group = DEF(G, *) --> binaryRelation(G, *) /\ associativity(G, *) /\ identityExistence(G, *) /\ inverseExistence(G, *)
}
