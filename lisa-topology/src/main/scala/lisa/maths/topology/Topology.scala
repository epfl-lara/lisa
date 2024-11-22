package lisa.maths.topology
import lisa.maths.settheory.*

object Topology extends lisa.Main {

  private val X, T = variable
  private val S, A, B, Y = variable

  /**
   * Bounded quantifiers --- These express the usual `∀x ∈ G ϕ` and `∃x ∈ G ϕ`, for some variables (sets) `x` and `G`, which
   * are shorthands for `∀x (x ∈ G ==> ϕ)` and `∃x (x ∈ G ==> ϕ)`, respectively.
   */
  def ∀(x: Variable, range: Variable, inner: Formula): Formula = forall(x, in(x, range) ==> inner)

  def ∃(x: Variable, range: Variable, inner: Formula): Formula = exists(x, in(x, range) ==> inner)

  def ∃!(x: Variable, range: Variable, inner: Formula): Formula = existsOne(x, in(x, range) ==> inner)

  /**
   * The ground set X cannot be empty
   */
  val nonEmpty = DEF(X) --> !(X === ∅)

  /**
   * All elements of T are subsets of X
   */
  val setOfSubsets = DEF(X, T) --> ∀(S, T, S ⊆ X)

  /**
   * X and the empty set ∅ belong to T
   */
  val containsExtremes = DEF(X, T) --> ∅ ∈ T /\ X ∈ T

  /**
   * The union of any (finite or infinite) number of sets in T belongs to T
   */
  val containsUnion = DEF(T) --> forall(Y, in(Y, powerSet(T)) ==> (union(Y) ∈ T))

  /**
   * The intersection of two sets in T belongs to T
   */
  val containsIntersection = DEF(T) --> ∀(A, T, ∀(B, T, union(unorderedPair(A, B)) ∈ T))

  /**
   * By Definition 1.1.1 from the book the pair (X, T) is called a topological space.
   * Or T is a topology on X
   */
  val topology = DEF(X, T) --> nonEmpty(X) /\ setOfSubsets(X, T) /\ containsExtremes(X, T) /\ containsUnion(T) /\ containsIntersection(T)
}
