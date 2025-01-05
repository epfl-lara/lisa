package lisa.maths.topology
import lisa.maths.settheory.*
import lisa.maths.settheory.SetTheory.*

object Topology extends lisa.Main {

  private val X, T = variable
  private val S, A, B, Y = variable

  /**
   * The ground set X cannot be empty
   */
  val nonEmpty = DEF(X) --> !(X === ∅)

  /**
   * Elements of T are subsets of X
   */
  val setOfSubsets = DEF(X, T) --> T ⊆ powerSet(X)

  /**
   * X and the empty set ∅ belong to T
   */
  val containsExtremes = DEF(X, T) --> ∅ ∈ T /\ X ∈ T

  /**
   * The union of any (finite or infinite) number of sets in T belongs to T
   */
  val containsUnion = DEF(T) --> forall(Y, (Y ⊆ T) ==> (union(Y) ∈ T))

  /**
   * The intersection of two sets in T belongs to T
   */
  val containsIntersection = DEF(T) --> forall(A, forall(B, (A ∈ T /\ B ∈ T) ==> A ∩ B ∈ T))

  /**
   * By Definition 1.1.1 from the book the pair (X, T) is called a topological space.
   * Or T is a topology on X
   */
  val topology = DEF(X, T) --> nonEmpty(X) /\ setOfSubsets(X, T) /\ containsExtremes(X, T) /\ containsUnion(T) /\ containsIntersection(T)
}
