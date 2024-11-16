package Topology

import lisa.maths.topology.*
import lisa.maths.settheory.*

object Instances extends lisa.Main {
  // var defs
  private val X, T = variable
  private val S, A, B, Y = variable

  val discreteTopology = DEF(X, T) --> (T === powerSet(X))
  val indiscreteTopology = DEF(X, T) --> ∅ ∈ T /\ X ∈ T /\ forall(S, in(S, T) ==> ((S === X) \/ (S === ∅)))

  val discreteIsTopology = Theorem(
    discreteTopology(X, T) ==> Topology.topology(X, T)
  ) {
    sorry
  }

  val indiscreteIsTopology = Theorem(
    indiscreteTopology(X, T) ==> Topology.topology(X, T)
  ) {
    sorry
  }
}
