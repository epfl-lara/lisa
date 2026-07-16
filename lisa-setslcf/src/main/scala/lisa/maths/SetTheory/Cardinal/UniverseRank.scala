package lisa.maths.SetTheory.Cardinal

import lisa.maths.SetTheory.Ordinals.Ordinal._

import Universe._

object UniverseRank extends lisa.Main:
  private val x, k = variable[Ind]
  private val U, U1, U2 = variable[Ind]

  /**
   * Von Neumann hierarchy
   */
  val V = constant[Ind >>: Ind]

  /**
   * The Level (or Rank) of a Universe.
   * If U = V_k, then level(U) = k.
   * Implementation: level(U) is the set of all ordinals contained in U.
   * Since U is transitive, this set is exactly the ordinal k.
   */
  val level = DEF(λ(U, ε(k, ∀(x, x ∈ k <=> (x ∈ U /\ ordinal(x))))))

  /**
   * The level of a Universe is an Ordinal (actually an Inaccessible Cardinal).
   */
  val levelIsOrdinal = Theorem(
    isUniverse(U) ==> ordinal(level(U))
  ) {
    sorry
  }

  /**
   * Axiom: Universes are nested.
   * Based on the fact that universes correspond to V_k where k are cardinals,
   * and cardinals are totally ordered.
   */
  val universesAreNested = Theorem(
    (isUniverse(U1), isUniverse(U2)) |- (U1 ⊆ U2) \/ (U2 ⊆ U1)
  ) {
    sorry
  }
