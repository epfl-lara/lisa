package lisa.maths.SetTheory.Relations.Operations

import lisa.maths.SetTheory.Base.Predef.*
import lisa.maths.SetTheory.Relations.Definitions.*
import lisa.maths.SetTheory.Relations.Examples.IdentityRelation
import lisa.maths.SetTheory.Relations.Examples.IdentityRelation.Δ

/** The closure of a relation `ℛ` with regards to a property `P` is the smallest
  * relation `𝒬 ⊇ ℛ` that has property `P`.
  *
  * For example, the [[Closure.reflexiveClosure]] of `ℛ` can be computed as `ℛ ∪ Δ(ℛ)`.
  */
object Closure extends lisa.Main {

  private val x, y = variable[Ind]
  private val X = variable[Ind]
  private val ℛ, 𝒬, 𝒬_ = variable[Ind]
  private val P = variable[Ind >>: Prop]

  /** Definition --- The closure of `ℛ` with regards to `P` is the smallest relation
    * `𝒬 ⊇ ℛ` that has property `P`.
    */
  val closure = DEF(λ(ℛ, λ(P, ε(𝒬, ℛ ⊆ 𝒬 /\ P(𝒬) /\ (∀(𝒬_, P(𝒬_) /\ (ℛ ⊆ 𝒬_) ==> 𝒬 ⊆ 𝒬_))))))

  /** Reflexive closure --- The reflexive closure of a relation `ℛ` on `X` is
    * the smallest reflexive relation on `X` containing `ℛ`, i.e.,
    * `reflexiveClosure(ℛ, X) = ℛ ∪ Δ(X)`.
    */
  val reflexiveClosure = DEF(λ(ℛ, λ(X, ℛ ∪ Δ(X))))

  /** Theorem --- The reflexive closure of any relation `ℛ` is reflexive.
    */
  val reflexiveClosureIsReflexive = Theorem(
    reflexive(reflexiveClosure(ℛ)(X))(X)
  ) {
    have(Δ(X) ⊆ (ℛ ∪ Δ(X))) by Tautology.from(Union.rightSubset of (x := ℛ, y := Δ(X)))
    thenHave(Δ(X) ⊆ reflexiveClosure(ℛ)(X)) by Substitute(reflexiveClosure.definition)
    thenHave(thesis) by Tautology.fromLastStep(IdentityRelation.identityRelationSubset of (ℛ := reflexiveClosure(ℛ)(X)))
  }

  /**
    * Theorem --- The [[reflexiveClosure]] of `ℛ` as defined above is indeed the
    * smallest reflexive relation containing `ℛ`.
    */
  val reflexiveClosureValid = Theorem(
    reflexiveClosure(ℛ)(X) === closure(ℛ)(λ(ℛ, reflexive(ℛ)(X)))
  ) {
    sorry
  }

  /** TODO: Define the transitive closure and transitive, reflexive closure. */
}

