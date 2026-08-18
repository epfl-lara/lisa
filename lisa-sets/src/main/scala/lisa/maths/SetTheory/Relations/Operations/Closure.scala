package lisa.maths.SetTheory.Relations
package Operations

import lisa.maths.SetTheory.Base.Predef._
import lisa.maths.SetTheory.Relations.Predef._

import Examples.IdentityRelation
import Examples.IdentityRelation.Δ

/**
 * The closure of a relation `R` with regards to a property `P` is the smallest
 * relation `Q ⊇ R` that has property `P`.
 *
 * Some closures have a closed form: for example, the
 * [[Closure.reflexiveClosure]] of `R` is `R ∪ Δ(R)`.
 */
object Closure extends lisa.Main {

  private val x, y = variable[Ind]
  private val X = variable[Ind]
  private val R, Q, Q_ = variable[Ind]
  private val P = variable[Ind >>: Prop]

  /**
   * Definition --- The closure of `R` with regards to `P` is the smallest relation
   * `Q ⊇ R` that has property `P`.
   */
  val closure = DEF(λ(R, λ(P, ε(Q, R ⊆ Q /\ P(Q) /\ (∀(Q_, P(Q_) /\ (R ⊆ Q_) ==> Q ⊆ Q_))))))

  /**
   * Reflexive closure --- The reflexive closure of a relation `R` on `X` is
   * the smallest reflexive relation on `X` containing `R`, i.e.,
   * `reflexiveClosure(R, X) = R ∪ Δ(X)`.
   */
  val reflexiveClosure = DEF(λ(R, λ(X, R ∪ Δ(X))))

  /**
   * Theorem --- The reflexive closure of any relation `R` is reflexive.
   */
  val reflexiveClosureIsReflexive = Theorem(
    reflexive(reflexiveClosure(R)(X))(X)
  ) {
    have(Δ(X) ⊆ (R ∪ Δ(X))) by Tautology.from(Union.rightSubset of (x := R, y := Δ(X)))
    thenHave(Δ(X) ⊆ reflexiveClosure(R)(X)) by Substitute(reflexiveClosure.definition)
    thenHave(thesis) by Tautology.fromLastStep(IdentityRelation.subset of (R := reflexiveClosure(R)(X)))
  }

  /**
   * Theorem --- The [[reflexiveClosure]] of `R` as defined above is indeed the
   * smallest reflexive relation containing `R`.
   */
  val reflexiveClosureValid = Theorem(
    reflexiveClosure(R)(X) === closure(R)(λ(R, reflexive(R)(X)))
  ) {
    sorry
  }

  /**
   * TODO: Define the transitive closure and transitive, reflexive closure.
   */
}
