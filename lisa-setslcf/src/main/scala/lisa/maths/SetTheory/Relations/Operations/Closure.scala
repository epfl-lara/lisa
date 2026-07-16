package lisa.maths.SetTheory.Relations
package Operations

import lisa.maths.Quantifiers
import lisa.maths.Quantifiers.∃!
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
  private val R, Q, Q_, S = variable[Ind]
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
   *
   * Proof sketch:
   *   Let φ(Q) = R ⊆ Q ∧ reflexive(Q)(X) ∧ ∀(Q', reflexive(Q')(X) ∧ R ⊆ Q' ⇒ Q ⊆ Q').
   *   The closure is ε(Q, φ(Q)) by definition of `closure`.
   *   We show R ∪ Δ(X) satisfies φ:
   *     - R ⊆ R ∪ Δ(X) by union-left-subset
   *     - reflexive(R ∪ Δ(X))(X) by reflexiveClosureIsReflexive
   *     - For any Q' with reflexive(Q')(X) and R ⊆ Q':
   *         Δ(X) ⊆ Q' (by IdentityRelation.subset)
   *         R ∪ Δ(X) ⊆ Q' (by leftUnionSubset)
   *   We show φ has a unique witness:
   *     If φ(Q) and φ(Q'), then Q ⊆ Q' (Q is minimal for Q') and Q' ⊆ Q.
   *   So ∃!(Q, φ(Q)), and since φ(R ∪ Δ(X)), we get R ∪ Δ(X) = ε(Q, φ(Q)).
   */
  val reflexiveClosureValid = Theorem(
    reflexiveClosure(R)(X) === closure(R)(λ(R, reflexive(R)(X)))
  ) {
    // The closure predicate: φ(Q) = R ⊆ Q ∧ reflexive(Q)(X) ∧ ∀(Q', reflexive(Q')(X) ∧ R ⊆ Q' ⇒ Q ⊆ Q')
    // After unfolding closure.definition and reflexiveClosure.definition

    // Step 1: R ∪ Δ(X) satisfies the minimality condition
    val satisfies = have(R ⊆ (R ∪ Δ(X)) /\ reflexive(R ∪ Δ(X))(X) /\ ∀(Q_, reflexive(Q_)(X) /\ (R ⊆ Q_) ==> ((R ∪ Δ(X)) ⊆ Q_))) subproof {
      val rSubset = have(R ⊆ (R ∪ Δ(X))) by Tautology.from(Union.leftSubset of (x := R, y := Δ(X)))
      val reflex = have(reflexive(R ∪ Δ(X))(X)) subproof {
        val rcIsReflex = have(reflexive(reflexiveClosure(R)(X))(X)) by Restate.from(reflexiveClosureIsReflexive)
        have(thesis) by Congruence.from(rcIsReflex, reflexiveClosure.definition of (R := R, X := X))
      }
      val minimal = have(∀(Q_, reflexive(Q_)(X) /\ (R ⊆ Q_) ==> ((R ∪ Δ(X)) ⊆ Q_))) subproof {
        assume(reflexive(Q_)(X))
        assume(R ⊆ Q_)
        val deltaSubQ = have(Δ(X) ⊆ Q_) by Tautology.from(
          IdentityRelation.subset of (R := Q_)
        )
        have(thesis) by Tautology.from(
          deltaSubQ,
          Union.leftUnionSubset of (x := R, y := Δ(X), z := Q_)
        )
      }
      have(thesis) by Tautology.from(rSubset, reflex, minimal)
    }

    // Step 2: Uniqueness — any two solutions to φ must be equal
    // Using Q and S as the two distinct solutions; Q_ as bound variable inside minimality
    val unique = have(
      (R ⊆ Q /\ reflexive(Q)(X) /\ ∀(Q_, reflexive(Q_)(X) /\ (R ⊆ Q_) ==> (Q ⊆ Q_)),
       R ⊆ S /\ reflexive(S)(X) /\ ∀(Q_, reflexive(Q_)(X) /\ (R ⊆ Q_) ==> (S ⊆ Q_)))
      |- (Q === S)
    ) subproof {
      assume(R ⊆ Q /\ reflexive(Q)(X) /\ ∀(Q_, reflexive(Q_)(X) /\ (R ⊆ Q_) ==> (Q ⊆ Q_)))
      assume(R ⊆ S /\ reflexive(S)(X) /\ ∀(Q_, reflexive(Q_)(X) /\ (R ⊆ Q_) ==> (S ⊆ Q_)))
      // Q ⊆ S from Q's minimality applied to S
      val qSubS = have(Q ⊆ S) subproof {
        have(∀(Q_, reflexive(Q_)(X) /\ (R ⊆ Q_) ==> (Q ⊆ Q_))) by Tautology
        thenHave(reflexive(S)(X) /\ (R ⊆ S) ==> (Q ⊆ S)) by InstantiateForall(S)
        have(thesis) by Tautology
      }
      // S ⊆ Q from S's minimality applied to Q
      val sSubQ = have(S ⊆ Q) subproof {
        have(∀(Q_, reflexive(Q_)(X) /\ (R ⊆ Q_) ==> (S ⊆ Q_))) by Tautology
        thenHave(reflexive(Q)(X) /\ (R ⊆ Q) ==> (S ⊆ Q)) by InstantiateForall(Q)
        have(thesis) by Tautology
      }
      have(thesis) by Tautology.from(qSubS, sSubQ, Subset.doubleInclusion of (x := Q, y := S))
    }

    // Step 3: ∃!(Q, φ(Q))
    val existsOne = have(∃!(Q, R ⊆ Q /\ reflexive(Q)(X) /\ ∀(Q_, reflexive(Q_)(X) /\ (R ⊆ Q_) ==> (Q ⊆ Q_)))) subproof {
      val exWitness = have(∃(Q, R ⊆ Q /\ reflexive(Q)(X) /\ ∀(Q_, reflexive(Q_)(X) /\ (R ⊆ Q_) ==> (Q ⊆ Q_)))) subproof {
        have(thesis) by RightExists(satisfies)
      }
      // For uniqueness: any two elements satisfying φ are equal
      // unique gives: (φ(Q), φ(S)) |- Q === S, so generalize over Q and S
      val allUnique = have(∀(Q, ∀(S, (R ⊆ Q /\ reflexive(Q)(X) /\ ∀(Q_, reflexive(Q_)(X) /\ (R ⊆ Q_) ==> (Q ⊆ Q_))) /\ (R ⊆ S /\ reflexive(S)(X) /\ ∀(Q_, reflexive(Q_)(X) /\ (R ⊆ Q_) ==> (S ⊆ Q_))) ==> (Q === S)))) subproof {
        have(thesis) by Generalize(unique)
      }
      have(thesis) by Tautology.from(
        exWitness,
        allUnique,
        Quantifiers.existsOneAlternativeDefinition of (P := λ(Q, R ⊆ Q /\ reflexive(Q)(X) /\ ∀(Q_, reflexive(Q_)(X) /\ (R ⊆ Q_) ==> (Q ⊆ Q_))))
      )
    }

    // Step 4: since φ(R ∪ Δ(X)) and ∃!(Q, φ(Q)), we have R ∪ Δ(X) === ε(Q, φ(Q))
    val epsilonEq = have((R ∪ Δ(X)) === ε(Q, R ⊆ Q /\ reflexive(Q)(X) /\ ∀(Q_, reflexive(Q_)(X) /\ (R ⊆ Q_) ==> (Q ⊆ Q_)))) subproof {
      have((R ∪ Δ(X)) === ε(Q, R ⊆ Q /\ reflexive(Q)(X) /\ ∀(Q_, reflexive(Q_)(X) /\ (R ⊆ Q_) ==> (Q ⊆ Q_)))) by Tautology.from(
        existsOne,
        satisfies,
        Quantifiers.existsOneEpsilonUniqueness of (
          P := λ(Q, R ⊆ Q /\ reflexive(Q)(X) /\ ∀(Q_, reflexive(Q_)(X) /\ (R ⊆ Q_) ==> (Q ⊆ Q_))),
          y := (R ∪ Δ(X))
        )
      )
    }

    // Step 5: rewrite using definitions
    // reflexiveClosure(R)(X) = R ∪ Δ(X) and closure(R)(λ(R, reflexive(R)(X))) = ε(Q, ...)
    have(thesis) by Congruence.from(
      epsilonEq,
      reflexiveClosure.definition of (R := R, X := X),
      closure.definition of (R := R, P := λ(R, reflexive(R)(X)))
    )
  }

  /**
   * TODO: Define the transitive closure and transitive, reflexive closure.
   */
}
