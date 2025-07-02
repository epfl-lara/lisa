package lisa.maths.SetTheory.Order
package WellOrders

import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Functions
import lisa.maths.SetTheory.Functions.Predef.*

import Definitions.*
import WellOrder.*
import InitialSegment.*

import lisa.maths.Quantifiers.∃!

/**
  * Given a well-ordering `(A, <)`, one can build a function `g` by recursion over `A`
  * that satisfies the following formula:
  *
  *   `g(x) = F(g↾initialSegment(x, A, <))` for all `x ∈ A`
  *
  * where `F : 𝕍 -> 𝕍` is a class function, and `g↾initialSegment(x, A, <)`
  * denotes `g` restricted to the initial segment of `x` in `A`, i.e. `g`
  * restricted to `{y ∈ A | y < x}`.
  */
object WellOrderedRecursion extends lisa.Main {

  private val x, y, z = variable[Ind]
  private val A, B, X = variable[Ind]
  private val < = variable[Ind]
  private val f, g = variable[Ind]
  private val F = variable[Ind >>: Ind]
  private val G, G1, G2 = variable[Ind]
  private val ℛ = variable[Ind]
  private type set = Expr[Ind]

  extension (f: set) {
    def apply(x: set): set = app(f)(x)
  }

  context(wellOrdering(A)(<))

  /**
    * Well-ordered recursion function is unique --- If G `: A -> 𝕍` is obtained by
    * well-ordered recursion on a well-ordering `(A, <)`, then it is unique.
    */
  val recursionUniqueness = Theorem(
    (
      functionOn(G1)(A),
      ∀(x, x ∈ A ==> (G1(x) === F(G1↾initialSegment(x)(<)(A)))),
      functionOn(G2)(A),
      ∀(x, x ∈ A ==> (G2(x) === F(G2↾initialSegment(x)(<)(A))))
    ) |- G1 === G2
  ) {
    assume(wellOrdering(A)(<))

    assume(functionOn(G1)(A))
    assume(∀(x, x ∈ A ==> (G1(x) === F(G1↾initialSegment(x)(<)(A)))))
    thenHave(x ∈ A ==> (G1(x) === F(G1↾initialSegment(x)(<)(A)))) by InstantiateForall(x)
    val `G1(x)` = thenHave(x ∈ A |- G1(x) === F(G1↾initialSegment(x)(<)(A))) by Restate

    assume(functionOn(G2)(A))
    assume(∀(x, x ∈ A ==> (G2(x) === F(G2↾initialSegment(x)(<)(A)))))
    thenHave(x ∈ A ==> (G2(x) === F(G2↾initialSegment(x)(<)(A)))) by InstantiateForall(x)
    val `G2(x)` = thenHave(x ∈ A |- G2(x) === F(G2↾initialSegment(x)(<)(A))) by Restate

    // Let `S` be the set of elements such that `G1(x) ≠ G2(x)`. If `G1 ≠ G2` then this set is non-empty.
    val S = {x ∈ A | G1(x) ≠ G2(x)}
    val `x ∈ S` = have(x ∈ S <=> (x ∈ A) /\ (G1(x) ≠ G2(x))) by Tautology.from(
      Comprehension.membership of (y := A, φ := λ(x, G1(x) ≠ G2(x)))
    )

    // Assume that `S` is non-empty. Proceed by contradiction.
    have(S ≠ ∅ |- ⊥) subproof {
      assume(S ≠ ∅)

      // `S` has an `<`-least element `x`, by well-ordering.
      have(S ⊆ A) by Tautology.from(Comprehension.subset of (y := A, φ := λ(x, G1(x) ≠ G2(x))))
      thenHave(∃(x, x ∈ S /\ minimal(x)(S)(<))) by Tautology.fromLastStep(WellOrder.minimalElement of (B := S))

      // Notice that `G1` and `G2` agree on `initialSegment(x)(A)` by
      // `<`-minimality, since it is empty.
      val agreement = have((x ∈ S, minimal(x)(S)(<)) |- G1↾initialSegment(x)(A)(<) === G2↾initialSegment(x)(A)(<)) subproof {
        assume(x ∈ S)
        assume(minimal(x)(S)(<))

        have(∀(y, y ∈ S ==> (y, x) ∉ <)) by Congruence.from(minimal.definition of (A := S, ℛ := <))
        thenHave(y ∈ S ==> (y, x) ∉ <) by InstantiateForall(y)
        thenHave(y ∈ initialSegment(x)(A)(<) ==> (G1(y) === G2(y))) by Tautology.fromLastStep(InitialSegment.membership, `x ∈ S` of (x := y))
        thenHave(∀(y, y ∈ initialSegment(x)(A)(<) ==> (G1(y) === G2(y)))) by RightForall

        have(thesis) by Tautology.from(FunctionRestriction.extensionality of (f := G1, g := G2, X := initialSegment(x)(A)(<)), lastStep)
      }

      // By definition of `G1` and `G2`, it must be the case that `G1(x) = G2(x)`.
      // TODO: Congruence does not work here for some reason
      // have((x ∈ A, x ∈ S, minimal(x)(<)(A)) |- G1(x) === G2(x)) by Congruence.from(`G1(x)`, `G2(x)`, `agreement`)

      // Contradiction since `x ∈ S` and thus `G1(x) ≠ G2(x)`.
      // thenHave(thesis) by Tautology.fromLastStep(`x ∈ S`)
      sorry
    }
    thenHave(S === ∅) by Restate

    have(x ∉ S) by Congruence.from(EmptySet.definition, lastStep)
    thenHave(x ∈ A ==> (G1(x) === G2(x))) by Tautology.fromLastStep(`x ∈ S`)
    thenHave(∀(x, x ∈ A ==> (G1(x) === G2(x)))) by RightForall
    thenHave(thesis) by Tautology.fromLastStep(Functions.Properties.extensionality of (f := G1, g := G2))
  }

  extension (G: set) {
    private inline def `is defined by recursion until`(z: set) =
      functionOn(G)(initialSegment(z)(A)(<)) /\ ∀(x, (x, z) ∈ < ==> (G(x) === F(G↾initialSegment(z)(A)(<))))
  }

  /**
    * Lemma --- The existence of a function `g` defined by recursion
    * propagates.
    */
  val recursionStep = Lemma(
    (
      x ∈ A,
      ∀(y, (y ∈ A) /\ ((y, x) ∈ <) ==> ∃!(G, G `is defined by recursion until` y))
    ) |-
      ∃(G, G `is defined by recursion until` x)
  ) {
    assume(x ∈ A)

    assume(∀(y, (y ∈ A) /\ ((y, x) ∈ <) ==> ∃!(G, G `is defined by recursion until` y)))
    thenHave((y ∈ A) /\ ((y, x) ∈ <) ==> ∃!(G, G `is defined by recursion until` y)) by InstantiateForall(y)
    thenHave(y ∈ initialSegment(x)(A)(<) ==> ∃!(G, G `is defined by recursion until` y)) by Substitute(InitialSegment.membership)

    // We can assign to each `y ∈ initialSegment(x)(A)(<)` the function defined
    // by recursion until `y`, and hence by the replacement schema we can form
    // the set of all functions defined on an initial segment of `x`.
    val R = {ε(G, G `is defined by recursion until`(y)) | y ∈ initialSegment(x)(A)(<)}
    val Q = ⋃(R)

    // There are two cases to consider:
    // 1. If `x` has a predecessor `y`, then `Q ∪ {(y, F(Q))}` is the desired function.
    have(((y, x) ∈ <, ∀(z, (z, x) ∈ < ==> (y, z) ∉ <)) |- ∃(G, G `is defined by recursion until` x)) subproof {
      sorry
    }
    thenHave(((y, x) ∈ < /\ ∀(z, (z, x) ∈ < ==> (y, z) ∉ <)) |- ∃(G, G `is defined by recursion until` x)) by Restate
    val `x has a predecessor` = thenHave(∃(y, (y, x) ∈ < /\ ∀(z, (z, x) ∈ < ==> (y, z) ∉ <)) |- ∃(G, G `is defined by recursion until` x)) by LeftExists

    // 2. If `x` has no predecessor, then `Q` is the desired function.
    val `x is limit` = have(
      ¬(∃(y, (y, x) ∈ < /\ ∀(z, (z, x) ∈ < ==> (y, z) ∉ <))) |- ∃(G, G `is defined by recursion until` x)
    ) subproof {
      sorry
    }

    have(thesis) by Tautology.from(`x has a predecessor`, `x is limit`)
  }


  /**
    * Well-ordered recursion --- Given `F : 𝕍 -> 𝕍` and a well-order `(A, <)`
    * there exists a unique `G : A -> 𝕍` such that
    *
    *   `∀x ∈ A. G(x) = F(G↾initialSegment(x, A, <))`
    *
    * This recursion principle implies recursion on any ordinal `α`, since `α`
    * is well-ordered by the membership relation, and `initialSegment(β, α, ∈_α) = β`
    * for `β ∈ α`.
    */
  val recursionExistence = Theorem(
    ∃(G, ∀(x, x ∈ A ==> (G(x) === F(G↾initialSegment(x)(A)(<)))))
  ) {
    sorry
  }

  /**
    * Definition --- Returns the function obtained by applying `F` recursively on `(A, <)`.
    */
  val recurse = DEF(λ(F, λ(A, λ(<, ε(G, ∀(x, x ∈ A ==> (G(x) === F(G↾initialSegment(x)(A)(<)))))))))
}
