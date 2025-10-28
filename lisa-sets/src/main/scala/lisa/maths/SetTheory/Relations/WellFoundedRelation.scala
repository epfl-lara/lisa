package lisa.maths.SetTheory.Relations

import lisa.maths.SetTheory.Base
import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Order.Extrema.minimal
import lisa.maths.SetTheory.Functions.Predef.*

import Relation.R

import lisa.maths.Quantifiers.∃!

/**
  * A relation `R` on a set `X` is called well-founded if every non-empty
  * subset `S ⊆ X` admits a `R`-minimal element.
  *
  * Well-founded relations allow one to perform (transfinite) induction on `X`:
  * to show that `P(x)` holds for all `x ∈ X`, it is sufficient to show that
  * `P(x)` follows from `P(y)` for all `y ∈ X` such that `y R x`.
  *
  * Similarly, we can construct functions by transfinite recursion over `X`, by using
  * values of the predecessors of `x` to define the function at `x`. More
  * precisely, there exists a function `G` such that for all `x ∈ X`,
  * `G(x) = F(x, G ↾ cl(x, R))` where `cl(x, R)` is the transitive closure of the
  * predecessor relation at `x`.
  */
object WellFoundedRelation extends lisa.Main {

  private val m = variable[Ind]
  private val S = variable[Ind]

  private val < = variable[Ind]
  private val F = variable[Ind >>: Ind >>: Ind]
  private val G, G1, G2 = variable[Ind]

  extension (x: Expr[Ind]) {
    private inline def apply(y: Expr[Ind]): Expr[Ind] = app(x)(y)
  }

  /**
    * Well-founded Relation --- A relation `R` on `X` is said to be well-founded if
    * every non-empty subset of `X` admits a `R`-minimal element.
    */
  val wellFounded = DEF(λ(R, λ(X, ∀(S, (S ⊆ X) /\ (S ≠ ∅) ==> ∃(m, minimal(m)(S)(R))))))

  /**
    * Theorem --- Quantifier-free reformulation of the well-foundedness property.
    */
  val minimalElement = Theorem(
    (wellFounded(R)(X), S ⊆ X, S ≠ ∅) |- ∃(m, minimal(m)(S)(R))
  ) {
    assume(wellFounded(R)(X))
    have(∀(S, (S ⊆ X) /\ (S ≠ ∅) ==> ∃(m, minimal(m)(S)(R)))) by Tautology.from(wellFounded.definition)
    thenHave((S ⊆ X) /\ (S ≠ ∅) ==> ∃(m, minimal(m)(S)(R))) by InstantiateForall(S)
    thenHave(thesis) by Restate
  }

  /**
    * Theorem --- If `R` is well-founded on `X` and `S ⊆ X` then `R` is well-founded
    * on `S`.
    */
  val subset = Theorem(
    (wellFounded(R)(X), S ⊆ X) |- wellFounded(R)(S)
  ) {
    assume(wellFounded(R)(X))
    assume(S ⊆ X)

    have(∀(A, (A ⊆ X) /\ (A ≠ ∅) ==> ∃(m, minimal(m)(A)(R)))) by Congruence.from(wellFounded.definition)
    thenHave((A ⊆ X) /\ (A ≠ ∅) ==> ∃(m, minimal(m)(A)(R))) by InstantiateForall(A)
    thenHave((A ⊆ S) /\ (A ≠ ∅) ==> ∃(m, minimal(m)(A)(R))) by Tautology.fromLastStep(
      Subset.transitivity of (x := A, y := S, z := X)
    )
    thenHave(∀(A, (A ⊆ S) /\ (A ≠ ∅) ==> ∃(m, minimal(m)(A)(R)))) by RightForall
    thenHave(thesis) by Substitute(wellFounded.definition of (X := S))
  }


  //////////////////////////////////////////////////////////////////////////////////
  section("Well-founded induction")


  /**
    * Theorem --- If `R` is well-founded, one can show that `P(x)` holds for all `x ∈ X`
    * by induction: it is sufficient to show that for all `x ∈ X`, if `P(y)`
    * holds for all `y R x`, then `P(x)` holds.
    *
    * This proof goes by *minimal counterexample*: assuming by contradiction that `¬P(x)`
    * holds for some `x`, there exists a minimal such counterexample by
    * well-foundedness, such that `P(y)` holds for all `y R x`. But by assumption this implies
    * `P(x)`, hence the contradiction.
    */
  val induction = Theorem(
    (wellFounded(R)(X), ∀(x ∈ X, (∀(y ∈ X, (y R x) ==> P(y))) ==> P(x))) |- ∀(x ∈ X, P(x))
  ) {
    assume(wellFounded(R)(X))
    assume(∀(x ∈ X, (∀(y ∈ X, (y R x) ==> P(y))) ==> P(x)))

    // We state the induction hypothesis
    val IHm = thenHave(m ∈ X ==> ((∀(x ∈ X, (x R m) ==> P(x))) ==> P(m))) by InstantiateForall(m)

    // Consider the set D of elements of X that do not satisfy P
    val D = { x ∈ X | ¬(P(x)) }
    val `x ∈ D` = have(x ∈ D <=> (x ∈ X) /\ ¬(P(x))) by Comprehension.apply

    // If D = ∅, we are done
    val `D = ∅` =
      have(x ∈ X ==> x ∉ ∅) by Tautology.from(EmptySet.definition)
      thenHave(D === ∅ |- x ∈ X ==> x ∉ D) by Congruence
      thenHave(D === ∅ |- x ∈ X ==> P(x)) by Tautology.fromLastStep(`x ∈ D`)
      thenHave(D === ∅ |- ∀(x ∈ X, P(x))) by RightForall

    // If D ≠ ∅, since `D ⊆ X` it admits a `R`-minimal element
    have(∀(S, (S ⊆ X) /\ (S ≠ ∅) ==> ∃(m, minimal(m)(S)(R)))) by Tautology.from(wellFounded.definition)
    thenHave((D ⊆ X) /\ (D ≠ ∅) ==> ∃(m, minimal(m)(D)(R))) by InstantiateForall(D)
    val `∃m R-minimal` = thenHave(D ≠ ∅ |- ∃(m, minimal(m)(D)(R))) by Tautology.fromLastStep(
      Comprehension.subset of (y := X, φ := λ(x, ¬(P(x))))
    )

    // Let m be the `R`-minimal element. Since there are no x ∈ X preceding m such that
    // ¬P(x) holds, P(x) holds for all x preceding m.
    have(minimal(m)(D)(R) |- ∀(x ∈ D, ¬(x R m))) by Tautology.from(minimal.definition of (A := D, < := R, a := m))
    thenHave(minimal(m)(D)(R) |- ∀(x ∈ D, (x R m) ==> P(x))) by Tableau
    val `case x ∈ D` = thenHave((minimal(m)(D)(R), x ∈ D) |- (x R m) ==> P(x)) by InstantiateForall(x)
    val `case x ∈ X - D` = have((x ∈ X, x ∉ D) |- (x R m) ==> P(x)) by Tautology.from(`x ∈ D`)

    have(minimal(m)(D)(R) |- x ∈ X ==> ((x R m) ==> P(x))) by Tautology.from(`case x ∈ D`, `case x ∈ X - D`)
    thenHave(minimal(m)(D)(R) |- ∀(x ∈ X, (x R m) ==> P(x))) by RightForall

    // By the induction hypothesis, it must be the case that P(m) holds. Contradiction
    thenHave(minimal(m)(D)(R) |- ()) by Tautology.fromLastStep(
      IHm,
      minimal.definition of (A := D, < := R, a := m),
      `x ∈ D` of (x := m)
    )
    thenHave(∃(m, minimal(m)(D)(R)) |- ()) by LeftExists
    thenHave(thesis) by Tautology.fromLastStep(`∃m R-minimal`, `D = ∅`)
  }

}

