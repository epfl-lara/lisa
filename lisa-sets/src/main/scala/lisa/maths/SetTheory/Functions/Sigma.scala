package lisa.maths.SetTheory.Functions

import lisa.maths.SetTheory.Base.Predef.{_, given}

import Function._

/**
 * Given a set `A` and a function `B`, the dependent sum `Σ(A, B)` is the set
 * of all pairs `(a, b)` such that `a ∈ A` and `b ∈ B(a)`.
 */
object Sigma extends lisa.Main {

  private val x = variable[Ind]
  private val a, b = variable[Ind]
  private val A = variable[Ind]
  private val B = variable[Ind]

  extension (f: Expr[Ind]) {
    def apply(x: Expr[Ind]) = app(f)(x)
  }

  /**
   * Definition --- Given a set `A` and a function `B`, the dependent sum `Σ(A, B)`
   * is the set of all pairs `(a, b)` such that `a ∈ A` and `b ∈ B(a)`.
   *
   *    `Σ(A, B) = {(a, b) | a ∈ A, b ∈ B(a) }`
   */
  val Σ = DEF(λ(A, λ(B, { x ∈ (A × ⋃({ B(a) | a ∈ A })) | snd(x) ∈ B(fst(x)) })))

  /**
   * Theorem --- The dependent sum on the empty set is ∅.
   */
  val emptySet = Theorem(
    Σ(∅)(B) === ∅
  ) {
    val W = ⋃({ B(a) | a ∈ ∅ })
    have(z ∈ { x ∈ (∅ × W) | snd(x) ∈ B(fst(x)) } <=> z ∈ (∅ × W) /\ (snd(z) ∈ B(fst(z)))) by Comprehension.apply
    thenHave(z ∈ Σ(∅)(B) <=> z ∈ (∅ × W) /\ (snd(z) ∈ B(fst(z)))) by Substitute(Σ.definition of (A := ∅))
    thenHave(z ∈ Σ(∅)(B) <=> z ∈ ∅ /\ (snd(z) ∈ B(fst(z)))) by Substitute(CartesianProduct.leftEmpty of (B := W))
    thenHave(z ∈ Σ(∅)(B) <=> z ∈ ∅) by Tautology.fromLastStep(EmptySet.definition of (x := z))
    thenHave(thesis) by Extensionality
  }

  /**
   * Theorem --- We have `(a, b) ∈ Σ(A, B)` <=> `a ∈ A` and `b ∈ B(a)`.
   */
  val membership = Theorem(
    (a, b) ∈ Σ(A)(B) <=> (a ∈ A) /\ (b ∈ B(a))
  ) {
    val fibers = { B(x) | x ∈ A }
    val bound = A × ⋃(fibers)
    val expanded = have(
      (a, b) ∈ { x ∈ bound | snd(x) ∈ B(fst(x)) } <=>
        ((a, b) ∈ bound) /\ (snd(a, b) ∈ B(fst(a, b)))
    ) by Comprehension.apply
    val projections = have(snd(a, b) ∈ B(fst(a, b)) <=> b ∈ B(a)) by Congruence.from(
      Pair.pairFst of (x := a, y := b),
      Pair.pairSnd of (x := a, y := b)
    )
    val pairInBound = CartesianProduct.pairMembership of (x := a, y := b, A := A, B := ⋃(fibers))
    val inFiberUnion = have((a ∈ A, b ∈ B(a)) |- b ∈ ⋃(fibers)) subproof {
      assume(a ∈ A)
      assume(b ∈ B(a))
      have(a ∈ A /\ (B(a) === B(a))) by Tautology
      thenHave(∃(x ∈ A, B(x) === B(a))) by RightExists
      val fiberMember = thenHave(B(a) ∈ fibers) by Tautology.fromLastStep(
        Replacement.membership of (F := λ(x, B(x)), y := B(a))
      )
      have(B(a) ∈ fibers /\ b ∈ B(a)) by Tautology.from(fiberMember)
      thenHave(∃(x, x ∈ fibers /\ b ∈ x)) by RightExists
      thenHave(thesis) by Tautology.fromLastStep(unionAxiom of (x := fibers, z := b))
    }
    have((a, b) ∈ { x ∈ bound | snd(x) ∈ B(fst(x)) } <=> (a ∈ A) /\ (b ∈ B(a))) by
      Tautology.from(expanded, projections, pairInBound, inFiberUnion)
    thenHave(thesis) by Substitute(Σ.definition)
  }

}
