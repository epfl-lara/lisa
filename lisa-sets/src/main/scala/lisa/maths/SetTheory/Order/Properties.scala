package lisa.maths.SetTheory.Order

import lisa.maths.SetTheory.Base.Predef.{*, given}
import lisa.maths.SetTheory.Relations
import lisa.maths.SetTheory.Relations.Predef.*

import Definitions.*

/** Properties and theorems about partial-orders.
  */
object Properties extends lisa.Main {

  private val x, y, z = variable[Ind]
  private val A, X = variable[Ind]
  private val < = variable[Ind]
  private val ℛ = variable[Ind]

  /** Local notations for partial orders. */
  extension (x: set) {
    private infix def <(y: set): Expr[Prop] = (x, y) ∈ Properties.<
  }

  /** Theorem --- If `(A, <)` is a strict partial order, then `<` is antisymmetric.
    *
    * This follows from irreflexivity and the fact that `¬(x < y /\ y < x)`.
    */
  val strictPartialOrderAntisymmetric = Theorem(
    strictPartialOrder(A)(<) |- antisymmetric(<)
  ) {
    assume(strictPartialOrder(A)(<))

    have(∀(x, ¬(x < x))) by Tautology.from(strictPartialOrder.definition, irreflexive.definition of (ℛ := <))
    val irreflexivity = thenHave(¬(x < x)) by InstantiateForall(x)

    have(∀(x, ∀(y, ∀(z, (x < y) /\ (y < z) ==> (x < z))))) by Tautology.from(strictPartialOrder.definition, transitive.definition of (ℛ := <, X := A))
    thenHave((x < y) /\ (y < x) ==> (x < x)) by InstantiateForall(x, y, x)
    thenHave((x < y) /\ (y < x) ==> (x === y)) by Tautology.fromLastStep(irreflexivity)
    thenHave(∀(x, ∀(y, (x < y) /\ (y < x) ==> (x === y)))) by Generalize
    thenHave(thesis) by Tautology.fromLastStep(
      antisymmetric.definition of (ℛ := <),
      strictPartialOrder.definition,
      Relations.Properties.relationOnIsRelation of (ℛ := <, X := A)
    )
  }
}
