package lisa.maths.SetTheory.Base

import Symbols._

/**
 * A class is a collection that is characterized by a first-order formula.
 *
 * Not all classes represent sets: for example, the class of all sets (`V`) is
 * not a set (see [[WellFounded.noUniversalSet]]), as well as the class of all
 * ordinals (`Ord`, see [[lisa.maths.SetTheory.Ordinals.Ordinal]]). Such classes
 * are called [[Class.proper]] classes.
 */
object Class extends lisa.Main {

  private val C = variable[Class]

  /**
   * Definition --- A class `C` is said to be proper if `C` does not represent a set:
   *
   *   `¬∃y. ∀x. x ∈ y <=> C(x)`
   */
  val proper = DEF(λ(C, ¬(∃(y, ∀(x, x ∈ y <=> C(x))))))

  /**
   * Represents the class of all sets, known as the von Neumann universe `V`.
   */
  val V = DEF(λ(x, ⊤))

  /**
   * Theorem --- `V` is a proper class: there is no set that contains all sets.
   *
   * Reformulation of [[FoundationAxiom.noUniversalSet]].
   */
  val `V is a proper class` = Theorem(
    proper(V)
  ) {
    have(¬(y ∈ y <=> ⊤)) by Restate.from(FoundationAxiom.selfNonInclusion of (x := y))
    thenHave(¬(y ∈ y <=> V(y))) by Substitute(V.definition)
    thenHave((y ∈ y <=> V(y)) |- ()) by Restate
    thenHave(∀(x, x ∈ y <=> V(x)) |- ()) by LeftForall
    thenHave(∃(y, ∀(x, (x ∈ y <=> V(x)))) |- ()) by LeftExists
    thenHave(¬(∃(y, ∀(x, (x ∈ y <=> V(x)))))) by Restate
    thenHave(thesis) by Substitute(proper.definition of (C := V))
  }
}
