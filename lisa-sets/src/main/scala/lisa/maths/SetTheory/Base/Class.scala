package lisa.maths.SetTheory.Base

import lisa.maths.Quantifiers.∃!

/**
 * A class is a collection that is characterized by a first-order formula.
 *
 * Not all classes represent sets: for example, the class of all sets (`V`) is
 * not a set (see [[WellFounded.noUniversalSet]]), as well as the class of all
 * ordinals (`On`). Such classes are called proper classes.
 */
object Class extends lisa.Main {

  private val x, y, z = variable[Ind]

  /**
   * A class is nothing more than a first-order formula with a free
   * variable.
   */
  type Class = Ind >>: Prop

  /**
   * A class-function is a binary predicate `F` that is functional: for any `x`,
   * there is at most one `y` such that `F(x, y)` holds.
   *
   * Equivalently, we can use meta-functions to represent class-functions, since
   * from a meta-function `f` one can define the predicate `F(x, y) := f(x) = y`,
   * and conversely from a class-function `F`, one defines the meta-function
   * `f := λ(x, ε(y, F(x, y)))`.
   *
   * Meta-functions are more convenient to use that functional predicates, and hence
   * will be used instead.
   */
  type ClassFunction = Ind >>: Ind

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
   * Reformulation of [[WellFounded.noUniversalSet]].
   */
  val `V is a proper class` = Theorem(
    proper(V)
  ) {
    have(¬(y ∈ y <=> ⊤)) by Restate.from(WellFounded.selfNonInclusion of (x := y))
    thenHave(¬(y ∈ y <=> V(y))) by Substitute(V.definition)
    thenHave((y ∈ y <=> V(y)) |- ()) by Restate
    thenHave(∀(x, x ∈ y <=> V(x)) |- ()) by LeftForall
    thenHave(∃(y, ∀(x, (x ∈ y <=> V(x)))) |- ()) by LeftExists
    thenHave(¬(∃(y, ∀(x, (x ∈ y <=> V(x)))))) by Restate
    thenHave(thesis) by Substitute(proper.definition of (C := V))
  }
}
