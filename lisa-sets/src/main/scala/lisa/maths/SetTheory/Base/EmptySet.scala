package lisa.maths.SetTheory.Base

/** The empty set, denoted `∅`, is the set that contains no elements.
  *
  * It can be obtained from first-order logic and the comprehension schema,
  * since `∃x. x = x` is a theorem of first-order logic. From that set `x`,
  * define `∅ = {y ∈ x | ⊥}`. By extensionality, the empty set is unique.
  * To simplify matters, we assume its existence through the [[emptySetAxiom]].
  */
object EmptySet extends lisa.Main {

  private val x, y = variable[Ind]

  /** Definition of the empty set:
    *
    *   `x ∉ ∅` for any `x`
    *
    * @see [[emptySetAxiom]]
    */
  val definition = emptySetAxiom

  /** Theorem --- If a set has an element, then it is not the empty set.
    *
    *    `x ∈ y ⊢ y ≠ ∅`
    */
  val setWithElementNonEmpty = Theorem(
    x ∈ y |- y ≠ ∅
  ) {
    have(y === ∅ |- x ∉ y) by Congruence.from(definition)
    thenHave(thesis) by Restate
  }

  /** Theorem --- A set containing no elements is equal to the empty set.
    *
    *    `∀ y. y ∉ x ⊢ x = ∅`
    *
    * Follows from [[Extensionality]].
    */
  val setWithNoElementsIsEmpty = Theorem(
    ∀(y, y ∉ x) |- x === ∅
  ) {
    have(y ∉ x |- (y ∈ x) <=> (y ∈ ∅)) by Tautology.from(definition of (x := y))
    thenHave(∀(y, y ∉ x) |- (y ∈ x) <=> (y ∈ ∅)) by LeftForall
    thenHave(thesis) by Extensionality
  }

  /** Theorem --- A non-empty set has an element:
    *
    *  `x ≠ ∅ ==> ∃y. y ∈ x`
    */
  val nonEmptyHasElement = Theorem(
    x ≠ ∅ |- ∃(y, y ∈ x)
  ) {
    have(thesis) by Restate.from(setWithNoElementsIsEmpty)
  }

}
