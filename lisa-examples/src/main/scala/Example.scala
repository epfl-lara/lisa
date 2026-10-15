
object Example extends lisa.Main:
  // First-order variables and a unary predicate.
  val x = variable[Ind]
  val y = variable[Ind]
  val P = variable[Ind >>: Prop]

  // Formulas are Scala values: they can be inspected and transformed.
  val formula = ∀(x, P(x) ==> ∃(y, P(y)))
  println(formula.subexpressions.mkString("\n"))

  // A unary first-order function.
  val f = variable[Ind >>: Ind]

  // Scala extensions can provide local mathematical notation.
  extension (left: Expr[Ind]) inline infix def subset(right: Expr[Ind]): Expr[Prop] = App(App(⊆, left), right)

  // Assumptions are facts. Quantified facts can be instantiated explicitly;
  // `Tautology` then combines the resulting implications propositionally.
  val fixedPointDoubleApplication = Theorem(∀(x, P(x) ==> P(f(x))) |- P(x) ==> P(f(f(x)))):
    val closure = assume(∀(x, P(x) ==> P(f(x))))
    val closureAtX = have(P(x) ==> P(f(x))) by InstantiateForall(x)(closure)
    val closureAtFx = have(P(f(x)) ==> P(f(f(x)))) by InstantiateForall(f(x))(closure)
    have(thesis) by Tautology.from(closureAtX, closureAtFx)

  /**
   * Every set is a subset of itself: `⊢ x ⊆ x`.
   */
  val subsetReflexivity = Theorem(x ⊆ x):
    have((y ∈ x) ==> (y ∈ x)) by Restate
    thenHave(∀(y, (y ∈ x) ==> (y ∈ x))) by RightForall
    have(thesis) by Tautology.from(lastStep, subsetAxiom of (x := x, y := x))

  /**
   * The empty set is a subset of every set: `⊢ ∅ ⊆ x`.
   */
  val emptySetSubset = Theorem(∅ ⊆ x):
    have((y ∈ ∅) ==> (y ∈ x)) by Weakening(emptySetAxiom of (x := y))
    thenHave(∀(y, (y ∈ ∅) ==> (y ∈ x))) by RightForall
    have(thesis) by Tautology.from(lastStep, subsetAxiom of (x := ∅, y := x))

  /**
   * A set containing an element is not empty: `y ∈ x ⊢ x ≠ ∅`.
   */
  val setWithElementNonEmpty = Theorem((y ∈ x) |- x =/= ∅):
    have((x === ∅) |- !(y ∈ x)) by Substitute(x === ∅)(emptySetAxiom of (x := y))

  /**
   * The power set of any set is non-empty: `⊢ 𝒫(x) ≠ ∅`.
   */
  val powerSetNonEmpty = Theorem(𝒫(x) =/= ∅):
    have(thesis) by Tautology.from(
      setWithElementNonEmpty of (y := ∅, x := 𝒫(x)),
      powerSetAxiom of (x := ∅, y := x),
      emptySetSubset
    )

  // `Tableau` handles first-order reasoning, including quantifiers.
  val drinkersParadox = Theorem(∃(x, P(x) ==> ∀(y, P(y)))):
    have(thesis) by Tableau
