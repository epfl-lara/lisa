import lisa.automation.Congruence
import lisa.automation.Substitution.{Apply => Substitute}
import lisa.automation.Tableau

object Example extends lisa.Main:
  // draft mode; only proofs from the current file are checked
  draft()

  // first-order variables
  val x = variable[Ind]
  val y = variable[Ind]

  // a predicate with one argument
  val P = variable[Ind >>: Prop]

  val form = forall(x, P(x) ==> exists(y, P(y)))

  // a first-order function with one argument
  val f = variable[Ind >>: Ind]

  // we can use scala extensions to define custom syntax
  extension (x: Expr[Ind])
    inline infix def subset(y: Expr[Ind]): Expr[Prop] = App(App(⊆, x), y)

  // a simple proof with Lisa's DSL
  val fixedPointDoubleApplication = Theorem(∀(x, P(x) ==> P(f(x))) |- P(x) ==> P(f(f(x)))) {
    val a1 = assume(∀(x, P(x) ==> P(f(x))))
    have(thesis) by Tautology.from(a1 of x, a1 of f(x))
  }

  // Example of set theoretic development
  /**
    * Theorem --- a set is a subset of itself.
    * 
    *  `|- x ⊆ x`
    */
  val union = Theorem(
    x ⊆ x
  ) {
    have((y ∈ x) ==> (y ∈ x)) by Restate
    have(∀(y, (y ∈ x) ==> (y ∈ x))) by Restate

    have(thesis) by Tautology.from(lastStep, subsetAxiom of (x := x, y := x))
  }

  /**
   * Theorem --- The empty set is a subset of every set.
   * 
   *   `|- ∅ ⊆ x`
   */
  val leftEmpty = Theorem(∅ ⊆ x): // braceless syntax is also fine!
    have((y ∈ ∅) ==> (y ∈ x)) by Weakening(emptySetAxiom of (x := y))
    thenHave(∀(y, (y ∈ ∅) ==> (y ∈ x))) by RightForall
    
    have(thesis) by Tautology.from(lastStep, subsetAxiom of (x := ∅, y := x))
  
  /**
   * Theorem --- If a set has an element, then it is not the empty set.
   * 
   *   `y ∈ x ⊢ ! x = ∅`
   */
  val setWithElementNonEmpty = Theorem(
    (y ∈ x) |- x =/= ∅
  ) {
    have((x === ∅) |- !(y ∈ x)) by Substitute(x === ∅)(emptySetAxiom of (x := y))
    // this statement is `Restate` equivalent to the result, so we are done!
  }

  /**
   * Theorem --- the power set of any set is non-empty.
   * 
   *  `|- 𝒫(x) =/= ∅`
   */
  val powerSetNonEmpty = Theorem(
    𝒫(x) =/= ∅
  ) {
    have(thesis) by Tautology.from(
      setWithElementNonEmpty of (y := ∅, x := 𝒫(x)),
      powerSetAxiom of (x := ∅, y := x),
      leftEmpty
    )
  }

  // example showing the Tableau tactic to discharge first-order tautologies
  val buveurs = Theorem(exists(x, P(x) ==> forall(y, P(y)))) {
    have(thesis) by Tableau
  }

