package lisa.maths.settheory

import lisa.automation.Substitution
import lisa.maths.Quantifiers

object Replacement extends lisa.Main:

  val x = variable[Term]
  val y = variable[Term]
  val z = variable[Term]
  val t = variable[Term]
  val s = variable[Term]
  val A = variable[Term]
  val f = variable[Term >>: Term]
  val P = variable[Term >>: Term >>: Formula]

  val map = DEF ( lambda(t, lambda(f, ε(s, ∀(x, (x ∈ s) <=> ∃(y, y ∈ t /\ (y === f(x))))))) )

  private val replacement: map.type = map

  extension (t: Expr[Term])
    def map(function: Expr[Term >>: Term]): Expr[Term] =
      replacement(t)(function)

  /**
    * The existence of the image of a set under a function. Or, the functional
    * form of the replacement schema.
    */
  val existence = Theorem( ∃(s, ∀(x, (x ∈ s) <=> ∃(y, y ∈ t /\ (y === f(x))))) ):
    val inst = replacementSchema of (A := t, P := lambda(x, lambda(y, y === f(x))))
    val conditional = have(∀(x, x ∈ t ==> ∀(y, ∀(z, ((y === f(x)) /\ (z === f(x))) ==> (y === z) ))) |- ∃(s, ∀(x, (x ∈ s) <=> ∃(y, y ∈ t /\ (y === f(x))))) ) by Weakening(inst)

    val eqTautology =
      have(((y === f(x)) /\ (z === f(x))) ==> (y === z)) by Weakening(Equality.transitivity of (x := y, y := f(x), z := z))
      thenHave(∀(y, ∀(z, ((y === f(x)) /\ (z === f(x))) ==> (y === z)))) by Quantifiers.quantifyAll

    thenHave(x ∈ t ==> ∀(y, ∀(z, ((y === f(x)) /\ (z === f(x))) ==> (y === z)))) by Weakening
    thenHave(∀(x, x ∈ t ==> ∀(y, ∀(z, ((y === f(x)) /\ (z === f(x))) ==> (y === z))))) by RightForall

    have(thesis) by Cut(lastStep, conditional)

  /**
    * The extensional definition of a [[map]]ped set.
    * 
    * `∀(x, x ∈ s.map(f) <=> ∃(y, y ∈ s /\ x === f(y)))`
    */
  val definition: THM = Theorem( ∀(x, x ∈ s.map(f) <=> ∃(y, y ∈ s /\ (x === f(y)))) ):
    have    ( ∀(x, x ∈ y <=> ∃(y, y ∈ s /\ (x === f(y)))) |- ∀(x, x ∈ y <=> ∃(y, y ∈ s /\ (x === f(y)))) ) by Hypothesis
    thenHave( ∀(x, x ∈ y <=> ∃(y, y ∈ s /\ (x === f(y)))) |- ∀(x, x ∈ ε(t, ∀(x, x ∈ t <=> ∃(y, y ∈ s /\ (x === f(y))))) <=> ∃(y, y ∈ s /\ (x === f(y)))) ) by RightEpsilon
    thenHave( ∀(x, x ∈ y <=> ∃(y, y ∈ s /\ (x === f(y)))) |- ∀(x, x ∈ s.map(f) <=> ∃(y, y ∈ s /\ (x === f(y)))) ) by Substitution.Apply(map.definition)
    thenHave( ∃(y, ∀(x, x ∈ y <=> ∃(y, y ∈ s /\ (x === f(y))))) |- ∀(x, x ∈ s.map(f) <=> ∃(y, y ∈ s /\ (x === f(y)))) ) by LeftExists
    have(thesis) by Cut(existence, lastStep)

  /**
   * The replacement property of a [[map]]ped set.
   * 
   * `x ∈ s ==> f(x) ∈ s.map(f)`
   */
  val unfolding = Theorem( x ∈ s ==> f(x) ∈ s.map(f) ):
    have(x ∈ s |- x ∈ s /\ (f(x) === f(x))) by Restate
    val cond = thenHave(x ∈ s |- ∃(y, y ∈ s /\ (f(x) === f(y)))) by RightExists

    val inst = 
      have(f(x) ∈ s.map(f) <=> ∃(y, y ∈ s /\ (f(x) === f(y)))) by InstantiateForall(f(x))(definition)
      thenHave(∃(y, y ∈ s /\ (f(x) === f(y))) |- f(x) ∈ s.map(f)) by Weakening

    have(x ∈ s |- f(x) ∈ s.map(f)) by Cut(cond, inst)

end Replacement