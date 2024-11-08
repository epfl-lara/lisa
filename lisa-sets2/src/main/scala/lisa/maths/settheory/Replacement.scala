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
  val B = variable[Term]
  val f = variable[Term >>: Term]
  val P = variable[Term >>: Term >>: Formula]

  val map = DEF(lambda(t, lambda(f, ε(s, ∀(y, (y ∈ s) <=> ∃(x, x ∈ t /\ (y === f(x))))))))

  private val replacement: map.type = map

  extension (t: Expr[Term])
    def map(function: Expr[Term >>: Term]): Expr[Term] =
      replacement(t)(function)

  /**
   * The existence of the image of a set under a function. Or, the functional
   * form of the replacement schema.
   */
  val existence = Theorem(∃(s, ∀(y, (y ∈ s) <=> ∃(x, x ∈ t /\ (y === f(x)))))):
    val inst = replacementSchema of (A := t, P := lambda(x, lambda(y, y === f(x))))
    val conditional = have(∀(x, x ∈ t ==> ∀(y, ∀(z, ((y === f(x)) /\ (z === f(x))) ==> (y === z)))) |- ∃(s, ∀(y, (y ∈ s) <=> ∃(x, x ∈ t /\ (y === f(x)))))) by Weakening(inst)

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
  val definition: THM = Theorem(∀(y, y ∈ s.map(f) <=> ∃(x, x ∈ s /\ (y === f(x))))):
    have(∀(y, y ∈ t <=> ∃(x, x ∈ s /\ (y === f(x)))) |-     ∀(y, y ∈ t                                                 <=> ∃(x, x ∈ s /\ (y === f(x))))) by Hypothesis
    thenHave(∀(y, y ∈ t <=> ∃(x, x ∈ s /\ (y === f(x)))) |- ∀(y, y ∈ ε(t, ∀(y, y ∈ t <=> ∃(x, x ∈ s /\ (y === f(x))))) <=> ∃(x, x ∈ s /\ (y === f(x))))) by RightEpsilon.withParameters(∀(y, y ∈ t <=> ∃(x, x ∈ s /\ (y === f(x)))), t, t)
    thenHave(∀(y, y ∈ t <=> ∃(x, x ∈ s /\ (y === f(x)))) |- ∀(y, y ∈ s.map(f) <=> ∃(x, x ∈ s /\ (y === f(x))))) by Substitution.Apply(map.definition of (t := s))
    thenHave(∃(t, ∀(y, y ∈ t <=> ∃(x, x ∈ s /\ (y === f(x))))) |- ∀(y, y ∈ s.map(f) <=> ∃(x, x ∈ s /\ (y === f(x))))) by LeftExists
    have(thesis) by Cut(existence of (t := s), lastStep)

  /**
   * The replacement property of a [[map]]ped set.
   *
   * `x ∈ s ==> f(x) ∈ s.map(f)`
   */
  val unfolding = Theorem(x ∈ s ==> f(x) ∈ s.map(f)):
    have(x ∈ s |- x ∈ s /\ (f(x) === f(x))) by Restate
    val cond = thenHave(x ∈ s |- ∃(y, y ∈ s /\ (f(x) === f(y)))) by RightExists

    val inst =
      have(f(x) ∈ s.map(f) <=> ∃(y, y ∈ s /\ (f(x) === f(y)))) by InstantiateForall(f(x))(definition)
      thenHave(∃(y, y ∈ s /\ (f(x) === f(y))) |- f(x) ∈ s.map(f)) by Weakening

    have(x ∈ s |- f(x) ∈ s.map(f)) by Cut(cond, inst)

end Replacement
