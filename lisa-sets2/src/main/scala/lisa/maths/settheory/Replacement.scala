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

  private val replacement: Constant[Arrow[T, Arrow[Arrow[T, T], T]]] = DEF ( lambda(t, lambda(f, ε(s, ∀(x, (x ∈ s) <=> ∃(y, y ∈ t /\ (y === f(x))))))) )

  extension (t: Term)
    def map(function: Term >>: Term): Term =
      replacement(t)(function)

  // this has to be after the extension for compilation
  val map = replacement

  val existence = Theorem( ∃(s, ∀(x, (x ∈ s) <=> ∃(y, y ∈ t /\ (y === f(x))))) ):
    val inst = replacementSchema of (A := t, P := lambda(x, lambda(y, y === f(x))))
    val conditional = have(∀(x, x ∈ t ==> ∀(y, ∀(z, ((y === f(x)) /\ (z === f(x))) ==> (y === z) ))) |- ∃(s, ∀(x, (x ∈ s) <=> ∃(y, y ∈ t /\ (y === f(x))))) ) by Weakening(inst)

    have(∀(y, ∀(z, ((y === f(x)) /\ (z === f(x))) ==> (y === z)))) subproof:
      have(((y === f(x)) /\ (z === f(x))) ==> (y === z)) by Weakening(Equality.transitivity of (x := y, y := f(x), z := z))
      thenHave(thesis) by Quantifiers.quantifyAll

    thenHave(x ∈ t ==> ∀(y, ∀(z, ((y === f(x)) /\ (z === f(x))) ==> (y === z)))) by Weakening
    thenHave(∀(x, x ∈ t ==> ∀(y, ∀(z, ((y === f(x)) /\ (z === f(x))) ==> (y === z))))) by RightForall

    have(thesis) by Cut(lastStep, conditional)

  // val definition: THM = Theorem( ∀(x, x ∈ s.map(f) <=> (x ∈ s /\ φ(x))) ):
  //   have    ( ∀(x, x ∈ y <=> (x ∈ s /\ φ(x))) |- ∀(x, x ∈ y <=> (x ∈ s /\ φ(x))) ) by Hypothesis
  //   // thenHave( ∀(x, x ∈ y <=> (x ∈ s /\ φ(x))) |- ∀(x, x ∈ ε(t, ∀(x, x ∈ t <=> (x ∈ s /\ φ(x)))) <=> (x ∈ s /\ φ(x))) ) by RightEpsilon
  //   thenHave( ∀(x, x ∈ y <=> (x ∈ s /\ φ(x))) |- ∀(x, x ∈ s.filter(φ) <=> (x ∈ s /\ φ(x))) ) by Substitution.Apply(filter.definition)
  //   thenHave( ∃(y, ∀(x, x ∈ y <=> (x ∈ s /\ φ(x)))) |- ∀(x, x ∈ s.filter(φ) <=> (x ∈ s /\ φ(x))) ) by LeftExists
  //   have(thesis) by Cut(existence, lastStep)

end Replacement