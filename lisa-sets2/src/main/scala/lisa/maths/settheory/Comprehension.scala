package lisa.maths.settheory

import lisa.automation.Substitution

object Comprehension extends lisa.Main:

  val x = variable[Term]
  val y = variable[Term]
  val z = variable[Term]
  val t = variable[Term]
  val s = variable[Term]

  val filter = DEF ( lambda(t, lambda(φ, ε(s, ∀(x, (x ∈ s) <=> (x ∈ t /\ φ(x)))))) )

  val comprehension: filter.type = filter

  extension (t: Term)
    def filter(predicate: Term >>: Formula): Term =
      comprehension(t)(predicate)

  val existence = Theorem( ∃(s, ∀(x, (x ∈ s) <=> (x ∈ t /\ φ(x)))) ):
    have(thesis) by Restate.from(comprehensionSchema of (z := t))

  val definition: THM = Theorem( ∀(x, x ∈ s.filter(φ) <=> (x ∈ s /\ φ(x))) ):
    have    ( ∀(x, x ∈ y <=> (x ∈ s /\ φ(x))) |- ∀(x, x ∈ y <=> (x ∈ s /\ φ(x))) ) by Hypothesis
    thenHave( ∀(x, x ∈ y <=> (x ∈ s /\ φ(x))) |- ∀(x, x ∈ ε(t, ∀(x, x ∈ t <=> (x ∈ s /\ φ(x)))) <=> (x ∈ s /\ φ(x))) ) by RightEpsilon
    thenHave( ∀(x, x ∈ y <=> (x ∈ s /\ φ(x))) |- ∀(x, x ∈ s.filter(φ) <=> (x ∈ s /\ φ(x))) ) by Substitution.Apply(filter.definition)
    thenHave( ∃(y, ∀(x, x ∈ y <=> (x ∈ s /\ φ(x)))) |- ∀(x, x ∈ s.filter(φ) <=> (x ∈ s /\ φ(x))) ) by LeftExists
    have(thesis) by Cut(existence, lastStep)

end Comprehension