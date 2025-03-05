package lisa.maths.settheory

import lisa.automation.Substitution

object Comprehension extends lisa.Main:

  val x = variable[Ind]
  val y = variable[Ind]
  val z = variable[Ind]
  val t = variable[Ind]
  val s = variable[Ind]

  val filter = DEF(lambda(t, lambda(φ, ε(s, ∀(x, (x ∈ s) <=> (x ∈ t /\ φ(x)))))))

  println(filter.definition.statement)

  private val comprehension: filter.type = filter

  extension (t: Expr[Ind])
    def filter(predicate: Expr[Ind >>: Prop]): Expr[Ind] =
      comprehension(t)(predicate)

  val existence = Theorem(∃(s, ∀(x, (x ∈ s) <=> (x ∈ t /\ φ(x))))):
    have(thesis) by Restate.from(comprehensionSchema of (z := t))

  val definition: THM = Theorem(∀(x, x ∈ s.filter(φ) <=> (x ∈ s /\ φ(x)))):
    have(∀(x, x ∈ y <=> (x ∈ s /\ φ(x))) |- ∀(x, x ∈ y <=> (x ∈ s /\ φ(x)))) by Hypothesis
    thenHave(∀(x, x ∈ y <=> (x ∈ s /\ φ(x))) |- ∀(x, x ∈ ε(t, ∀(x, x ∈ t <=> (x ∈ s /\ φ(x)))) <=> (x ∈ s /\ φ(x)))) by RightEpsilon
    thenHave(∀(x, x ∈ y <=> (x ∈ s /\ φ(x))) |- ∀(x, x ∈ s.filter(φ) <=> (x ∈ s /\ φ(x)))) by Substitution.Apply(filter.definition of (t := s))
    thenHave(∃(y, ∀(x, x ∈ y <=> (x ∈ s /\ φ(x)))) |- ∀(x, x ∈ s.filter(φ) <=> (x ∈ s /\ φ(x)))) by LeftExists
    have(thesis) by Cut.withParameters(∃(t, ∀(x, (x ∈ t) <=> (x ∈ s /\ φ(x)))))(existence of (t := s), lastStep)

end Comprehension
