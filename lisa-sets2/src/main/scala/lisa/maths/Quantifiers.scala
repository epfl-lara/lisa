package lisa.maths

import lisa.utils.K.repr
import lisa.utils.prooflib.Library
import lisa.utils.Printing
import lisa.utils.prooflib.ProofTacticLib.ProofFactSequentTactic
import lisa.automation.Substitution

/** This file proves first-order logic theorems related to quantifiers. It includes:
  * - Quantifier elimination ([[Quantifiers.closedFormulaUniversal]],
  *   [[Quantifiers.closedFormulaExistential]])
  * - Definition of the uniqueness quantifier ([[Quantifiers.∃!]])
  * - Distribution of connectives over binders
  */
object Quantifiers extends lisa.Main {

  private val x, y, z = variable[Ind]
  private val a, b = variable[Ind]
  private val p = variable[Prop]
  private val P, Q = variable[Ind >>: Prop]


  ///////////////////////////////////////////////////////////////////////////
  section("Quantifier elimination")


  /** Theorem --- A formula is equivalent to itself universally quantified if
    * the bound variable is not free in it.
    */
  val closedFormulaUniversal = Theorem(
    ∀(x, p) <=> p
  ) {
    have(thesis) by Tableau
  }

  /** Theorem --- A formula is equivalent to itself existentially quantified if
    * the bound variable is not free in it.
    */
  val closedFormulaExistential = Theorem(
    ∃(x, p) <=> p
  ) {
    have(thesis) by Tableau
  }


  ///////////////////////////////////////////////////////////////////////////
  section("Uniqueness quantifier (∃!)")


  /** Definition --- The uniqueness quantifier `∃!x P(x)` asserts that there
    * exists a single element `x` that satisfies `P(x)`.
    */
  val ∃! = DEF(λ(P, ∃(x, P(x) /\ ∀(y, P(y) ==> (y === x))))).asBinder[Ind, Prop, Prop]

  /** Theorem --- If there exists a unique element satisfying a predicate,
    * then we can say there exists an element satisfying it as well.
    */
  val existsOneImpliesExists = Theorem(
    ∃!(x, P(x)) |- ∃(x, P(x))
  ) {
    have(P(x) /\ ∀(y, P(y) ==> (y === x)) |- P(x)) by Tautology
    thenHave(P(x) /\ ∀(y, P(y) ==> (y === x)) |- ∃(x, P(x))) by RightExists
    thenHave(∃(x, P(x) /\ ∀(y, P(y) ==> (y === x))) |- ∃(x, P(x))) by LeftExists
    thenHave(thesis) by Substitution.Apply(∃!.definition)
  }

  /** Theorem --- If there exists a unique element satisfying a predicate `P`,
    * then `εx. P` is that element.
    */
  val existsOneEpsilon = Theorem(
    ∃!(x, P(x)) |- P(ε(x, P(x)))
  ) {
    have(P(x) /\ ∀(y, P(y) ==> (y === x)) |- P(x)) by Tautology
    thenHave(P(x) /\ ∀(y, P(y) ==> (y === x)) |- P(ε(x, P(x)))) by RightEpsilon
    thenHave(∃(x, P(x) /\ ∀(y, P(y) ==> (y === x))) |- P(ε(x, P(x)))) by LeftExists
    thenHave(thesis) by Substitution.Apply(∃!.definition)
  }

  /** Theorem --- If there exists a unique element satisfying `P`, then whenever
    * both `P(x)` and `P(y)` hold we have `x === y`.
    */
  val existsOneUniqueness = Theorem(
    ∃!(x, P(x)) |- ∀(x, ∀(y, P(x) /\ P(y) ==> (x === y)))
  ) {
    have(P(x) /\ ∀(y, P(y) ==> (y === x)) |- ∀(y, P(y) ==> (y === x))) by Tautology
    thenHave(P(x) /\ ∀(y, P(y) ==> (y === x)) |- P(z) ==> (z === x)) by InstantiateForall(z)
    thenHave((P(x) /\ ∀(y, P(y) ==> (y === x)), P(z)) |- (z === x)) by Restate

    have((P(x) /\ ∀(y, P(y) ==> (y === x)), P(a), P(b)) |- (a === b)) by Congruence.from(
      lastStep of (z := a),
      lastStep of (z := b)
    )
    thenHave(P(x) /\ ∀(y, P(y) ==> (y === x)) |- P(a) /\ P(b) ==> (a === b)) by Restate
    thenHave(P(x) /\ ∀(y, P(y) ==> (y === x)) |- ∀(a, ∀(b, P(a) /\ P(b) ==> (a === b)))) by Generalize
    thenHave(∃(x, P(x) /\ ∀(y, P(y) ==> (y === x))) |- ∀(a, ∀(b, P(a) /\ P(b) ==> (a === b)))) by LeftExists
    thenHave(thesis) by Substitution.Apply(∃!.definition)
  }

  /** Theorem --- There exists a unique `x` such that `P(x)` if and only if:
    * - There exists some `x` such that `P(x)`
    * - Any two `x` and `y` such that `P(x)` and `P(y)` are equal.
    *
    * Alternative definition of [[∃!]] that breaks down the uniqueness quantifier
    * into existence and uniqueness.
    */
  val existsOneAlternativeDefinition = Theorem(
    ∃!(x, P(x)) <=> ∃(x, P(x)) /\ ∀(x, ∀(y, P(x) /\ P(y) ==> (x === y)))
  ) {
    val `==>` = have(∃!(x, P(x)) |- ∃(x, P(x)) /\ ∀(x, ∀(y, P(x) /\ P(y) ==> (x === y)))) by Tautology.from(existsOneImpliesExists, existsOneUniqueness)

    have((P(x), ∀(x, ∀(y, P(x) /\ P(y) ==> (x === y)))) |- ∃!(x, P(x))) subproof {
      assume(P(x))
      assume(∀(x, ∀(y, P(x) /\ P(y) ==> (x === y))))
      thenHave(P(x) /\ P(y) ==> (x === y)) by InstantiateForall(x, y)
      thenHave(P(y) ==> (y === x)) by Tautology
      thenHave(∀(y, P(y) ==> (y === x))) by RightForall
      thenHave(P(x) /\ ∀(y, P(y) ==> (y === x))) by Tautology
      thenHave(∃(x, P(x) /\ ∀(y, P(y) ==> (y === x)))) by RightExists
      thenHave(thesis) by Substitute(∃!.definition)
    }
    val `<==` = thenHave((∃(x, P(x)), ∀(x, ∀(y, P(x) /\ P(y) ==> (x === y)))) |- ∃!(x, P(x))) by LeftExists

    have(thesis) by Tautology.from(`==>`, `<==`)
  }


  ///////////////////////////////////////////////////////////////////////////
  section("Commutation")


  /** Theorem --- Conjunction and universal quantification commute.
    */
  val universalConjunctionCommutation = Theorem(
    ∀(x, P(x) /\ Q(x)) <=> ∀(x, P(x)) /\ ∀(x, Q(x))
  ) {
    have(thesis) by Tableau
  }

  /** Theorem -- Existential quantification distributes conjunction.
    */
  val existentialConjunctionDistribution = Theorem(
    ∃(x, P(x) /\ Q(x)) |- ∃(x, P(x)) /\ ∃(x, Q(x))
  ) {
    have(thesis) by Tableau
  }

  /** Theorem -- Existential quantification fully distributes when the
    * conjunction involves one closed formula.
    */
  val existentialConjunctionWithClosedFormula = Theorem(
    ∃(x, P(x) /\ p) <=> (∃(x, P(x)) /\ p)
  ) {
    have(thesis) by Tableau
  }

  /** Theorem -- If there is an equality on the existential quantifier's bound
    * variable inside its body, then we can reduce the existential quantifier to
    * the satisfaction of the remaining body.
    */
  val onePointRule = Theorem(
    ∃(x, P(x) /\ (y === x)) <=> P(y)
  ) {
    have(∃(x, P(x) /\ (y === x)) |- P(y)) subproof {
      have((P(x), y === x) |- P(y)) by Congruence
      thenHave(P(x) /\ (y === x) |- P(y)) by Restate
      thenHave(thesis) by LeftExists
    }
    val forward = thenHave(∃(x, P(x) /\ (y === x)) ==> P(y)) by Restate

    have(P(y) |- ∃(x, P(x) /\ (y === x))) subproof {
      have(P(x) /\ (y === x) |- P(x) /\ (y === x)) by Hypothesis
      thenHave(P(x) /\ (y === x) |- ∃(x, P(x) /\ (y === x))) by RightExists
      thenHave(P(y) /\ (y === y) |- ∃(x, P(x) /\ (y === x))) by InstSchema(x := y)
      thenHave(thesis) by Restate
    }
    val backward = thenHave(P(y) ==> ∃(x, P(x) /\ (y === x))) by Restate

    have(thesis) by RightIff(forward, backward)
  }

  /** Theorem --- Disjunction and existential quantification commute.
    */
  val existentialDisjunctionCommutation = Theorem(
    ∃(x, P(x) \/ Q(x)) <=> ∃(x, P(x)) \/ ∃(x, Q(x))
  ) {
    have(thesis) by Tableau
  }

  section("Distribution")

  /** Theorem --- Universal quantification distributes over equivalence
    */
  val universalEquivalenceDistribution = Theorem(
    ∀(z, P(z) <=> Q(z)) |- (∀(z, P(z)) <=> ∀(z, Q(z)))
  ) {
    have(thesis) by Tableau
  }

  /** Theorem --- Universal quantification of equivalence implies equivalence
    * of existential quantification.
    */
  val existentialEquivalenceDistribution = Theorem(
    ∀(z, P(z) <=> Q(z)) |- (∃(z, P(z)) <=> ∃(z, Q(z)))
  ) {
    have(thesis) by Tableau
  }

  /** Theorem --- Universal quantification of equivalence implies equivalence of
    * unique existential quantification.
    */
  val uniqueExistentialEquivalenceDistribution = Theorem(
    ∀(z, P(z) <=> Q(z)) |- (∃!(z, P(z)) <=> ∃!(z, Q(z)))
  ) {
    have(∀(z, P(z) <=> Q(z)) |- ∃(z, P(z) /\ ∀(y, P(y) ==> (y === z))) <=> ∃(z, Q(z) /\ ∀(y, Q(y) ==> (y === z)))) by Tableau
    thenHave(thesis) by Substitution.Apply(∃!.definition, ∃!.definition of (P := Q))
  }

  /** Theorem --- Universal quantification distributes over implication
    */
  val universalImplicationDistribution = Theorem(
    ∀(z, P(z) ==> Q(z)) |- (∀(z, P(z)) ==> ∀(z, Q(z)))
  ) {
    have(thesis) by Tableau
  }

  /** Theorem --- Universal quantification of implication implies implication
    * of existential quantification.
    */
  val existentialImplicationDistribution = Theorem(
    ∀(z, P(z) ==> Q(z)) |- (∃(z, P(z)) ==> ∃(z, Q(z)))
  ) {
    have(thesis) by Tableau
  }

  /** Existential substitutes for ε
    */
  val existsEpsilon = Theorem(
    ∃(x, P(x)) |- P(ε(x, P(x)))
  ) {
    have(P(x) |- P(x)) by Restate
    thenHave(P(x) |- P(ε(x, P(x)))) by RightEpsilon
    thenHave(thesis) by LeftExists
  }


}
