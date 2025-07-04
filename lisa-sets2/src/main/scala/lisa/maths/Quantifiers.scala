package lisa.maths

import lisa.utils.K.repr
import lisa.utils.prooflib.Library
import lisa.utils.Printing
import lisa.utils.prooflib.ProofTacticLib.ProofFactSequentTactic
import lisa.automation.Substitution

/** This file proves first-order logic theorems related to quantifiers. It includes:
  * - Closed formulas under binders ([[Quantifiers.closedFormulaUniversal]],
  *   [[Quantifiers.closedFormulaExistential]])
  * - Definition of the uniqueness quantifier ([[Quantifiers.∃!]])
  */
object Quantifiers extends lisa.Main {

  private val X, Y = variable[Prop]
  private val x, y, z = variable[Ind]
  private val a, b = variable[Ind]
  private val p = variable[Prop]
  private val P, Q = variable[Ind >>: Prop]
  private val Phi = variable[Prop >>: Prop]

  section("Closed formulas")

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

  /*

  /**
   * Theorem --- if atleast two distinct elements exist, then there is no unique
   * existence
   */
  val atleastTwoExist = Theorem(
    (∃(x, P(x)) /\ !existsOne(x, P(x))) <=> ∃(x, ∃(y, P(x) /\ P(y) /\ !(x === y)))
  ) {
    val fwd = have((∃(x, P(x)) /\ !existsOne(x, P(x))) ==> ∃(x, ∃(y, P(x) /\ P(y) /\ !(x === y)))) subproof {
      have((P(x), ((x === y) /\ !P(y))) |- P(x) /\ !P(y)) by Restate
      have((P(x), ((x === y) /\ !P(y))) |- P(y) /\ !P(y)) by Sorry //Substitution.ApplyRules(x === y) // contradiction
      val xy = thenHave((P(x), ((x === y) /\ !P(y))) |- ∃(x, ∃(y, P(x) /\ P(y) /\ !(x === y)))) by Weakening

      have((P(x), (!(x === y) /\ P(y))) |- (!(x === y) /\ P(y) /\ P(x))) by Restate
      thenHave((P(x), (!(x === y) /\ P(y))) |- ∃(y, !(x === y) /\ P(y) /\ P(x))) by RightExists
      val nxy = thenHave((P(x), (!(x === y) /\ P(y))) |- ∃(x, ∃(y, !(x === y) /\ P(y) /\ P(x)))) by RightExists

      have((P(x), (!(x === y) /\ P(y)) \/ ((x === y) /\ !P(y))) |- ∃(x, ∃(y, P(x) /\ P(y) /\ !(x === y)))) by Tautology.from(xy, nxy)
      thenHave((P(x), ∃(y, (!(x === y) /\ P(y)) \/ ((x === y) /\ !P(y)))) |- ∃(x, ∃(y, P(x) /\ P(y) /\ !(x === y)))) by LeftExists
      thenHave((P(x), ∀(x, ∃(y, (!(x === y) /\ P(y)) \/ ((x === y) /\ !P(y))))) |- ∃(x, ∃(y, P(x) /\ P(y) /\ !(x === y)))) by LeftForall
      thenHave((∃(x, P(x)), ∀(x, ∃(y, (!(x === y) /\ P(y)) \/ ((x === y) /\ !P(y))))) |- ∃(x, ∃(y, P(x) /\ P(y) /\ !(x === y)))) by LeftExists

      thenHave(thesis) by Restate
    }

    val bwd = have(∃(x, ∃(y, P(x) /\ P(y) /\ !(x === y))) ==> (∃(x, P(x)) /\ !existsOne(x, P(x)))) subproof {
      have((P(x), P(y), !(x === y)) |- P(x)) by Restate
      val ex = thenHave((P(x), P(y), !(x === y)) |- ∃(x, P(x))) by RightExists

      have((P(x), P(y), !(x === y)) |- P(y) /\ !(y === x)) by Restate
      have((P(x), P(y), !(x === y), (x === z)) |- P(y) /\ !(y === z)) by Sorry //Substitution.ApplyRules(x === z)
      thenHave((P(x), P(y), !(x === y), (x === z)) |- (P(y) /\ !(y === z)) \/ (!P(y) /\ (y === z))) by Weakening
      val xz = thenHave((P(x), P(y), !(x === y), (x === z)) |- ∃(y, (P(y) /\ !(y === z)) \/ (!P(y) /\ (y === z)))) by RightExists

      have((P(x), P(y), !(x === y), !(x === z)) |- (P(x) /\ !(x === z)) \/ (!P(x) /\ (x === z))) by Restate
      val nxz = thenHave((P(x), P(y), !(x === y), !(x === z)) |- ∃(x, (P(x) /\ !(x === z)) \/ (!P(x) /\ (x === z)))) by RightExists

      have((P(x), P(y), !(x === y)) |- ∃(x, (P(x) /\ !(x === z)) \/ (!P(x) /\ (x === z)))) by Tautology.from(xz, nxz)
      thenHave((P(x), P(y), !(x === y)) |- ∀(z, ∃(x, (P(x) /\ !(x === z)) \/ (!P(x) /\ (x === z))))) by RightForall
      val uex = thenHave(P(x) /\ P(y) /\ !(x === y) |- !existsOne(z, P(z))) by Restate

      have(P(x) /\ P(y) /\ !(x === y) |- ∃(x, P(x)) /\ !existsOne(z, P(z))) by Tautology.from(ex, uex)
      thenHave(∃(y, P(x) /\ P(y) /\ !(x === y)) |- ∃(x, P(x)) /\ !existsOne(z, P(z))) by LeftExists
      thenHave(∃(x, ∃(y, P(x) /\ P(y) /\ !(x === y))) |- ∃(x, P(x)) /\ !existsOne(z, P(z))) by LeftExists

      thenHave(thesis) by Restate
    }

    have(thesis) by Tautology.from(fwd, bwd)
  }

   */

}
