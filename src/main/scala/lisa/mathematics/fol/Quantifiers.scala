package lisa.mathematics
package fol

import lisa.automation.Tableau
import lisa.automation.kernel.OLPropositionalSolver.Tautology
import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.prooflib.Substitution

/**
 * Implements theorems about first-order logic.
 */
object Quantifiers extends lisa.Main {

  private val x = variable
  private val y = variable
  private val z = variable
  private val a = variable
  private val b = variable
  private val c = variable
  private val p = formulaVariable
  private val P = predicate[1]
  private val Q = predicate[1]

  /**
   * Theorem --- A formula is equivalent to itself universally quantified if
   * the bound variable is not free in it.
   */
  val closedFormulaUniversal = Theorem(
    () |- ∀(x, p) <=> p
  ) {
    have(thesis) by Tableau
  }

  /**
   * Theorem --- A formula is equivalent to itself existentially quantified if
   * the bound variable is not free in it.
   */
  val closedFormulaExistential = Theorem(
    () |- ∃(x, p) <=> p
  ) {
    have(thesis) by Tableau
  }

  /**
   * Theorem --- If there exists a *unique* element satisfying a predicate,
   * then we can say there *exists* an element satisfying it as well.
   */
  val existsOneImpliesExists = Theorem(
    ∃!(x, P(x)) |- ∃(x, P(x))
  ) {
    have((x === y) <=> P(y) |- (x === y) <=> P(y)) by Hypothesis
    thenHave(∀(y, (x === y) <=> P(y)) |- (x === y) <=> P(y)) by LeftForall
    thenHave(∀(y, (x === y) <=> P(y)) |- P(x)) by InstFunSchema(Map(y -> x))
    thenHave(∀(y, (x === y) <=> P(y)) |- ∃(x, P(x))) by RightExists
    thenHave(∃(x, ∀(y, (x === y) <=> P(y))) |- ∃(x, P(x))) by LeftExists
    thenHave(thesis) by Restate
  }

  /**
   * Theorem --- Equality relation is transitive.
   */
  val equalityTransitivity = Theorem(
    (x === y) /\ (y === z) |- (x === z)
  ) {
    have((x === y) |- (x === y)) by Hypothesis
    thenHave(((x === y), (y === z)) |- (x === z)) by RightSubstEq.apply2
    thenHave(thesis) by Restate
  }

  /**
   * Theorem --- Conjunction and universal quantification commute.
   */
  val universalConjunctionCommutation = Theorem(
    () |- forall(x, P(x) /\ Q(x)) <=> forall(x, P(x)) /\ forall(x, Q(x))
  ) {
    have(thesis) by Tableau
  }

  /**
   * Theorem -- Existential quantification distributes conjunction.
   */
  val existentialConjunctionDistribution = Theorem(
    exists(x, P(x) /\ Q(x)) |- exists(x, P(x)) /\ exists(x, Q(x))
  ) {
    have(thesis) by Tableau
  }

  /**
   * Theorem -- Existential quantification fully distributes when the conjunction involves one closed formula.
   */
  val existentialConjunctionWithClosedFormula = Theorem(
    exists(x, P(x) /\ p) <=> (exists(x, P(x)) /\ p)
  ) {
    have(thesis) by Tableau
  }

  /**
   * Theorem -- If there is an equality on the existential quantifier's bound variable inside its body, then we can reduce
   * the existential quantifier to the satisfaction of the remaining body.
   */
  val equalityInExistentialQuantifier = Theorem(
    exists(x, P(x) /\ (y === x)) <=> P(y)
  ) {
    have(exists(x, P(x) /\ (y === x)) |- P(y)) subproof {
      have(P(x) |- P(x)) by Hypothesis
      thenHave((P(x), y === x) |- P(y)) by RightSubstEq.withParameters(List((y, x)), lambda(y, P(y)))
      thenHave(P(x) /\ (y === x) |- P(y)) by Restate
      thenHave(thesis) by LeftExists
    }
    val forward = thenHave(exists(x, P(x) /\ (y === x)) ==> P(y)) by Restate

    have(P(y) |- exists(x, P(x) /\ (y === x))) subproof {
      have(P(x) /\ (y === x) |- P(x) /\ (y === x)) by Hypothesis
      thenHave(P(x) /\ (y === x) |- exists(x, P(x) /\ (y === x))) by RightExists
      thenHave(P(y) /\ (y === y) |- exists(x, P(x) /\ (y === x))) by InstFunSchema(Map(x -> y))
      thenHave(thesis) by Restate
    }
    val backward = thenHave(P(y) ==> exists(x, P(x) /\ (y === x))) by Restate

    have(thesis) by RightIff(forward, backward)
  }

  /**
   * Theorem --- Disjunction and existential quantification commute.
   */
  val existentialDisjunctionCommutation = Theorem(
    () |- exists(x, P(x) \/ Q(x)) <=> exists(x, P(x)) \/ exists(x, Q(x))
  ) {
    have(thesis) by Tableau
  }

  /**
   * Theorem --- Universal quantification distributes over equivalence
   */
  val universalEquivalenceDistribution = Theorem(
    forall(z, P(z) <=> Q(z)) |- (forall(z, P(z)) <=> forall(z, Q(z)))
  ) {
    have(thesis) by Tableau
  }

  /**
   * Theorem --- Universal quantification of equivalence implies equivalence
   * of existential quantification.
   */
  val existentialEquivalenceDistribution = Theorem(
    forall(z, P(z) <=> Q(z)) |- (exists(z, P(z)) <=> exists(z, Q(z)))
  ) {
    have(thesis) by Tableau

  }

  /**
   * Theorem --- Universal quantification distributes over implication
   */
  val universalImplicationDistribution = Theorem(
    forall(z, P(z) ==> Q(z)) |- (forall(z, P(z)) ==> forall(z, Q(z)))
  ) {
    have(thesis) by Tableau
  }

  /**
   * Theorem --- Universal quantification of implication implies implication
   * of existential quantification.
   */
  val existentialImplicationDistribution = Theorem(
    forall(z, P(z) ==> Q(z)) |- (exists(z, P(z)) ==> exists(z, Q(z)))
  ) {
    have(thesis) by Tableau
  }

  /**
   * Theorem --- Universal quantification of equivalence implies equivalence
   * of unique existential quantification.
   */
  val uniqueExistentialEquivalenceDistribution = Theorem(
    forall(z, P(z) <=> Q(z)) |- (existsOne(z, P(z)) <=> existsOne(z, Q(z)))
  ) {
    val yz = have(forall(z, P(z) <=> Q(z)) |- ((y === z) <=> P(y)) <=> ((y === z) <=> Q(y))) subproof {
      have(forall(z, P(z) <=> Q(z)) |- forall(z, P(z) <=> Q(z))) by Hypothesis
      val quant = thenHave(forall(z, P(z) <=> Q(z)) |- P(y) <=> Q(y)) by InstantiateForall(y)

      val lhs = have((forall(z, P(z) <=> Q(z)), ((y === z) <=> P(y))) |- ((y === z) <=> Q(y))) subproof {
        have((P(y) <=> Q(y), ((y === z) <=> P(y))) |- ((y === z) <=> Q(y))) by Tautology
        have(thesis) by Tautology.from(lastStep, quant)
      }
      val rhs = have((forall(z, P(z) <=> Q(z)), ((y === z) <=> Q(y))) |- ((y === z) <=> P(y))) subproof {
        have((P(y) <=> Q(y), ((y === z) <=> Q(y))) |- ((y === z) <=> P(y))) by Tautology
        have(thesis) by Tautology.from(lastStep, quant)
      }

      have(thesis) by Tautology.from(lhs, rhs)
    }

    val fy = thenHave(forall(z, P(z) <=> Q(z)) |- forall(y, ((y === z) <=> P(y)) <=> ((y === z) <=> Q(y)))) by RightForall

    have(forall(y, P(y) <=> Q(y)) |- (forall(y, P(y)) <=> forall(y, Q(y)))) by Restate.from(universalEquivalenceDistribution)
    val univy = thenHave(forall(y, ((y === z) <=> P(y)) <=> ((y === z) <=> Q(y))) |- (forall(y, ((y === z) <=> P(y))) <=> forall(y, ((y === z) <=> Q(y))))) by InstPredSchema(
      Map((P -> lambda(y, (y === z) <=> P(y))), (Q -> lambda(y, (y === z) <=> Q(y))))
    )

    have(forall(z, P(z) <=> Q(z)) |- (forall(y, ((y === z) <=> P(y))) <=> forall(y, ((y === z) <=> Q(y))))) by Cut(fy, univy)

    thenHave(forall(z, P(z) <=> Q(z)) |- forall(z, forall(y, ((y === z) <=> P(y))) <=> forall(y, ((y === z) <=> Q(y))))) by RightForall
    have(forall(z, P(z) <=> Q(z)) |- exists(z, forall(y, ((y === z) <=> P(y)))) <=> exists(z, forall(y, ((y === z) <=> Q(y))))) by Cut(
      lastStep,
      existentialEquivalenceDistribution of (P -> lambda(z, forall(y, (y === z) <=> P(y))), Q -> lambda(z, forall(y, (y === z) <=> Q(y))))
    )

    thenHave(thesis) by Restate
  }

  /**
   * Theorem --- if atleast two distinct elements exist, then there is no unique
   * existence
   */
  val atleastTwoExist = Theorem(
    (exists(x, P(x)) /\ !existsOne(x, P(x))) <=> exists(x, exists(y, P(x) /\ P(y) /\ !(x === y)))
  ) {
    val fwd = have((exists(x, P(x)) /\ !existsOne(x, P(x))) ==> exists(x, exists(y, P(x) /\ P(y) /\ !(x === y)))) subproof {
      have((P(x), ((x === y) /\ !P(y))) |- P(x) /\ !P(y)) by Restate
      thenHave((P(x), ((x === y) /\ !P(y))) |- P(y) /\ !P(y)) by Substitution.ApplyRules(x === y) // contradiction
      val xy = thenHave((P(x), ((x === y) /\ !P(y))) |- exists(x, exists(y, P(x) /\ P(y) /\ !(x === y)))) by Weakening

      have((P(x), (!(x === y) /\ P(y))) |- (!(x === y) /\ P(y) /\ P(x))) by Restate
      thenHave((P(x), (!(x === y) /\ P(y))) |- exists(y, !(x === y) /\ P(y) /\ P(x))) by RightExists
      val nxy = thenHave((P(x), (!(x === y) /\ P(y))) |- exists(x, exists(y, !(x === y) /\ P(y) /\ P(x)))) by RightExists

      have((P(x), (!(x === y) /\ P(y)) \/ ((x === y) /\ !P(y))) |- exists(x, exists(y, P(x) /\ P(y) /\ !(x === y)))) by Tautology.from(xy, nxy)
      thenHave((P(x), exists(y, (!(x === y) /\ P(y)) \/ ((x === y) /\ !P(y)))) |- exists(x, exists(y, P(x) /\ P(y) /\ !(x === y)))) by LeftExists
      thenHave((P(x), forall(x, exists(y, (!(x === y) /\ P(y)) \/ ((x === y) /\ !P(y))))) |- exists(x, exists(y, P(x) /\ P(y) /\ !(x === y)))) by LeftForall
      thenHave((exists(x, P(x)), forall(x, exists(y, (!(x === y) /\ P(y)) \/ ((x === y) /\ !P(y))))) |- exists(x, exists(y, P(x) /\ P(y) /\ !(x === y)))) by LeftExists

      thenHave(thesis) by Restate
    }

    val bwd = have(exists(x, exists(y, P(x) /\ P(y) /\ !(x === y))) ==> (exists(x, P(x)) /\ !existsOne(x, P(x)))) subproof {
      have((P(x), P(y), !(x === y)) |- P(x)) by Restate
      val ex = thenHave((P(x), P(y), !(x === y)) |- exists(x, P(x))) by RightExists

      have((P(x), P(y), !(x === y)) |- P(y) /\ !(y === x)) by Restate
      thenHave((P(x), P(y), !(x === y), (x === z)) |- P(y) /\ !(y === z)) by Substitution.ApplyRules(x === z)
      thenHave((P(x), P(y), !(x === y), (x === z)) |- (P(y) /\ !(y === z)) \/ (!P(y) /\ (y === z))) by Weakening
      val xz = thenHave((P(x), P(y), !(x === y), (x === z)) |- exists(y, (P(y) /\ !(y === z)) \/ (!P(y) /\ (y === z)))) by RightExists

      have((P(x), P(y), !(x === y), !(x === z)) |- (P(x) /\ !(x === z)) \/ (!P(x) /\ (x === z))) by Restate
      val nxz = thenHave((P(x), P(y), !(x === y), !(x === z)) |- exists(x, (P(x) /\ !(x === z)) \/ (!P(x) /\ (x === z)))) by RightExists

      have((P(x), P(y), !(x === y)) |- exists(x, (P(x) /\ !(x === z)) \/ (!P(x) /\ (x === z)))) by Tautology.from(xz, nxz)
      thenHave((P(x), P(y), !(x === y)) |- forall(z, exists(x, (P(x) /\ !(x === z)) \/ (!P(x) /\ (x === z))))) by RightForall
      val uex = thenHave(P(x) /\ P(y) /\ !(x === y) |- !existsOne(z, P(z))) by Restate

      have(P(x) /\ P(y) /\ !(x === y) |- exists(x, P(x)) /\ !existsOne(z, P(z))) by Tautology.from(ex, uex)
      thenHave(exists(y, P(x) /\ P(y) /\ !(x === y)) |- exists(x, P(x)) /\ !existsOne(z, P(z))) by LeftExists
      thenHave(exists(x, exists(y, P(x) /\ P(y) /\ !(x === y))) |- exists(x, P(x)) /\ !existsOne(z, P(z))) by LeftExists

      thenHave(thesis) by Restate
    }

    have(thesis) by Tautology.from(fwd, bwd)
  }

}
