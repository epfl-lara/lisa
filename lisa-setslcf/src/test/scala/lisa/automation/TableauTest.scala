package lisa.test.automation

import lisa.automation.Tableau.solve
import lisa.kernel.proof.SCProofChecker.checkSCProof
import org.scalatest.funsuite.AnyFunSuite

class TableauTest extends AnyFunSuite with lisa.TestMain {

  given lib: lisa.SetTheoryLibrary.type = lisa.SetTheoryLibrary

  // --- Individual variables ---
  private val u = variable[Ind]
  private val w = variable[Ind]
  private val x = variable[Ind]
  private val y = variable[Ind]
  private val z = variable[Ind]
  private val h2 = variable[Ind]

  // --- Propositional variables ---
  private val a = variable[Prop]
  private val b = variable[Prop]
  private val c = variable[Prop]
  private val d = variable[Prop]

  // --- Function variables ---
  private val f = variable[Ind >>: Ind]
  private val g = variable[Ind >>: Ind]
  private val h = variable[Ind >>: Ind >>: Ind]

  // --- Predicate variables ---
  private val D = variable[Ind >>: Prop]
  private val E = variable[Ind >>: Ind >>: Prop]
  private val P = variable[Ind >>: Prop]
  private val Q = variable[Ind >>: Prop]
  private val R = variable[Ind >>: Ind >>: Prop]

  /**
   * Solve a formula and return (proofFound, proofValid).
   */
  private def solveAndCheck(formula: Expr[Prop]): (Boolean, Boolean) = {
    val res = Tableau.solve(() |- formula)
    res match
      case None => (false, false)
      case Some(proof) =>
        val judgement = checkSCProof(proof)
        (true, judgement.isValid)
  }

  // ========================================================================
  // Propositional
  // ========================================================================

  private val propFormulas: List[Expr[Prop]] = List(
    a <=> a,
    a \/ !a,
    ((a ==> b) /\ (b ==> c)) ==> (a ==> c),
    (a <=> b) <=> ((a /\ b) \/ (!a /\ !b)),
    ((a ==> c) /\ (b ==> c)) <=> ((a \/ b) ==> c),
    ((a ==> b) /\ (c ==> d)) ==> ((a \/ c) ==> (b \/ d))
  )

  test("Propositional Positive cases") {
    val results = propFormulas.zipWithIndex.map { case (formula, i) =>
      val (found, valid) = solveAndCheck(formula)
      (i, formula, found, valid)
    }
    val failures = results.filterNot(_._3)
    assert(failures.isEmpty, failures.map(r => s"#${r._1}: ${r._2}").mkString("Not proved: ", ", ", ""))
    val invalidProofs = results.filter(r => r._3 && !r._4)
    assert(invalidProofs.isEmpty, invalidProofs.map(r => s"#${r._1}").mkString("Invalid proof: ", ", ", ""))
  }

  // ========================================================================
  // First Order – Quantifier Free
  // ========================================================================

  private val qfFormulas: List[Expr[Prop]] = List(
    propFormulas.map(fo => fo.substitute(a := P(h(x)(h2)), b := P(x), c := R(x)(h(x)(h2)))),
    propFormulas.map(fo => fo.substitute(a := P(h(x)(h2)), b := P(h(x)(h2)), c := R(x)(h(x)(h2)))),
    propFormulas.map(fo => fo.substitute(a := R(y)(y), b := P(h(y)(h2)), c := R(h(x)(y))(h2)))
  ).flatten

  test("First Order Quantifier-Free Positive cases") {
    val results = qfFormulas.zipWithIndex.map { case (formula, i) =>
      val (found, valid) = solveAndCheck(formula)
      (i, formula, found, valid)
    }
    val failures = results.filterNot(_._3)
    assert(failures.isEmpty, failures.map(r => s"#${r._1}: ${r._2}").mkString("Not proved: ", ", ", ""))
    val invalidProofs = results.filter(r => r._3 && !r._4)
    assert(invalidProofs.isEmpty, invalidProofs.map(r => s"#${r._1}").mkString("Invalid proof: ", ", ", ""))
  }

  // ========================================================================
  // First Order – Easy (quantified substitutions)
  // ========================================================================

  private val easyFormulas: List[Expr[Prop]] = List(
    propFormulas.map(fo => fo.substitute(a := ∀(x, P(x)), b := ∀(x, P(y)), c := ∃(x, P(x)))),
    propFormulas.map(fo => fo.substitute(a := ∀(x, P(x) /\ Q(f(x))), b := ∀(x, P(x) \/ R(y)(x)), c := ∃(x, Q(x) ==> R(x)(y)))),
    propFormulas.map(fo => fo.substitute(a := ∃(y, ∀(x, P(x) /\ Q(f(y)))), b := ∀(y, ∃(x, P(x) \/ R(y)(x))), c := ∀(y, ∃(x, Q(x) ==> R(x)(y)))))
  ).flatten

  test("Regression test for proof reconstruction failure in delta") {
    val a = variable[Prop]
    val b = ∀(y, ∃(x, P(x)))
    val formula = (a <=> b) ==> ((a /\ b) \/ (!a /\ !b))
    val (found, valid) = solveAndCheck(formula)
    assert(found, s"Tableau should find a proof for $formula")
    assert(valid, s"Proof found for $formula should be valid")
  }

  test("First Order Easy Positive cases") {
    val results = easyFormulas.zipWithIndex.map { case (formula, i) =>
      val (found, valid) = solveAndCheck(formula)
      (i, formula, found, valid)
    }
    val failures = results.filterNot(_._3)
    assert(failures.isEmpty, failures.map(r => s"#${r._1}: ${r._2}").mkString("Not proved: ", ", ", ""))
    val invalidProofs = results.filter(r => r._3 && !r._4)
    assert(invalidProofs.isEmpty, invalidProofs.map(r => s"#${r._1}: ${r._2}, proofFound: ${r._3}, proofValid: ${r._4}").mkString("Invalid proof: \n", "\n", ""))
  }

  // ========================================================================
  // First Order – Hard (from Isabelle FOL-ex/Quantifiers_Cla.html)
  // ========================================================================

  private val a1 = ∀(x, ∀(y, ∀(z, ((E(x)(y) /\ E(y)(z)) ==> E(x)(z)))))
  private val a2 = ∀(x, ∀(y, (E(x)(y) ==> E(f(x))(f(y)))))
  private val a3 = ∀(x, E(f(g(x)))(g(f(x))))
  private val biga = ∀(
    x,
    ∀(
      y,
      ∀(
        z,
        ((E(x)(y) /\ E(y)(z)) ==> E(x)(z)) /\
          (E(x)(y) ==> E(f(x))(f(y))) /\
          E(f(g(x)))(g(f(x)))
      )
    )
  )

  private val hardFormulas: List[Expr[Prop]] = List(
    ∀(x, P(x) ==> Q(x)) ==> (∀(x, P(x)) ==> ∀(x, Q(x))),
    ∀(x, ∀(y, R(x)(y))) ==> ∀(y, ∀(x, R(x)(y))),
    ∀(x, ∀(y, R(x)(y))) ==> ∀(y, ∀(x, R(y)(x))),
    ∃(x, ∃(y, R(x)(y))) ==> ∃(y, ∃(x, R(x)(y))),
    ∃(x, ∃(y, R(x)(y))) ==> ∃(y, ∃(x, R(y)(x))),
    (∀(x, P(x)) \/ ∀(x, Q(x))) ==> ∀(x, P(x) \/ Q(x)),
    ∀(x, a ==> Q(x)) <=> (a ==> ∀(x, Q(x))),
    ∀(x, P(x) ==> a) <=> (∃(x, P(x)) ==> a),
    ∃(x, P(x) \/ Q(x)) <=> (∃(x, P(x)) \/ ∃(x, Q(x))),
    ∃(x, P(x) /\ Q(x)) ==> (∃(x, P(x)) /\ ∃(x, Q(x))),
    ∃(y, ∀(x, R(x)(y))) ==> ∀(x, ∃(y, R(x)(y))),
    ∀(x, Q(x)) ==> ∃(x, Q(x)),
    (∀(x, P(x) ==> Q(x)) /\ ∃(x, P(x))) ==> ∃(x, Q(x)),
    ((a ==> ∃(x, Q(x))) /\ a) ==> ∃(x, Q(x)),
    ∀(x, P(x) ==> Q(f(x))) /\ ∀(x, Q(x) ==> R(g(x))(x)) ==> (P(y) ==> R(g(f(y)))(f(y))),
    ∀(x, ∀(y, P(x) ==> Q(y))) ==> (∃(x, P(x)) ==> ∀(y, Q(y))),
    (∃(x, P(x)) ==> ∀(y, Q(y))) ==> ∀(x, ∀(y, P(x) ==> Q(y))),
    ∀(x, ∀(y, P(x) ==> Q(y))) <=> (∃(x, P(x)) ==> ∀(y, Q(y))),
    ∃(x, ∃(y, P(x) /\ R(x)(y))) ==> ∃(x, P(x) /\ ∃(y, R(x)(y))),
    ∃(x, P(x) /\ ∃(y, R(x)(y))) ==> ∃(x, ∃(y, P(x) /\ R(x)(y))),
    ∃(x, ∃(y, P(x) /\ R(x)(y))) <=> ∃(x, P(x) /\ ∃(y, R(x)(y))),
    ∃(y, ∀(x, P(x) ==> R(x)(y))) ==> (∀(x, P(x)) ==> ∃(y, R(x)(y))),
    ∀(x, P(x)) ==> P(y),
    !(∀(x, D(x) /\ !D(f(x)))),
    !(∀(x, (D(x) /\ !D(f(x))) \/ (D(x) /\ !D(x)))),
    ∀(x, ∀(y, (E(x)(y) ==> E(f(x))(f(y))) /\ E(f(g(x)))(g(f(x))))) ==> E(f(f(g(u))))(f(g(f(u)))),
    !(∀(x, !(E(f(x))(x))) /\ ∀(x, ∀(y, !(E(x)(y)) /\ E(f(x))(g(x))))),
    a1 /\ a2 /\ a3 ==> E(f(f(g(u))))(f(g(f(u)))),
    a1 /\ a2 /\ a3 ==> E(f(g(f(u))))(g(f(f(u)))),
    biga ==> E(f(f(g(u))))(f(g(f(u)))),
    biga ==> E(f(g(f(u))))(g(f(f(u))))
  )

  test("First Order Hard Positive cases") {
    val results = hardFormulas.zipWithIndex.map { case (formula, i) =>
      val (found, valid) = solveAndCheck(formula)
      (i, formula, found, valid)
    }
    val failures = results.filterNot(_._3)
    assert(failures.isEmpty, failures.map(r => s"#${r._1}: ${r._2}").mkString("Not proved: ", ", ", ""))
    val invalidProofs = results.filter(r => r._3 && !r._4)
    assert(invalidProofs.isEmpty, invalidProofs.map(r => s"#${r._1}").mkString("Invalid proof: ", ", ", ""))
  }

  // ========================================================================
  // StackOverflow regression tests
  // ========================================================================

  test("triggerStackOverflow1 - Skolem dependency loop (abstracted set theory)") {
    // ∃(z, U(z) ∧ P(z)), ∀(z, U(z) ⟺ ∃(R, E(R)(w) ∧ E(z)(R))) ⊢ ∃(y, E(y)(w) ∧ ∃(z, E(z)(y) ∧ Q(z)))
    val tE = variable[Ind >>: Ind >>: Prop]
    val tP = variable[Ind >>: Prop]
    val tQ = variable[Ind >>: Prop]
    val formula = ∃(z, tP(z) /\ tQ(z)) /\ ∀(z, tP(z) <=> ∃(u, tE(u)(w) /\ tE(z)(u))) ==> ∃(y, tE(y)(w) /\ ∃(z, tE(z)(y) /\ tQ(z)))
    val (found, valid) = solveAndCheck(formula)
    assert(found, "Tableau should find a proof for triggerStackOverflow1")
    assert(valid, "Proof for triggerStackOverflow1 should be valid")
  }

  test("triggerStackOverflow2 - minimal ∀∃/∀∀¬ loop") {
    // ∀x.∃y.R(x,y) and ∀u.∀z.¬R(z,u) are contradictory
    val tR = variable[Ind >>: Ind >>: Prop]
    val formula = (∀(x, ∃(y, tR(x)(y))) /\ ∀(u, ∀(z, !tR(z)(u)))) ==> bot
    val (found, valid) = solveAndCheck(formula)
    assert(found, "Tableau should find a proof for triggerStackOverflow2")
    assert(valid, "Proof for triggerStackOverflow2 should be valid")
  }

}