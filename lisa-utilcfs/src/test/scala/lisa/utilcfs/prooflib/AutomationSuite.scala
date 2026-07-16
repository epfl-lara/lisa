package lisa.utilcfs.prooflib

import lisa.utilcfs.K
import lisa.utilcfs.fol.FOL.{*, given}
import org.scalatest.funsuite.AnyFunSuite

class AutomationSuite extends AnyFunSuite:
  private class TestLibrary extends Library

  private val a = variable[Prop]
  private val b = variable[Prop]
  private val c = variable[Prop]
  private val x = variable[Ind]
  private val y = variable[Ind]
  private val z = variable[Ind]
  private val P = variable[Ind >>: Prop]
  private val Q = variable[Ind >>: Prop]
  private val F = variable[Ind >>: Ind]
  private val R = variable[Ind >>: Ind >>: Prop]

  private def axiom(using library: Library)(statement: Sequent): Thm =
    K.Axiom(using library.theory)(statement.underlying) match
      case Right(thm) => Thm(statement, thm)

  private def assertValid(judgement: ProofJudgement): Unit =
    assert(judgement.isValid, judgement.errors.map(_.message).mkString("\n"))
    assert(!judgement.destruct._1.kernel.usesSorry)

  test("Tautology proves propositional sequents"):
    given Library = TestLibrary()
    assertValid(Tautology(() |- (((a ==> b) /\ (b ==> c)) ==> (a ==> c))))

  test("Tautology rejects non-tautologies"):
    given Library = TestLibrary()
    val judgement = Tautology(() |- a)
    assert(!judgement.isValid)
    assert(judgement.errors.nonEmpty)

  test("Tautology uses and discharges theorem premises"):
    given Library = TestLibrary()
    val premise = axiom(a |- b)
    assertValid(Tautology.from(premise)(a |- b))

  test("Tableau proves quantified sequents"):
    given Library = TestLibrary()
    assertValid(Tableau(() |- (forall(x, P(x)) ==> P(y))))
    assertValid(Tableau(() |- ((forall(x, P(x) ==> Q(x)) /\ exists(x, P(x))) ==> exists(x, Q(x)))))
    assertValid(Tableau(() |- (exists(x, exists(y, P(x) /\ Q(y))) ==> exists(y, exists(x, P(x) /\ Q(y))))))
    assertValid(Tableau(() |- !forall(x, P(x) /\ !P(F(x)))))

  test("Tableau uses and discharges theorem premises"):
    given Library = TestLibrary()
    val premise = axiom(() |- forall(x, P(x)))
    assertValid(Tableau.from(premise)(() |- P(y)))

  test("Tableau rejects open branches"):
    given Library = TestLibrary()
    val judgement = Tableau(() |- forall(x, P(x)))
    assert(!judgement.isValid)
    assert(judgement.errors.nonEmpty)

  test("Congruence rewrites function and predicate arguments"):
    given Library = TestLibrary()
    assertValid(Congruence((x === y) |- (F(x) === F(y))))
    assertValid(Congruence((x === y, P(x)) |- P(y)))

  test("Congruence composes equality chains"):
    given Library = TestLibrary()
    assertValid(Congruence((x === y, y === z) |- (F(x) === F(z))))
    assertValid(Congruence((x === y) |- (F(F(x)) === F(F(y)))))

  test("Congruence rewrites formula arguments"):
    given Library = TestLibrary()
    assertValid(Congruence((a <=> b) |- ((a /\ c) <=> (b /\ c))))
    assertValid(Congruence((x === y, x === z) |- (R(x)(x) <=> R(y)(z))))

  test("Congruence closes contradictory equalities"):
    given Library = TestLibrary()
    assertValid(Congruence((x === y, !(F(x) === F(y))) |- ()))

  test("Congruence uses theorem premises"):
    given Library = TestLibrary()
    val premise = axiom(() |- (x === y))
    assertValid(Congruence.from(premise)(() |- (F(x) === F(y))))
    val conditionalPremise = axiom(P(x) |- (x === y))
    assertValid(Congruence.from(conditionalPremise)(P(x) |- (F(x) === F(y))))

  test("Congruence rejects unrelated equalities"):
    given Library = TestLibrary()
    val judgement = Congruence((x === y) |- (F(x) === F(z)))
    assert(!judgement.isValid)
    assert(judgement.errors.nonEmpty)
