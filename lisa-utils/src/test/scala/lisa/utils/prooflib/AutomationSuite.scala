package lisa.utils.prooflib

import lisa.utils.K
import lisa.utils.fol.FOL.{*, given}
import org.scalatest.funsuite.AnyFunSuite

class AutomationSuite extends AnyFunSuite:
  private class TestLibrary extends Library

  private val a = variable[Prop]
  private val b = variable[Prop]
  private val c = variable[Prop]
  private val d = variable[Prop]
  private val x = variable[Ind]
  private val y = variable[Ind]
  private val z = variable[Ind]
  private val P = variable[Ind >>: Prop]
  private val Q = variable[Ind >>: Prop]
  private val F = variable[Ind >>: Ind]
  private val G = variable[Ind >>: Ind]
  private val H = variable[Ind >>: Ind >>: Ind]
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

  test("Congruence combines projection equalities"):
    given Library = TestLibrary()
    val leftProjection = axiom(() |- (F(H(y)(z)) === y))
    val rightProjection = axiom(() |- (G(H(y)(z)) === z))
    val conclusion = (x === H(y)(z)) |- (x === H(F(x))(G(x)))
    val egraph = EGraphExpr()
    egraph.addAll(conclusion.left ++ conclusion.right + leftProjection.right.head + rightProjection.right.head)
    egraph.merge(x, H(y)(z))
    egraph.merge(F(H(y)(z)), y)
    egraph.merge(G(H(y)(z)), z)
    assert(egraph.idEq(F(x), y), "left projection did not close")
    assert(egraph.idEq(G(x), z), "right projection did not close")
    assert(egraph.idEq(x, H(F(x))(G(x))), "outer constructor did not close")
    val allLeft = conclusion.left + leftProjection.right.head + rightProjection.right.head
    val unordered = EGraphExpr()
    unordered.addAll(allLeft ++ conclusion.right)
    allLeft.foreach:
      case equality(left, right) => unordered.merge(left, right)
      case _ => ()
    assert(unordered.idEq(x, H(F(x))(G(x))), s"unordered closure failed for ${allLeft.mkString(", ")}")
    val reconstructed = unordered.proveExpr(x, H(F(x))(G(x)), Sequent(allLeft, conclusion.right))
    assert(reconstructed.isRight, reconstructed.left.toOption.getOrElse(""))
    assertValid(Congruence.from(leftProjection, rightProjection)(conclusion))

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

  test("Congruence chains conditional theorem premises"):
    given Library = TestLibrary()
    val result = axiom((b, c) |- d)
    val first = axiom(a |- b)
    val second = axiom(() |- c)
    assertValid(Congruence.from(result, first, second)(a |- d))

  test("Congruence keeps goal assumptions supplied as premises"):
    given Library = TestLibrary()
    val redundant = axiom(a |- a)
    val equality = axiom(() |- (a <=> b))
    assertValid(Congruence.from(redundant, equality)(a |- b))

  test("Congruence rejects unrelated equalities"):
    given Library = TestLibrary()
    val judgement = Congruence((x === y) |- (F(x) === F(z)))
    assert(!judgement.isValid)
    assert(judgement.errors.nonEmpty)
