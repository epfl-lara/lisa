package lisa.utils.prooflib

import lisa.utils.K
import lisa.utils.fol.FOL.{_, given}
import org.scalatest.funsuite.AnyFunSuite

class AutomationSuite extends AnyFunSuite:

  given testLibrary: Library = new Library

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

  private def sorry(using Library)(statement: Sequent): Thm =
    BasicStep.Sorry(statement).destruct._1

  private def assertValid(judgement: ProofJudgement): Unit =
    assert(judgement.isValid, judgement.errors.map(_.message).mkString("\n"))

  test("Tautology proves propositional sequents"):
    assertValid(Tautology(() |- (((a ==> b) /\ (b ==> c)) ==> (a ==> c))))

  test("Tautology rejects non-tautologies"):
    val judgement = Tautology(() |- a)
    assert(!judgement.isValid)
    assert(judgement.errors.nonEmpty)

  test("Tautology uses and discharges theorem premises"):
    val premise = sorry(a |- b)
    assertValid(Tautology.from(premise)(a |- b))

  test("Tableau proves quantified sequents"):
    assertValid(Tableau(() |- (forall(x, P(x)) ==> P(y))))
    assertValid(Tableau(() |- ((forall(x, P(x) ==> Q(x)) /\ exists(x, P(x))) ==> exists(x, Q(x)))))
    assertValid(Tableau(() |- (exists(x, exists(y, P(x) /\ Q(y))) ==> exists(y, exists(x, P(x) /\ Q(y))))))
    assertValid(Tableau(() |- !forall(x, P(x) /\ !P(F(x)))))

  test("Tableau uses and discharges theorem premises"):
    val premise = sorry(() |- forall(x, P(x)))
    assertValid(Tableau.from(premise)(() |- P(y)))

  test("Tableau rejects open branches"):
    val judgement = Tableau(() |- forall(x, P(x)))
    assert(!judgement.isValid)
    assert(judgement.errors.nonEmpty)

  test("Congruence rewrites function and predicate arguments"):
    assertValid(Congruence((x === y) |- (F(x) === F(y))))
    assertValid(Congruence((x === y, P(x)) |- P(y)))

  test("Congruence composes equality chains"):
    assertValid(Congruence((x === y, y === z) |- (F(x) === F(z))))
    assertValid(Congruence((x === y) |- (F(F(x)) === F(F(y)))))

  test("Congruence combines projection equalities"):
    val leftProjection = sorry(() |- (F(H(y)(z)) === y))
    val rightProjection = sorry(() |- (G(H(y)(z)) === z))
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
    assertValid(Congruence((a <=> b) |- ((a /\ c) <=> (b /\ c))))
    assertValid(Congruence((x === y, x === z) |- (R(x)(x) <=> R(y)(z))))

  test("Congruence closes contradictory equalities"):
    assertValid(Congruence((x === y, !(F(x) === F(y))) |- ()))

  test("Congruence uses theorem premises"):
    val premise = sorry(() |- (x === y))
    assertValid(Congruence.from(premise)(() |- (F(x) === F(y))))
    val conditionalPremise = sorry(P(x) |- (x === y))
    assertValid(Congruence.from(conditionalPremise)(P(x) |- (F(x) === F(y))))

  test("Congruence chains conditional theorem premises"):
    val result = sorry((b, c) |- d)
    val first = sorry(a |- b)
    val second = sorry(() |- c)
    assertValid(Congruence.from(result, first, second)(a |- d))

  test("Congruence keeps goal assumptions supplied as premises"):
    val redundant = sorry(a |- a)
    val equality = sorry(() |- (a <=> b))
    assertValid(Congruence.from(redundant, equality)(a |- b))

  test("Congruence rejects unrelated equalities"):
    val judgement = Congruence((x === y) |- (F(x) === F(z)))
    assert(!judgement.isValid)
    assert(judgement.errors.nonEmpty)
