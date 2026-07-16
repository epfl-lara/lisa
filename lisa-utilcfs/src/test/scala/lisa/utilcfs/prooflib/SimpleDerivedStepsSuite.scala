package lisa.utilcfs.prooflib

import lisa.utilcfs.K
import lisa.utilcfs.fol.FOL.{_, given}
import org.scalatest.funsuite.AnyFunSuite

class SimpleDerivedStepsSuite extends AnyFunSuite:
  private class TestLibrary extends Library

  private val x = variable[Ind]
  private val y = variable[Ind]
  private val z = variable[Ind]
  private val a = variable[Ind]
  private val b = variable[Ind]
  private val P = variable[Ind >>: Prop]
  private val Q = variable[Ind >>: Prop]
  private val R = variable[Ind >>: Ind >>: Prop]
  private val F = variable[Ind >>: Ind]
  private val G = variable[Ind >>: Ind]

  private def axiom(using library: Library)(statement: Sequent): Thm =
    K.Axiom(using library.theory)(statement.underlying) match
      case Right(thm) => Thm(statement, thm)

  private def assertValid(judgement: ProofJudgement): Unit =
    assert(judgement.isValid, judgement.errors.map(_.message).mkString("\n"))
    assert(!judgement.destruct._1.kernel.usesSorry)

  private def assertInvalid(judgement: ProofJudgement): Unit =
    assert(!judgement.isValid)
    assert(judgement.errors.nonEmpty)

  test("Generalize quantifies one right formula"):
    given Library = TestLibrary()
    val premise = axiom(P(x) |- Q(y))
    assertValid(Generalize(P(x) |- forall(y, Q(y)), premise))

  test("Generalize quantifies nested variables in the right order"):
    given Library = TestLibrary()
    val premise = axiom(P(z) |- R(x)(y))
    assertValid(Generalize(P(z) |- forall(x, forall(y, R(x)(y))), premise))

  test("Generalize rejects variables free on the left"):
    given Library = TestLibrary()
    val premise = axiom(P(x) |- Q(x))
    assertInvalid(Generalize(P(x) |- forall(x, Q(x)), premise))

  test("InstantiateForall explicitly instantiates one quantifier"):
    given Library = TestLibrary()
    val premise = axiom(() |- forall(x, P(x)))
    assertValid(InstantiateForall(a)(() |- P(a), premise))

  test("InstantiateForall explicitly instantiates nested quantifiers"):
    given Library = TestLibrary()
    val premise = axiom(() |- forall(x, forall(y, R(x)(y))))
    assertValid(InstantiateForall(a, b)(() |- R(a)(b), premise))

  test("InstantiateForall infers a single instantiation term"):
    given Library = TestLibrary()
    val premise = axiom(() |- forall(x, P(x)))
    assertValid(InstantiateForall(() |- P(a), premise))

  test("InstantiateForall rejects non-universal premises"):
    given Library = TestLibrary()
    val premise = axiom(() |- P(a))
    assertInvalid(InstantiateForall(a)(() |- P(a), premise))

  test("Discharge removes available left formulas"):
    given Library = TestLibrary()
    val available = axiom(P(a) |- Q(a))
    val premise = axiom((Q(a), R(a)(b)) |- P(b))
    val judgement = Discharge(available)(premise)
    assertValid(judgement)
    assert(judgement.destruct._1.statement == ((P(a), R(a)(b)) |- P(b)))

  test("Discharge rejects non-singleton right premises"):
    given Library = TestLibrary()
    val badAvailable = axiom(P(a) |- (Q(a), Q(b)))
    val premise = axiom(Q(a) |- P(b))
    assertInvalid(Discharge(badAvailable)(premise))

  test("Substitute rewrites the right side using a formula equality on the left"):
    given Library = TestLibrary()
    val premise = axiom(P(a) |- P(a))
    val judgement = Substitute(a === b)((P(a), a === b) |- P(b), premise)
    assertValid(judgement)

  test("Substitute rewrites the left side using a formula equality on the left"):
    given Library = TestLibrary()
    val premise = axiom(P(a) |- Q(a))
    val judgement = Substitute(a === b)((P(b), a === b) |- Q(a), premise)
    assertValid(judgement)

  test("Substitute rewrites the right side using an iff formula on the left"):
    given Library = TestLibrary()
    val premise = axiom(P(a) |- (P(a) \/ R(a)(b)))
    val equality = R(a)(b) <=> Q(a)
    val judgement = Substitute(equality)((P(a), equality) |- (P(a) \/ Q(a)), premise)
    assertValid(judgement)

  test("Substitute rewrites the left side using an iff formula on the left"):
    given Library = TestLibrary()
    val premise = axiom(R(a)(b) |- P(a))
    val equality = R(a)(b) <=> Q(a)
    val judgement = Substitute(equality)((Q(a), equality) |- P(a), premise)
    assertValid(judgement)

  test("Substitute cuts away theorem equalities"):
    given Library = TestLibrary()
    val premise = axiom(P(a) |- P(a))
    val equality = axiom(() |- (a === b))
    val judgement = Substitute.from(premise, equality)(P(a) |- P(b))
    assertValid(judgement)

  test("Substitute rewrites through a lifted whole-function equality"):
    given Library = TestLibrary()
    val premise = axiom(() |- P(F(a)))
    val equality = axiom(() |- makeEq(F, G))
    val judgement = Substitute.from(premise, equality)(() |- P(G(a)))
    assertValid(judgement)
