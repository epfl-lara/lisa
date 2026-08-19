package lisa.utils.prooflib

import lisa.utils.K
import lisa.utils.fol.FOL.{_, given}
import lisa.utils.prooflib.ProofHelpers.*
import org.scalatest.funsuite.AnyFunSuite

class SimpleDerivedStepsSuite extends AnyFunSuite:

  given testLibrary: Library = new Library

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

  private def sorry(using Library)(statement: Sequent): Thm =
    BasicStep.Sorry(statement).destruct._1

  private def assertValid(judgement: ProofJudgement): Unit =
    assert(judgement.isValid, judgement.errors.map(_.message).mkString("\n"))

  private def assertInvalid(judgement: ProofJudgement): Unit =
    assert(!judgement.isValid)
    assert(judgement.errors.nonEmpty)

  test("Generalize quantifies one right formula"):
    val premise = sorry(P(x) |- Q(y))
    assertValid(Generalize(P(x) |- forall(y, Q(y)), premise))

  test("Generalize quantifies nested variables in the right order"):
    val premise = sorry(P(z) |- R(x)(y))
    assertValid(Generalize(P(z) |- forall(x, forall(y, R(x)(y))), premise))

  test("Generalize rejects variables free on the left"):
    val premise = sorry(P(x) |- Q(x))
    assertInvalid(Generalize(P(x) |- forall(x, Q(x)), premise))

  test("InstantiateForall explicitly instantiates one quantifier"):
    val premise = sorry(() |- forall(x, P(x)))
    assertValid(InstantiateForall(a)(() |- P(a), premise))

  test("InstantiateForall explicitly instantiates nested quantifiers"):
    val premise = sorry(() |- forall(x, forall(y, R(x)(y))))
    assertValid(InstantiateForall(a, b)(() |- R(a)(b), premise))

  test("InstantiateForall weakens an implication instance"):
    val premise = sorry(() |- forall(x, P(x) ==> Q(x)))
    assertValid(InstantiateForall(a)(P(a) |- Q(a), premise))

  test("InstantiateForall infers a single instantiation term"):
    val premise = sorry(() |- forall(x, P(x)))
    assertValid(InstantiateForall(() |- P(a), premise))

  test("InstantiateForall rejects non-universal premises"):
    val premise = sorry(() |- P(a))
    assertInvalid(InstantiateForall(a)(() |- P(a), premise))

  test("Discharge removes available left formulas"):
    val available = sorry(P(a) |- Q(a))
    val premise = sorry((Q(a), R(a)(b)) |- P(b))
    val judgement = Discharge(available)(premise)
    assertValid(judgement)
    assert(judgement.destruct._1.statement == ((P(a), R(a)(b)) |- P(b)))

  test("Discharge rejects non-singleton right premises"):
    val badAvailable = sorry(P(a) |- (Q(a), Q(b)))
    val premise = sorry(Q(a) |- P(b))
    assertInvalid(Discharge(badAvailable)(premise))

  test("Substitute rewrites the right side using a formula equality on the left"):
    val premise = sorry(P(a) |- P(a))
    val judgement = Substitute(a === b)((P(a), a === b) |- P(b), premise)
    assertValid(judgement)

  test("Substitute simultaneously rewrites repeated occurrences on the right"):
    val premise = sorry(() |- (R(F(a))(F(a)) /\ R(G(a))(G(a))))
    val judgement = Substitute(F(a) === x, G(a) === y)(
      (F(a) === x, G(a) === y) |- (R(x)(x) /\ R(y)(y)),
      premise
    )
    assertValid(judgement)

  test("Substitute rewrites the left side using a formula equality on the left"):
    val premise = sorry(P(a) |- Q(a))
    val judgement = Substitute(a === b)((P(b), a === b) |- Q(a), premise)
    assertValid(judgement)

  test("Substitute rewrites the right side using an iff formula on the left"):
    val premise = sorry(P(a) |- (P(a) \/ R(a)(b)))
    val equality = R(a)(b) <=> Q(a)
    val judgement = Substitute(equality)((P(a), equality) |- (P(a) \/ Q(a)), premise)
    assertValid(judgement)

  test("Substitute rewrites the left side using an iff formula on the left"):
    val premise = sorry(R(a)(b) |- P(a))
    val equality = R(a)(b) <=> Q(a)
    val judgement = Substitute(equality)((Q(a), equality) |- P(a), premise)
    assertValid(judgement)

  test("Substitute cuts away theorem equalities"):
    val premise = sorry(P(a) |- P(a))
    val equality = sorry(() |- (a === b))
    val judgement = Substitute.from(premise, equality)(P(a) |- P(b))
    assertValid(judgement)

  test("Substitute weakens its rewritten conclusion"):
    val premise = sorry(() |- P(a))
    val equality = sorry(() |- (a === b))
    assertValid(Substitute.from(premise, equality)(Q(a) |- P(b)))

  test("Substitute carries assumptions from theorem equalities"):
    val premise = sorry(P(a) |- P(a))
    val equality = sorry(R(a)(b) |- (a === b))
    val judgement = Substitute.from(premise, equality)((P(a), R(a)(b)) |- P(b))
    assertValid(judgement)

  test("Substitute rewrites two left formulas with theorem instances"):
    val premise = sorry((P(a), P(b)) |- R(a)(b))
    val equality = sorry(() |- (P(x) <=> Q(x)))
    val judgement = Substitute.from(premise, equality.of(x := a), equality.of(x := b))(
      (Q(a), Q(b)) |- R(a)(b)
    )
    assertValid(judgement)

  test("Substitute infers instantiations from theorem rules"):
    val premise = sorry(P(a) |- P(a))
    val equality = sorry(() |- (P(x) <=> Q(x)))
    assertValid(Substitute.from(premise, equality)(P(a) |- Q(a)))

  test("Substitute infers instantiations from local proof-step rules"):
    val premise = sorry(P(a) |- P(a))
    SubproofM:
      val eq = have(() |- (P(x) <=> Q(x))) by BasicStep.Sorry
      val sub = Substitute.from(premise, eq)(P(a) |- Q(a))
      
      assertValid(sub)
      sub

  test("Substitute uniformly instantiates assumptions of local theorem rules"):
    val premise = sorry(P(a) |- P(a))
    val equality = sorry(R(x)(z) |- (P(x) <=> Q(x)))
    assertValid(Substitute.from(premise, equality)((P(a), R(a)(z)) |- Q(a)))

  test("Substitute prefers a structural rewrite over an over-general theorem instance"):
    val premise = sorry(() |- (F(x) === F(x)))
    val equality = sorry(R(x)(a) |- (x === a))
    assertValid(Substitute.from(premise, equality)(R(x)(a) |- (F(x) === F(a))))

  test("Substitute rejects a local theorem instance without its instantiated assumptions"):
    val premise = sorry(P(a) |- P(a))
    val equality = sorry(R(x)(z) |- (P(x) <=> Q(x)))
    assertInvalid(Substitute.from(premise, equality)(P(a) |- Q(a)))

  test("Substitute rejects inconsistent instantiations of a local theorem rule"):
    val premise = sorry(P(a) |- P(a))
    val equality = sorry(R(x)(z) |- (P(x) <=> Q(x)))
    assertInvalid(Substitute.from(premise, equality)((P(a), R(b)(z)) |- Q(a)))

  test("Substitute keeps raw equality formulas confined"):
    val premise = sorry(P(a) |- P(a))
    val equality = P(x) <=> Q(x)
    assertInvalid(Substitute(equality)((P(a), equality) |- Q(a), premise))

  test("Substitute rewrites through a lifted whole-function equality"):
    val premise = sorry(() |- P(F(a)))
    val equality = sorry(() |- makeEq(F, G))
    val judgement = Substitute.from(premise, equality)(() |- P(G(a)))
    assertValid(judgement)
