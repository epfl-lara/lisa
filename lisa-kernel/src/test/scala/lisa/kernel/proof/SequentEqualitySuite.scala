package lisa.kernel.proof

import lisa.kernel.fol.FOL.*
import org.scalatest.funsuite.AnyFunSuite

class SequentEqualitySuite extends AnyFunSuite:
  private val p = Variable(Identifier("sequent-equality-p"), Prop)
  private val q = Variable(Identifier("sequent-equality-q"), Prop)

  test("accept equal sequents regardless of set construction order"):
    val first = Sequent(Set(p, q), Set(p))
    val second = Sequent(List(q, p).toSet, List(p).toSet)
    assert(!(first eq second))
    assert(isSameSequent(first, second))

  test("retain OL and beta equivalence for syntactically different sequents"):
    val x = Variable(Identifier("sequent-equality-x"), Prop)
    val first = Sequent(Set(p, q), Set.empty)
    val second = Sequent(Set(and(p)(q)), Set.empty)
    assert(first != second)
    assert(isSameSequent(first, second))
    assert(isSameSequent(Sequent(Set.empty, Set(Lambda(x, x)(p))), Sequent(Set.empty, Set(p))))

  test("reject inequivalent sequents and preserve Restate dependencies and theory checks"):
    val theory = Theory.empty
    val statement = Sequent(Set.empty, Set(p))
    val premise = Assume(using theory)(statement).toOption.get
    assert(!isSameSequent(statement, Sequent(Set.empty, Set(q))))
    val result = Restate(using theory)(statement.copy(), premise).toOption.get
    assert(result.assumptions == premise.assumptions)
    assert(Restate(using Theory.empty)(statement, premise).isLeft)
