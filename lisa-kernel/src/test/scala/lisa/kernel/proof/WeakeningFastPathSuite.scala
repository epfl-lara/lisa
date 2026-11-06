package lisa.kernel.proof

import lisa.kernel.fol.FOL.*
import org.scalatest.funsuite.AnyFunSuite

class WeakeningFastPathSuite extends AnyFunSuite:
  private val p = Variable(Identifier("weakening-p"), Prop)
  private val q = Variable(Identifier("weakening-q"), Prop)

  test("agree with the existing OL check across exact, reordered and compound contexts"):
    given Theory = Theory.empty
    val contexts = Vector(Set.empty[Expression], Set(p), Set(q), Set(p, q), Set(and(p)(q)), Set(or(p)(q)))
    val statements = for left <- contexts; right <- contexts yield Sequent(left, right)
    for from <- statements; to <- statements do
      val premise = Assume(from).toOption.get
      assert(Weakening(to, premise).isRight == isImplyingSequent(from, to), s"$from -> $to")

  test("preserve open dependencies and reject cross-theory premises on the fast path"):
    val first = Theory.empty
    val second = Theory.empty
    val source = Sequent(Set.empty, Set(p))
    val target = Sequent(Set(q), Set(p, q))
    val premise = Assume(using first)(source).toOption.get
    val result = Weakening(using first)(target, premise).toOption.get
    assert(result.assumptions == Set(source))
    assert(result.statement == target)
    assert(result.rule == Weakening)
    assert(Weakening(using second)(target, premise).left.toOption.exists(_.isInstanceOf[TheoryMismatch]))

  test("retain OL-only weakenings and reject premise removal"):
    given Theory = Theory.empty
    val premise = Assume(Sequent(Set(p), Set.empty)).toOption.get
    val target = Sequent(Set(and(p)(q)), Set.empty)
    assert(!premise.left.subsetOf(target.left))
    assert(Weakening(target, premise).isRight)
    assert(Weakening(Sequent(Set.empty, Set.empty), premise).isLeft)
