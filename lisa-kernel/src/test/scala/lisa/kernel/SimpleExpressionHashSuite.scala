package lisa.kernel

import lisa.kernel.fol.FOL.*
import org.scalatest.funsuite.AnyFunSuite

import scala.collection.immutable.HashSet

class SimpleExpressionHashSuite extends AnyFunSuite:
  private def expressions(): Seq[SimpleExpression] =
    val id = Identifier("hash-x")
    val x = SimpleVariable(id, Ind, true)
    val p = SimpleVariable(Identifier("hash-p"), Prop, true)
    Seq(
      x,
      SimpleBoundVariable(0, Ind, true),
      SimpleConstant(Identifier("hash-f"), Ind -> Ind, true),
      SimpleApplication(SimpleConstant(Identifier("hash-f"), Ind -> Ind, true), x, true),
      SimpleLambda(Variable(id, Ind), x),
      SimpleAnd(Seq(p, SimpleLiteral(false)), true),
      SimpleForall(id, p, true),
      SimpleLiteral(true),
      SimpleEquality(x, SimpleVariable(Identifier("hash-y"), Ind, true), true)
    )

  test("equal simple expressions with distinct IDs share hashes and hash-set entries"):
    expressions().zip(expressions()).foreach: (left, right) =>
      assert(left.uniqueKey != right.uniqueKey)
      assert(left == right)
      assert(left.hashCode == right.hashCode)
      assert(HashSet(left).contains(right))
      assert(HashSet(left, right).size == 1)

  test("structural hash collisions do not identify different expressions"):
    val left = SimpleVariable(Identifier("Aa"), Prop, true)
    val right = SimpleVariable(Identifier("BB"), Prop, true)
    assert(left.hashCode == right.hashCode)
    assert(left != right)
    assert(HashSet(left, right).size == 2)

  test("normalization caches do not change expression hashes or set membership"):
    val left = expressions().last
    val equal = expressions().last
    val hash = left.hashCode
    val set = HashSet(left)

    getInversePolar(left)
    toLocallyNameless(left)
    computeNormalForm(left)
    toExpressionAIG(left)
    toExpressionNNF(left, true)

    assert(left.hashCode == hash)
    assert(left == equal)
    assert(left.hashCode == equal.hashCode)
    assert(set.contains(equal))

  test("repeated hashes do not traverse conjunction children again"):
    var visits = 0
    val child = SimpleLiteral(true)
    val children = new scala.collection.immutable.AbstractSeq[SimpleExpression]:
      def length: Int = 8
      def apply(index: Int): SimpleExpression =
        require(index >= 0 && index < length)
        visits += 1
        child
      def iterator: Iterator[SimpleExpression] = Iterator.range(0, length).map(apply)

    val expression = SimpleAnd(children, true)
    val hash = expression.hashCode
    val firstVisits = visits
    assert(firstVisits > 0)
    (0 until 10).foreach(_ => assert(expression.hashCode == hash))
    assert(visits == firstVisits)
