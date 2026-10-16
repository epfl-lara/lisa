package lisa.hol

import lisa.utils.K
import org.scalatest.funsuite.AnyFunSuite

class StepStatisticsSuite extends AnyFunSuite:
  private val p = K.Variable(K.Identifier("shape-p"), K.Prop)

  test("count sharing separately from expanded occurrences across sequents"):
    val repeated = K.and(p)(p)
    val sequent = K.Sequent(Set(p), Set(repeated))
    val shape = StepStatistics.shape(Seq(sequent, sequent))
    assert(shape == StepStatistics.Shape(formulas = 4, dagNodes = 4, treeNodes = 12, depth = 3))

  test("handle deep DAGs without recursion and saturate exponential tree size"):
    val expression = (0 until 2000).foldLeft(p: K.Expression)((term, _) => K.and(term)(term))
    val shape = StepStatistics.shape(Seq(K.Sequent(Set.empty, Set(expression))))
    assert(shape.treeNodes == Long.MaxValue)
    assert(shape.dagNodes == 4002)
    assert(shape.depth == 4001)

  test("measure empty sequents without inventing nodes"):
    assert(StepStatistics.shape(Seq(K.Sequent(Set.empty, Set.empty))) == StepStatistics.Shape(0, 0, 0, 0))
