package lisa.hol

import lisa.utils.K
import java.util.IdentityHashMap

/** Measure sequent shape only when per-step profiling is enabled; retain no trees between calls. */
private[hol] object StepStatistics:
  val rules = Set("MK_COMB", "EQ_MP", "DEDUCT_ANTISYM_RULE")
  final case class Shape(formulas: Int, dagNodes: Int, treeNodes: Long, depth: Int)

  private def add(a: Long, b: Long): Long = if Long.MaxValue - a < b then Long.MaxValue else a + b

  /** Count distinct object nodes and expanded occurrences; saturate expanded size on overflow. */
  def shape(sequents: Seq[K.Sequent]): Shape =
    val roots = sequents.flatMap(s => s.left.toSeq ++ s.right.toSeq)
    val sizes = new IdentityHashMap[K.Expression, (Long, Int)]
    var pending = roots.toList.map(_ -> false)
    while pending.nonEmpty do
      val (expression, visited) = pending.head
      pending = pending.tail
      if !sizes.containsKey(expression) then
        val children = expression match
          case K.Application(f, arg) => List(f, arg)
          case K.Lambda(v, body) => List(v, body)
          case _ => Nil
        if !visited && children.nonEmpty then
          pending = children.map(_ -> false) ::: (expression -> true) :: pending
        else
          val size = children.foldLeft(1L)((sum, child) => add(sum, sizes.get(child)._1))
          val depth = 1 + children.map(child => sizes.get(child)._2).maxOption.getOrElse(0)
          sizes.put(expression, size -> depth)
    Shape(roots.size, sizes.size(), roots.foldLeft(0L)((sum, root) => add(sum, sizes.get(root)._1)), roots.map(sizes.get(_)._2).maxOption.getOrElse(0))
