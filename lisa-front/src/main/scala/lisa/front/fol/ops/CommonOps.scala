package lisa.front.fol.ops

import lisa.front.fol.definitions.CommonDefinitions

import scala.compiletime.ops.int.-

trait CommonOps extends CommonDefinitions {

  /**
   * Creates a tuple type with <code>N</code> types <code>T</code>.
   * @tparam T the type of that tuple's members
   * @tparam N the arity of that tuple
   */
  protected type FillTuple[T, N <: Arity] <: Tuple & Matchable = N match {
    case 0 => EmptyTuple
    case _ => T *: FillTuple[T, N - 1]
  }

  /**
   * Similar to [[FillTuple]], except that for convenience when used as function arguments, the tuple of arity one
   * is replaced by its own element.
   * @tparam T
   * @tparam N
   */
  type FillArgs[T <: Matchable, N <: Arity] <: (T | Tuple) & Matchable = N match {
    case 1 => T
    case _ => FillTuple[T, N]
  }

  //given liftArgsConversion1[U, V]: Conversion[V, FillArgs[U, 0] => V] = v => _ => v
  //given liftArgsConversion2[U, V]: Conversion[() => V, FillArgs[U, 0] => V] = v => _ => v()

  private[front] def fillTupleParameters[N <: Arity, T <: Matchable, U](name: String => T, n: N, f: FillArgs[T, N] => U, taken: Set[String] = Set.empty): (FillArgs[T, N], U) = {
    val newIds = LazyList.from(0).map(i => s"x$i").filter(!taken.contains(_)).take(n).toIndexedSeq
    val parameters = fillTuple[T, N](n, i => name(newIds(i)))
    (parameters, f(parameters))
  }

  protected def tuple2seq[T <: Matchable, N <: Arity](any: FillArgs[T, N]): Seq[T] =
    any match {
      case tuple: Tuple => tuple.productIterator.toSeq.asInstanceOf[Seq[T]]
      case _ => Seq(any.asInstanceOf[T]) // Safe cast
    }

  /**
   * Fills a tuple with <code>n</code> elements of type <code>T</code>.
   * @param n the arity of the tuple
   * @param f the function generating the elements
   * @tparam T the type of the elements
   * @tparam N the arity type
   * @return the generated tuple
   */
  def fillTuple[T <: Matchable, N <: Arity](n: N, f: Int => T): FillArgs[T, N] =
    if(n == 1)
      f(0).asInstanceOf[FillArgs[T, N]]
    else
      (0 until n).foldRight(EmptyTuple: Tuple)((i, acc) => f(i) *: acc).asInstanceOf[FillArgs[T, N]]

  extension [T <: Matchable, N <: Arity](tuple: FillArgs[T, N]) {
    /**
     * Converts a tuple into a sequence of value. Loses all typing information, but simplifies the usage.
     */
    def toSeq: Seq[T] = tuple2seq(tuple)
  }

}
