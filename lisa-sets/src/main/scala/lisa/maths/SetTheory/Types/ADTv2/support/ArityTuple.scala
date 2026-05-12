package lisa.maths.SetTheory.Types.ADTv2.support

import lisa.utils.prooflib.ProofTacticLib.Arity
import scala.compiletime.ops.int.S

type TupleOf[A, N <: Arity] <: Tuple = N match
  case 0 => EmptyTuple
  case S[n] => A *: TupleOf[A, n]

type **[A, N <: Arity] = TupleOf[A, N]

object ** {
  inline def apply(): EmptyTuple =
    EmptyTuple

  inline def apply[A](a1: A): A *: EmptyTuple =
    a1 *: EmptyTuple

  inline def apply[A](a1: A, a2: A): A *: A *: EmptyTuple =
    a1 *: a2 *: EmptyTuple

  inline def apply[A](a1: A, a2: A, a3: A): A *: A *: A *: EmptyTuple =
    a1 *: a2 *: a3 *: EmptyTuple

  inline def apply[A](a1: A, a2: A, a3: A, a4: A): A *: A *: A *: A *: EmptyTuple =
    a1 *: a2 *: a3 *: a4 *: EmptyTuple

  inline def apply[A](a1: A, a2: A, a3: A, a4: A, a5: A): A *: A *: A *: A *: A *: EmptyTuple =
    a1 *: a2 *: a3 *: a4 *: a5 *: EmptyTuple

  def fromSeq[A, N <: Arity](values: Seq[A]): **[A, N] =
    (values.length match
      case 0 => EmptyTuple
      case 1 => values(0) *: EmptyTuple
      case 2 => values(0) *: values(1) *: EmptyTuple
      case 3 => values(0) *: values(1) *: values(2) *: EmptyTuple
      case 4 => values(0) *: values(1) *: values(2) *: values(3) *: EmptyTuple
      case 5 => values(0) *: values(1) *: values(2) *: values(3) *: values(4) *: EmptyTuple
      case n =>
        throw new IllegalArgumentException(
          s"Unsupported arity $n. Supported arities: 0 to 5."
        )
    ).asInstanceOf[**[A, N]]
}

extension [A, N <: Arity](tuple: **[A, N]) {
  def toSeq: Seq[A] =
    tuple.productIterator.asInstanceOf[Iterator[A]].toSeq
}
