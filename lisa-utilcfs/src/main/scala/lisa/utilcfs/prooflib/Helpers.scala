package lisa.utilcfs.prooflib

import lisa.kernelcf.proof.Helpers as KH
import lisa.utilcfs.fol.FOL.*

object Helpers:

  inline def expEq[S, T](s: Expr[S], t: Expr[T]): Boolean =
    KH.expEq(s.underlying, t.underlying)

  extension [S](set: Set[Expr[S]])
    inline def containsEq[T](formula: Expr[T]): Boolean =
      KH.containsEq(set.map(_.underlying))(formula.underlying)

    inline def subsetOfEq[T](target: Set[Expr[T]]): Boolean =
      KH.subsetOfEq(set.map(_.underlying))(target.map(_.underlying))

    inline def containedExcept[T, U](target: Set[Expr[T]], exception: Expr[U]): Boolean =
      KH.containedExcept(set.map(_.underlying))(target.map(_.underlying), exception.underlying)

    inline def containedExceptEither[T, U, V](target: Set[Expr[T]], exception1: Expr[U], exception2: Expr[V]): Boolean =
      KH.containedExceptEither(set.map(_.underlying))(target.map(_.underlying), exception1.underlying, exception2.underlying)
