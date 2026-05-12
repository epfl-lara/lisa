package lisa.maths.SetTheory.Types.ADTv2.interface

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.fol.FOL.{Abs, IsSort, unsafeSortEvidence}
import lisa.utils.prooflib.ProofTacticLib.Arity

import scala.compiletime.ops.int.*

type IndOf[N <: Arity] =
  N match {
    case 0 => Ind
    case S[n] => Ind >>: IndOf[n]
  }

private def indOfSortEvidence[N <: Arity](arity: Int): IsSort[IndOf[N]] = {
  val witness: Expr[?] = Abs.apply(
    xs = List.tabulate(arity)(i => variable[Ind](s"indOfArg$i")),
    t = variable[Ind]("indOfResult")
  )
  unsafeSortEvidence[IndOf[N]](witness.sort)
}

given instIndOf[N <: Arity](using valueOfN: ValueOf[N]): IsSort[IndOf[N]] =
  indOfSortEvidence(valueOfN.value)
