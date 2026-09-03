package lisa.maths.SetTheory.Types.ADTv2.interface

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.utils.fol.FOL.Abs
import lisa.utils.fol.FOL.Sort
import lisa.utils.fol.FOL.unsafeSortEvidence
import lisa.utils.prooflib.ProofTacticLib.Arity

import scala.compiletime.ops.int._

type IndOf[N <: Arity] =
  N match {
    case 0 => Ind
    case S[n] => Ind >>: IndOf[n]
  }

private def indOfSortEvidence[N <: Arity](arity: Int): Sort[IndOf[N]] = {
  val witness: Expr[?] = Abs.apply(
    xs = List.tabulate(arity)(i => variable[Ind](s"indOfArg$i")),
    t = variable[Ind]("indOfResult")
  )
  unsafeSortEvidence[IndOf[N]](witness.sort)
}

given instIndOf[N <: Arity](using valueOfN: ValueOf[N]): Sort[IndOf[N]] =
  indOfSortEvidence(valueOfN.value)
