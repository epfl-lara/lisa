package ADTv2Examples.proofs

import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Types.ADTv2.library.*

object InductionOnNat extends lisa.Main {

  val n = variable[Ind]
  val prev = variable[Ind]

  val natReflexive = Theorem((n :: nat) |- n === n) {
    have(thesis) by Induction(n, nat) {
      Case(zero) subproof {
        have(thesis) by RightRefl
      }
      Case(succ, prev) subproof {
        have(thesis) by RightRefl
      }
    }
  }
}
