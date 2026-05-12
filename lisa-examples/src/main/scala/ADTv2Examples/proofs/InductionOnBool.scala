package ADTv2Examples.proofs

import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Types.ADTv2.library.*

object InductionOnBool extends lisa.Main {

  val b = variable[Ind]

  val negNegIsId = Theorem((b :: bool) |- not * (not * b) === b) {
    val negFalse = have(not * fals === tru) by Restate.from(not.elim(fals))
    val negTrue = have(not * tru === fals) by Restate.from(not.elim(tru))

    have(thesis) by Induction(b, bool) {
      Case(tru) subproof {
        have(not * (not * tru) === tru) by Congruence.from(negTrue, negFalse)
      }
      Case(fals) subproof {
        have(not * (not * fals) === fals) by Congruence.from(negTrue, negFalse)
      }
    }
  }
}
