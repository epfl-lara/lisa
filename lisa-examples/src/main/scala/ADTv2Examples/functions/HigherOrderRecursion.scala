package ADTv2Examples.functions

import lisa.maths.SetTheory.Types.ADTv2.library.*

object HigherOrderRecursion extends lisa.Main {

  section("Recursive functions returning functions")
  show(add.intro)
  show(add.introApp)
  show(add.elim(zero))
  show(add.elim(succ))
}
