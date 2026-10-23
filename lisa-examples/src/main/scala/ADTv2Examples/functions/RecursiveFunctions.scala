package ADTv2Examples.functions

import lisa.maths.SetTheory.Types.ADTv2.library.*

object RecursiveFunctions extends lisa.Main {

  section("Boolean recursion")
  show(not.intro)
  show(not.elim(tru))
  show(not.elim(fals))

  section("Natural number recursion")
  show(double.intro)
  show(double.elim(zero))
  show(double.elim(succ))

  section("Polymorphic list recursion")
  show(length.intro(nat))
  show(length.elim(nat)(nil))
  show(length.elim(nat)(cons))
}
