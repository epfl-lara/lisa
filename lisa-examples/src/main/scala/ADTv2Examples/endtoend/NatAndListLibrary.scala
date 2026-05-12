package ADTv2Examples.endtoend

import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Types.ADTv2.library.*
import lisa.maths.SetTheory.Types.Tactics.Typecheck

object NatAndListLibrary extends lisa.Main {

  val list1 = cons(nat) * zero * nil(nat)
  val list2 = cons(nat) * (succ * zero) * list1

  section("Introduction rules")
  show(nil.intro(nat))
  show(cons.intro(nat))
  show(length.intro(nat))

  section("Type checking")

  val nilTyping = Theorem(nil(nat) :: list(nat)) {
    have(thesis) by Typecheck.prove
  }

  val nilLengthTyping = 
    Theorem(length(nat) * nil(nat) :: nat) {
    have(thesis) by Typecheck.prove
  }
  val list1LengthTyping = Theorem(length(nat) * list1 :: nat) {
    have(thesis) by Typecheck.prove
  }
  val list2LengthTyping = Theorem(length(nat) * list2 :: nat) {
    have(thesis) by Typecheck.prove
  }

  section("Library theorems")
  show(double.intro)
  show(add.elim(zero))
  show(add.elim(succ))
}
