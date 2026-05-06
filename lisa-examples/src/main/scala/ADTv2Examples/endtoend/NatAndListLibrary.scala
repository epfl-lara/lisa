package ADTv2Examples.endtoend

import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Types.ADTv2.library.*
import lisa.maths.SetTheory.Types.Tactics.Typecheck

object NatAndListLibrary extends lisa.Main {

  val natList = list.specialize(nat)
  val nilNat = nil.specialize(nat)
  val consNat = cons.specialize(nat)
  val singletonZero = consNat * zero * nilNat

  val singletonZeroTyping = Theorem(singletonZero :: natList) {
    have(thesis) by Typecheck.prove
  }

  val singletonLengthTyping = Theorem(length.specialize(nat) * singletonZero :: nat) {
    have(thesis) by Typecheck.prove
  }

  section("Library theorems")
  show(double.intro)
  show(length.specialize(nat).intro)
  show(add.elim(zero))
}
