package ADTv2Examples.endtoend

import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Types.ADTv2.library.*
import lisa.maths.SetTheory.Types.Tactics.Typecheck

object NatAndListLibrary extends lisa.Main {

  val natList = list(nat)
  val nilNat = nil(nat)
  val consNat = cons(nat)
  val singletonZero = consNat * zero * nilNat

  val singletonZeroTyping = Theorem(singletonZero :: natList) {
    have(thesis) by Typecheck.prove
  }

  val singletonLengthTyping = Theorem(length(nat) * singletonZero :: nat) {
    have(thesis) by Typecheck.prove
  }

  section("Library theorems")
  show(double.intro)
  show(length.introAt(nat))
  show(add.elim(zero))
}
