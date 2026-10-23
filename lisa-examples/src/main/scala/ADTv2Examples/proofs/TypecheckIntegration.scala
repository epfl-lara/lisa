package ADTv2Examples.proofs

import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Types.ADTv2.library.*
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.maths.SetTheory.Functions.Pi.{->:}

object TypecheckIntegration extends lisa.Main {

  val n = variable[Ind]
  val b = variable[Ind]

  section("Constructor heads")

  val zeroTyping = Theorem(zero :: nat) {
    have(thesis) by Typecheck.prove
  }

  val succTyping = Theorem(succ :: (nat ->: nat)) {
    have(thesis) by Typecheck.prove
  }

  val truTyping = Theorem(tru :: bool) {
    have(thesis) by Typecheck.prove
  }

  section("Constructor applications")

  val succZeroTyping = Theorem(succ * zero :: nat) {
    have(thesis) by Typecheck.prove
  }

  val succSuccTyping = Theorem((n :: nat) |- succ * (succ * n) :: nat) {
    have(thesis) by Typecheck.prove
  }

  section("Recursive-function heads")

  val doubleTyping = Theorem(double :: (nat ->: nat)) {
    have(thesis) by Typecheck.prove
  }

  val negTyping = Theorem(not :: (bool ->: bool)) {
    have(thesis) by Typecheck.prove
  }

  section("Nested terms")

  val doubleZeroTyping = Theorem(double * zero :: nat) {
    have(thesis) by Typecheck.prove
  }

  val nestedNatTyping = Theorem((n :: nat) |- succ * (double * n) :: nat) {
    have(thesis) by Typecheck.prove
  }

  val nestedBoolTyping = Theorem((b :: bool) |- not * (not * b) :: bool) {
    have(thesis) by Typecheck.prove
  }
}
