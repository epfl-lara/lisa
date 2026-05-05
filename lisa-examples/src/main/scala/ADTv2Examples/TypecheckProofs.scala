import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Types.ADTv2.basics.Nat.*
import lisa.maths.SetTheory.Types.ADTv2.basics.Bool.*
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.maths.SetTheory.Functions.Pi.{->:}

object TypecheckProofs extends lisa.Main {

  val n = variable[Ind]
  val b = variable[Ind]

  val idNat = recFun(nat, nat) { self =>
    Case(zero):
      zero
    Case(succ, n):
      succ * (self * n)
  }

  val addOne = recFun(nat, nat) { self =>
    Case(zero):
      succ * zero
    Case(succ, n):
      succ * (self * n)
  }

  val flip = recFun(bool, bool) { self =>
    Case(tru):
      fals
    Case(fals):
      tru
  }

  section("Easy constructor heads")

  val zeroTyping = Theorem(zero :: nat) {
    have(thesis) by Typecheck.prove
  }

  val succTyping = Theorem(succ :: (nat ->: nat)) {
    have(thesis) by Typecheck.prove
  }

  val truTyping = Theorem(tru :: bool) {
    have(thesis) by Typecheck.prove
  }

  val falsTyping = Theorem(fals :: bool) {
    have(thesis) by Typecheck.prove
  }

  section("Constructor applications")

  val succZeroTyping = Theorem(succ * zero :: nat) {
    have(thesis) by Typecheck.prove
  }

  val succSuccTyping = Theorem((n :: nat) |- succ * (succ * n) :: nat) {
    have(thesis) by Typecheck.prove
  }

  val boolVariableTyping = Theorem((b :: bool) |- b :: bool) {
    have(thesis) by Typecheck.prove
  }

  section("Recursive-function heads")

  val idNatTyping = Theorem(idNat :: (nat ->: nat)) {
    have(thesis) by Typecheck.prove
  }

  val addOneTyping = Theorem(addOne :: (nat ->: nat)) {
    have(thesis) by Typecheck.prove
  }

  val flipTyping = Theorem(flip :: (bool ->: bool)) {
    have(thesis) by Typecheck.prove
  }

  section("Nested terms")

  val idNatOnSuccTyping = Theorem((idNat :: (nat ->: nat), n :: nat) |- idNat * (succ * n) :: nat) {
    have(thesis) by Typecheck.prove
  }

  val addOneOnIdNatTyping = Theorem(
    (idNat :: (nat ->: nat), addOne :: (nat ->: nat), n :: nat) |- addOne * (idNat * n) :: nat
  ) {
    have(thesis) by Typecheck.prove
  }

  val nestedRecTyping = Theorem(
    (idNat :: (nat ->: nat), addOne :: (nat ->: nat), n :: nat) |- succ * (addOne * (idNat * n)) :: nat
  ) {
    have(thesis) by Typecheck.prove
  }

  val flipOnTrueTyping = Theorem((flip :: (bool ->: bool)) |- flip * tru :: bool) {
    have(thesis) by Typecheck.prove
  }

  val flipOnFalseTyping = Theorem((flip :: (bool ->: bool)) |- flip * fals :: bool) {
    have(thesis) by Typecheck.prove
  }

  val nestedBoolTyping = Theorem(
    (flip :: (bool ->: bool), b :: bool) |- flip * (flip * b) :: bool
  ) {
    have(thesis) by Typecheck.prove
  }
}
