package ADTv2Examples.functions

import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Types.ADTv2.API.`*`
import lisa.maths.SetTheory.Types.ADTv2.library.Bool.*
import lisa.maths.SetTheory.Types.ADTv2.library.List.*
import lisa.maths.SetTheory.Types.ADTv2.library.Nat.*
import lisa.maths.SetTheory.Types.ADTv2.library.*

/**
 * Examples of recursive functions defined with nested pattern matching.
 *
 * Nested patterns let a single Case branch test a constructor argument against
 * a concrete term rather than binding it to a fresh variable.  Two or more
 * branches for the same constructor with complementary conditions cover all
 * cases of that constructor.
 */
object NestedPatterns extends lisa.Main {

  private val k = variable[Ind]
  private val hd = variable[Ind]
  private val tl = variable[Ind]
  private val boolList = list.specialize(bool)

  // ── List[Bool] examples ────────────────────────────────────────────────
  section("countTrue on List[Bool]")

  // Count occurrences of `tru` in a list of booleans.
  // The cons constructor is split into two nested branches:
  //   • cons(tru, tl)  — head is true  → increment the count
  //   • cons(fals, tl) — head is false → skip
  lazy val countTrue = recFun(boolList, nat) { self =>
    Case(nil):
      zero
    Case(cons, tru, tl):
      succ * (self * tl)
    Case(cons, fals, tl):
      self * tl
  }
  // show(countTrue.intro(bool))
  // show(countTrue.elim(bool)(nil))
  // show(countTrue.elim(bool)(cons))
  // show(countTrue.elimTotal(bool))


  // Check whether any element of a list of booleans is `tru`.
  lazy val existsTrue = recFun(boolList, bool) { self =>
    Case(nil):
      fals
    Case(cons, tru, tl):
      tru
    Case(cons, fals, tl):
      self * tl
  }
  section("existsTrue on List[Bool]")
  // show(existsTrue.intro(bool))
  // show(existsTrue.elim(bool)(nil))
  // show(existsTrue.elim(bool)(cons))
  // show(existsTrue.elim(bool)(Case(cons, tru, tl)))
  // show(existsTrue.elim(bool)(Case(cons, fals, tl)))
  // show(existsTrue.elimTotal(bool))


  // ── List[Nat] examples ─────────────────────────────────────────────────

  // Test whether the head of a list of natural numbers is `zero`.
  // The catch-all branch `cons(hd, tl)` binds the head to a fresh variable,
  // covering every head value that is not `zero`.
  // val headIsZero = recFun(list, bool) { self =>
  //   Case(nil):
  //     fals
  //   Case(cons, zero, tl):
  //     tru
  //   Case(cons, hd, tl):
  //     fals
  // }
  // show(headIsZero.intro(nat))
  // show(headIsZero.elim(nat)(nil))
  // show(headIsZero.elim(nat)(cons))
  
  
  
  
  // section("headIsZero on List[Nat]")
  // val isOptionZero = fun(Option.option.specialize(nat), bool) {
  //   Case(Option.none):
  //     fals
  //   Case(Option.some, zero):
  //     tru
  //   Case(Option.some, k):
  //   // Case(Option.some, succ * k):
  //     fals
  // }
  

  // ── Multi-level nested patterns on Nat examples ────────────────────────────────────────────────
  section("multi-level nested patterns on Nat (fun)")

  // val isGreaterThanOne = fun(nat, bool) {
  //   Case(zero):
  //     fals
  //   Case(succ, zero):
  //     fals
  //   Case(succ, succ * k):
  //     tru
  // }
  // show(isGreaterThanOne.intro)
  // show(isGreaterThanOne.elimTotal)

  // val isGreaterThanTwo = fun(nat, bool) {
  //   Case(zero):
  //     fals
  //   Case(succ, zero):
  //     fals
  //   Case(succ, succ * zero):
  //     fals
  //   Case(succ, succ * (succ * k)):
  //     tru
  // }
  // show(isGreaterThanTwo.intro)
  // show(isGreaterThanTwo.elimTotal)

  // val isMultipleOfThree = recFun(nat, bool) { self =>
  //   Case(zero):
  //     tru
  //   Case(succ, zero):
  //     fals
  //   Case(succ, succ * zero):
  //     fals
  //   Case(succ, succ * (succ * k)):
  //     self * k
  // }
  // show(isMultipleOfThree.intro)
  // show(isMultipleOfThree.elimTotal)


  // ── Example of a more complex function with nested patterns ────────────────────────────────────────────────
  section("hasDuplicate on List[Bool]")

  val hasDuplicate = recFun(boolList, bool) { self =>
    Case(nil):
      fals
    Case(cons, tru, nil(bool)):
      fals
    Case(cons, fals, nil(bool)):
      fals
    Case(cons, tru, cons(bool) * tru * tl):
      tru
    Case(cons, fals, cons(bool) * fals * tl):
      tru
    Case(cons, tru, cons(bool) * fals * tl):
      self * tl
    Case(cons, fals, cons(bool) * tru * tl):
      self * tl
  }

  
  show(hasDuplicate.intro(bool))
  show(hasDuplicate.elim(bool)(nil))
  show(hasDuplicate.elim(bool)(Case(cons, tru, cons(bool) * tru * tl)))
  

  Time.printSummary()

}
