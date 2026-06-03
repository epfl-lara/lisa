package ADTv2Examples.functions

import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Types.ADTv2.library.Bool.*
import lisa.maths.SetTheory.Types.ADTv2.library.List.*
import lisa.maths.SetTheory.Types.ADTv2.library.Nat.*

/**
 * Examples of recursive functions defined with nested pattern matching.
 *
 * Nested patterns let a single Case branch test a constructor argument against
 * a concrete term rather than binding it to a fresh variable.  Two or more
 * branches for the same constructor with complementary conditions cover all
 * cases of that constructor.
 */
object NestedPatterns extends lisa.Main {

  println("launching NestedPatterns...")

  private val hd = variable[Ind]
  private val tl = variable[Ind]
  private val boolList = list.specialize(bool)

  // ── List[Bool] examples ────────────────────────────────────────────────

  // Count occurrences of `tru` in a list of booleans.
  // The cons constructor is split into two nested branches:
  //   • cons(tru, tl)  — head is true  → increment the count
  //   • cons(fals, tl) — head is false → skip
  val countTrue = recFun(boolList, nat) { self =>
    Case(nil):
      zero
    Case(cons, tru, tl):
      succ * (self * tl)
    Case(cons, fals, tl):
      self * tl
  }


  println("countTrue defined")

  // Check whether all elements of a list of booleans are `tru`.
  // val allTrue = recFun(boolList, bool) { self =>
  //   Case(nil):
  //     tru
  //   Case(cons, tru, tl):
  //     self * tl
  //   Case(cons, fals, tl):
  //     fals
  // }
  

  // println("allTrue defined")

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

  // ── Show theorems ──────────────────────────────────────────────────────

  section("countTrue on List[Bool]")
  show(countTrue.intro(bool))
  show(countTrue.elim(bool)(nil))
  show(countTrue.elim(bool)(cons))

  // section("allTrue on List[Bool]")
  // show(allTrue.intro(bool))
  // show(allTrue.elim(bool)(nil))
  // show(allTrue.elim(bool)(cons))

  // section("headIsZero on List[Nat]")
  // show(headIsZero.intro(nat))
  // show(headIsZero.elim(nat)(nil))
  // show(headIsZero.elim(nat)(cons))

  Time.printSummary()
}
