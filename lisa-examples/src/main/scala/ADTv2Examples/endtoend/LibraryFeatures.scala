package ADTv2Examples.endtoend

import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Types.ADTv2.library.*

/**
 * Coverage example: touches every predefined library ADT and every library
 * function, showing the core generated theorems for each.
 *
 * Conventions on type arguments:
 *   - monomorphic ADTs (Nat, Bool, Unit, Void) take no type argument;
 *   - 1-parameter ADTs (List, Option, Box) take one;
 *   - 2-parameter ADTs (Union, Product) take two.
 */
object LibraryFeatures extends lisa.Main {

  // ════════════════════════════ ADTs ════════════════════════════

  section("Nat")
  show(nat.induction)
  show(nat.elim)
  show(nat.disjointness(zero, succ))
  show(zero.intro)
  show(succ.intro)

  section("Bool")
  show(bool.induction)
  show(bool.elim)
  show(bool.disjointness(tru, fals))
  show(tru.intro)
  show(fals.intro)

  section("Unit")
  show(unit.induction)
  show(unit.elim)
  show(star.intro)

  section("Void")
  show(void.induction)
  show(void.elim)

  section("List")
  show(list.induction(nat))
  show(list.elim(nat))
  show(list.disjointness(nil, cons, nat))
  show(nil.intro(nat))
  show(cons.intro(nat))

  section("Option")
  show(option.induction(nat))
  show(option.elim(nat))
  show(option.disjointness(some, none, nat))
  show(some.intro(nat))
  show(none.intro(nat))

  section("Box")
  show(box.induction(unit))
  show(box.elim(unit))
  show(pack.intro(unit))

  section("Union")
  show(union.induction(nat, bool))
  show(union.elim(nat, bool))
  show(union.disjointness(inl, inr, nat, bool))
  show(inl.intro(nat, bool))
  show(inr.intro(nat, bool))

  section("Product")
  show(product.induction(nat, bool))
  show(product.elim(nat, bool))
  show(pair.intro(nat, bool))
  show(pair.introApp(nat, bool))

  // ════════════════════════════ Functions ════════════════════════════

  section("not : Bool -> Bool")
  show(not.intro)
  show(not.elim(tru))
  show(not.elim(fals))

  section("pred : Nat -> Nat")
  show(pred.intro)
  show(pred.elim(zero))
  show(pred.elim(succ))

  section("double : Nat -> Nat")
  show(double.intro)
  show(double.elim(zero))
  show(double.elim(succ))

  section("add : Nat -> (Nat -> Nat)")
  show(add.intro)
  show(add.introApp)
  show(add.elim(zero))
  show(add.elim(succ))

  section("length : List[A] -> Nat")
  show(length.intro(nat))
  show(length.elim(nat)(nil))
  show(length.elim(nat)(cons))

  section("isLeft : Union[A,B] -> Bool")
  show(isLeft.intro(nat, bool))
  show(isLeft.elim(nat, bool)(inl))
  show(isLeft.elim(nat, bool)(inr))
  show(isLeft.elimTotal(nat, bool))
}
