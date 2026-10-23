package ADTv2Examples.endtoend

import lisa.maths.SetTheory.Types.ADTv2.library.*

/**
 * Coverage example for predefined library functions.
 */
object LibraryFunctions extends lisa.Main {

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

  section("size : Tree[A] -> Nat")
  show(size.intro(nat))
  show(size.elim(nat)(leaf))
  show(size.elim(nat)(node))

  section("leafCount : Tree[A] -> Nat")
  show(leafCount.intro(nat))
  show(leafCount.elim(nat)(leaf))
  show(leafCount.elim(nat)(node))

  section("mirror : Tree[A] -> Tree[A]")
  show(mirror.intro(nat))
  show(mirror.elim(nat)(leaf))
  show(mirror.elim(nat)(node))

  section("isEmpty : Tree[A] -> Bool")
  show(isEmpty.intro(nat))
  show(isEmpty.elim(nat)(leaf))
  show(isEmpty.elim(nat)(node))

  section("isLeft : Union[A,B] -> Bool")
  show(isLeft.intro(nat, bool))
  show(isLeft.elim(nat, bool)(inl))
  show(isLeft.elim(nat, bool)(inr))
  show(isLeft.elimTotal(nat, bool))
}
