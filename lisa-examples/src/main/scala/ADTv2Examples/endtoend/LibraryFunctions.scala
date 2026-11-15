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
  show(length.intro)
  show(length.elim(nil))
  show(length.elim(cons))

  section("size : Tree[A] -> Nat")
  show(size.intro)
  show(size.elim(leaf))
  show(size.elim(node))

  section("leafCount : Tree[A] -> Nat")
  show(leafCount.intro)
  show(leafCount.elim(leaf))
  show(leafCount.elim(node))

  section("mirror : Tree[A] -> Tree[A]")
  show(mirror.intro)
  show(mirror.elim(leaf))
  show(mirror.elim(node))

  section("isEmpty : Tree[A] -> Bool")
  show(isEmpty.intro)
  show(isEmpty.elim(leaf))
  show(isEmpty.elim(node))

  section("isLeft : Union[A,B] -> Bool")
  show(isLeft.intro)
  show(isLeft.elim(inl))
  show(isLeft.elim(inr))
  show(isLeft.elimTotal)
}
