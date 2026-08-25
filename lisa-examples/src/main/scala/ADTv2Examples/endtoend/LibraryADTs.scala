package ADTv2Examples.endtoend

import lisa.maths.SetTheory.Types.ADTv2.library.*

/**
 * Coverage example for predefined library ADTs and constructor theorems.
 *
 * Conventions on type arguments:
 *   - monomorphic ADTs (Nat, Bool, Unit, Void) take no type argument;
 *   - 1-parameter ADTs (List, Tree, Option, Box) take one;
 *   - 2-parameter ADTs (Union, Product) take two.
 */
object LibraryADTs extends lisa.Main {

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
  show(list.induction)
  show(list.elim)
  show(list.disjointness(nil, cons))
  show(nil.intro)
  show(cons.intro)

  section("Tree")
  show(tree.induction)
  show(tree.elim)
  show(tree.disjointness(leaf, node))
  show(leaf.intro)
  show(node.intro)

  section("Option")
  show(option.induction)
  show(option.elim)
  show(option.disjointness(some, none))
  show(some.intro)
  show(none.intro)

  section("Box")
  show(box.induction)
  show(box.elim)
  show(pack.intro)

  section("Union")
  show(union.induction)
  show(union.elim)
  show(union.disjointness(inl, inr))
  show(inl.intro)
  show(inr.intro)

  section("Product")
  show(product.induction)
  show(product.elim)
  show(pair.intro)
  show(pair.introApp)
}
