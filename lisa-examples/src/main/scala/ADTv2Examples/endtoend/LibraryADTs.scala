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
  show(list.induction(nat))
  show(list.elim(nat))
  show(list.disjointness(nil, cons, nat))
  show(nil.intro(nat))
  show(cons.intro(nat))

  section("Tree")
  show(tree.induction(nat))
  show(tree.elim(nat))
  show(tree.disjointness(leaf, node, nat))
  show(leaf.intro(nat))
  show(node.intro(nat))

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
}
