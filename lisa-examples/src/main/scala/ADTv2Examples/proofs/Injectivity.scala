package ADTv2Examples.proofs

import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Types.ADTv2.library.*

/**
 * Injectivity comes in two flavours, and this example exercises both.
 *
 *   - Same-constructor (argument-wise) injectivity: a constructor applied to
 *     two argument tuples is equal iff the arguments are equal, e.g.
 *     `succ(a) = succ(b) <=> a = b`.  Exposed as `constructor.injectivity`.
 *
 *   - Cross-constructor disjointness: two *different* constructors of the same
 *     ADT never produce the same value, e.g. `zero != succ(k)`.  Exposed as
 *     `adt.injectivity(c1, c2)`.
 */
object Injectivity extends lisa.Main {

  // ── Same-constructor, argument-wise injectivity ─────────────────────────
  section("Argument-wise injectivity (single constructor)")
  show(succ.injectivity) // Nat:    succ(k) = succ(k2) <=> k = k2
  show(cons.injectivity(nat)) // List:   cons(h,t) = cons(h2,t2) <=> h=h2 /\ t=t2
  show(some.injectivity(nat)) // Option: some(x) = some(x2) <=> x = x2
  show(inl.injectivity(nat, bool)) // Union:  inl(x) = inl(x2) <=> x = x2
  show(pair.injectivity(nat, bool)) // Product:pair(x,y) = pair(x2,y2) <=> x=x2 /\ y=y2

  // ── Cross-constructor disjointness ──────────────────────────────────────
  section("Cross-constructor disjointness (distinct constructors)")
  show(nat.disjointness(zero, succ)) // zero != succ(k)
  show(bool.disjointness(tru, fals)) // tru  != fals
  show(option.disjointness(some, none, nat)) // some(x) != none
  show(union.disjointness(inl, inr, nat, bool)) // inl(x) != inr(y)
}
