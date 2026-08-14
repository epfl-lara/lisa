package lisa.automation.superposition

import org.scalatest.funsuite.AnyFunSuite

import Core.*

/**
 * What the signature's intern key must and must not distinguish.
 *
 * Interning is the boundary where kernel symbols become the prover's integer codes, so anything the key drops
 * is a distinction the prover can no longer make: two source symbols become one, and the engine may resolve
 * across them. It is also the one place cheap enough not to care: it runs once per symbol occurrence during
 * ingestion, never on a search path.
 */
class SignatureTest extends AnyFunSuite:

  test("a name used as both a predicate and a function at the same arity yields two symbols") {
    // The key used to be `(name, arity)`, accepting `isPredicate` and discarding it, so these collapsed into
    // one symbol, and whichever was interned first decided the kind for both. TPTP cannot express this (the
    // positions are distinct there), but `Constant("p", Ind→Prop)` and `Constant("p", Ind→Ind)` are two legal
    // kernel symbols in a Lisa goal.
    val sig = new Signature
    val asPredicate = sig.intern("p", 1, isPredicate = true)
    val asFunction = sig.intern("p", 1, isPredicate = false)
    assert(asPredicate != asFunction, "a predicate and a function sharing name and arity must stay distinct")
    assert(sig.info(asPredicate).isPredicate && !sig.info(asFunction).isPredicate)
  }

  test("the identifier's counter is part of the key: `e` and `e_1` are different symbols") {
    val sig = new Signature
    val e0 = sig.intern("e", 0, 1, isPredicate = false)
    val e1 = sig.intern("e", 1, 1, isPredicate = false)
    assert(e0 != e1, "`e` and `e_1` are different kernel identifiers")
    assert(sig.info(e1).name == "e" && sig.info(e1).no == 1,
      "the identifier is stored in two parts, so consumers rebuild it rather than parsing `e_1` back")
  }

  test("arity is part of the key") {
    val sig = new Signature
    assert(sig.intern("f", 1, isPredicate = false) != sig.intern("f", 2, isPredicate = false))
  }

  test("interning is still memoised: the same symbol always gets the same code") {
    val sig = new Signature
    val a = sig.intern("q", 3, 2, isPredicate = true)
    val b = sig.intern("q", 3, 2, isPredicate = true)
    assert(a == b, "a repeated intern must return the existing code, not mint a new one")
    val before = sig.size
    sig.intern("q", 3, 2, isPredicate = true)
    assert(sig.size == before, "re-interning must not grow the signature")
  }

  test("equality keeps code 0, which the term representation assumes") {
    // `Core.EqualitySymbol` is a constant `0`; the signature reserves it by interning `=` first.
    val sig = new Signature
    assert(sig.intern("=", 2, isPredicate = true) == EqualitySymbol)
  }
