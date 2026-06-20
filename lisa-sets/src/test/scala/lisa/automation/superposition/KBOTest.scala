package lisa.automation.superposition

import org.scalatest.funsuite.AnyFunSuite

import Core.*

/**
 * Tests for the Knuth-Bendix ordering [[KBO]] on concrete terms.
 *
 * The core is standalone (no Lisa dependency), so terms are built directly through a
 * [[Signature]] + [[TermBank]]. Note that a symbol's KBO weight is folded into a term's cached
 * weight *at construction*, so any custom weights must be set before the terms are built;
 * precedence, by contrast, is read live and may be changed at any time.
 */
class KBOTest extends AnyFunSuite:

  /** A small fixture: a fresh signature/bank/comparator and helpers to build terms. */
  class Fix:
    val sig: Signature = new Signature
    val bank: TermBank = new TermBank(sig)
    val kbo: KBO = new KBO(bank)

    def fn(name: String, arity: Int): Symbol = sig.intern(name, arity, isPredicate = false)
    def const(name: String): Term = bank.mkConst(fn(name, 0))
    def app(f: Symbol, args: Term*): Term = bank.mkApp(f, args.toArray)
    def v(n: Int): Term = bank.mkVar(Core.Variable(n))

  import Cmp.*

  test("a term is equal to itself") {
    val fx = new Fix
    import fx.*
    val a = const("a")
    val f = fn("f", 1)
    assert(kbo.compare(a, a) == Eq)
    assert(kbo.compare(app(f, a), app(f, a)) == Eq)
    assert(kbo.compare(v(0), v(0)) == Eq)
  }

  test("heavier term is greater (weight dominates)") {
    val fx = new Fix
    import fx.*
    val a = const("a")
    val f = fn("f", 1)
    val fa = app(f, a) // weight 2 vs 1
    assert(kbo.compare(fa, a) == Gt)
    assert(kbo.compare(a, fa) == Lt)
  }

  test("a proper ground subterm is strictly smaller") {
    val fx = new Fix
    import fx.*
    val a = const("a")
    val g = fn("g", 1)
    val f = fn("f", 1)
    val t = app(f, app(g, a)) // f(g(a))
    assert(kbo.compare(t, app(g, a)) == Gt)
    assert(kbo.compare(app(g, a), a) == Gt)
  }

  test("f(x) is greater than x (variable occurs)") {
    val fx = new Fix
    import fx.*
    val f = fn("f", 1)
    val x = v(0)
    assert(kbo.compare(app(f, x), x) == Gt)
    assert(kbo.compare(x, app(f, x)) == Lt)
  }

  test("distinct variables are incomparable") {
    val fx = new Fix
    import fx.*
    val f = fn("f", 1)
    assert(kbo.compare(v(0), v(1)) == Inc)
    assert(kbo.compare(app(f, v(0)), app(f, v(1))) == Inc)
  }

  test("variable condition forces incomparability") {
    val fx = new Fix
    import fx.*
    val g = fn("g", 2)
    val x = v(0)
    val y = v(1)
    // g(x,x) vs g(x,y): x occurs more on the left, y more on the right => neither dominates
    assert(kbo.compare(app(g, x, x), app(g, x, y)) == Inc)
  }

  test("equal weight is broken by precedence") {
    val fx = new Fix
    import fx.*
    val a = const("a") // interned first  => lower precedence (default precedence = intern order)
    val b = const("b") // interned second => higher precedence
    assert(kbo.compare(a, b) == Lt)
    assert(kbo.compare(b, a) == Gt)
  }

  test("lexicographic comparison on first differing argument") {
    val fx = new Fix
    import fx.*
    val f = fn("f", 2)
    val a = const("a")
    val b = const("b") // prec(b) > prec(a)
    // f(a,b) vs f(a,a): equal weights, same head, first difference at arg 2 -> b vs a -> Gt
    assert(kbo.compare(app(f, a, b), app(f, a, a)) == Gt)
    assert(kbo.compare(app(f, a, a), app(f, a, b)) == Lt)
  }

  test("weight-zero maximal unary symbol: f(x) > x, and admissibility holds") {
    val fx = new Fix
    import fx.*
    val f = fn("f", 1)
    val a = const("a")
    sig.info(f).weight = 0 // set BEFORE building terms (weights are cached at construction)
    sig.info(f).precedence = 1000 // make f precedence-maximal
    val x = v(0)
    assert(kbo.checkAdmissibility().isEmpty)
    // w(f(x)) = 0 + w(x) = w(x): equal weight, but x is a proper subterm => f(x) > x
    assert(kbo.compare(app(f, x), x) == Gt)
  }

  test("admissibility violations are reported") {
    val fx = new Fix
    import fx.*
    val c = fn("c", 0)
    sig.info(c).weight = 0 // a constant lighter than the variable weight (1)
    assert(kbo.checkAdmissibility().isDefined)

    val fx2 = new Fix
    val g = fx2.fn("g", 1)
    fx2.fn("h", 0) // some other symbol with higher precedence than g
    fx2.sig.info(g).weight = 0 // weight-0 unary that is NOT precedence-maximal
    assert(fx2.kbo.checkAdmissibility().isDefined)
  }

  test("ground terms are totally ordered, and the order is antisymmetric") {
    val fx = new Fix
    import fx.*
    val a = const("a")
    val b = const("b")
    val cc = const("c")
    val f = fn("f", 1)
    val g = fn("g", 2)
    val atoms: Array[Term] = Array(a, b, cc)

    val rng = new scala.util.Random(20260619L)
    def randomGround(depth: Int): Term =
      if depth <= 0 || rng.nextInt(3) == 0 then atoms(rng.nextInt(atoms.length))
      else
        rng.nextInt(2) match
          case 0 => app(f, randomGround(depth - 1))
          case _ => app(g, randomGround(depth - 1), randomGround(depth - 1))

    val terms: Array[Term] = Array.fill(60)(randomGround(4))
    for s <- terms; t <- terms do
      val st = kbo.compare(s, t)
      assert(st != Inc, "ground terms must be comparable")
      val ts = kbo.compare(t, s)
      st match
        case Gt => assert(ts == Lt)
        case Lt => assert(ts == Gt)
        case Eq => assert(ts == Eq)
        case Inc => fail("unreachable")
  }

  test("ground KBO is transitive on a random sample") {
    val fx = new Fix
    import fx.*
    val a = const("a")
    val b = const("b")
    val f = fn("f", 1)
    val g = fn("g", 2)
    val atoms: Array[Term] = Array(a, b)

    val rng = new scala.util.Random(42L)
    def randomGround(depth: Int): Term =
      if depth <= 0 || rng.nextInt(3) == 0 then atoms(rng.nextInt(atoms.length))
      else if rng.nextInt(2) == 0 then app(f, randomGround(depth - 1))
      else app(g, randomGround(depth - 1), randomGround(depth - 1))

    val terms: Array[Term] = Array.fill(25)(randomGround(4))
    for s <- terms; t <- terms; u <- terms do
      if kbo.compare(s, t) == Gt && kbo.compare(t, u) == Gt then
        assert(kbo.compare(s, u) == Gt, "Gt must be transitive")
  }
