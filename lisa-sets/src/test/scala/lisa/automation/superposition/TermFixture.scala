package lisa.automation.superposition

import Core.*

/**
 * The shared term-building fixture for the prover tests.
 *
 * Fourteen test classes each carried a near-identical private `class Fix` — a fresh signature, term bank and
 * trail plus the same dozen builders. Beyond the duplication, the copies had drifted in small ways that cost
 * a reader real time: `clause` was `cl` in one file, `order` was `ord` in another, so telling whether two
 * fixtures meant the same thing needed a diff. One base fixes both.
 *
 * Each test extends it and adds only what is genuinely its own (a `DiscriminationTree`, a `subsumes`
 * shorthand, a non-default selector). A fresh instance per test keeps them independent: the signature,
 * bank and trail are all mutable, and symbol codes and clause ids depend on interning order.
 */
class TermFixture:
  val sig: Signature = new Signature
  val bank: TermBank = new TermBank(sig)
  val trail: Trail = new Trail(bank)

  /** The bank's shared KBO-based ordering. Safe to force here: `Order` stamps its orientation memo with the
    * signature's `orderingVersion`, so a later `Precedence.assign` invalidates it rather than being ignored. */
  val order: Order = bank.order
  val kbo: KBO = order.kbo

  def pred(name: String, arity: Int): Symbol = sig.intern(name, arity, isPredicate = true)
  def fn(name: String, arity: Int): Symbol = sig.intern(name, arity, isPredicate = false)
  def const(name: String): Term = bank.mkConst(fn(name, 0))
  def prop(name: String): Term = bank.mkConst(pred(name, 0)) // a 0-ary (propositional) atom
  def app(f: Symbol, args: Term*): Term = bank.mkApp(f, args.toArray)
  def v(n: Int): Term = bank.mkVar(Core.Variable(n))
  def mkEq(s: Term, t: Term): Term = bank.mkApp(EqualitySymbol, Array(s, t)) // the equality atom `s = t`
  def pos(atom: Term): Literal = bank.mkLiteral(atom, true)
  def neg(atom: Term): Literal = bank.mkLiteral(atom, false)
  def lit(atom: Term, positive: Boolean): Literal = bank.mkLiteral(atom, positive)
  def clause(lits: Literal*): Clause = bank.mkClause(lits.toArray)
