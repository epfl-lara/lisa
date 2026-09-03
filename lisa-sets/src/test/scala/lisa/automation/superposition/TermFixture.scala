package lisa.automation.superposition

import lisa.automation.superposition.index._
import lisa.automation.superposition.ordering._

import Core._

/**
 * The shared term-building fixture for the prover tests.
 *
 * Fourteen test classes each carried a near-identical private `class Fix`: a fresh signature, term bank and
 * trail plus the same dozen builders. Beyond the duplication, the copies had drifted in small ways that cost
 * a reader real time: `clause` was `cl` in one file, `order` was `ord` in another, so telling whether two
 * fixtures meant the same thing needed a diff. One base fixes both.
 *
 * Each test extends it and adds only what is genuinely its own (a `DiscriminationTree`, a `subsumes`
 * shorthand, a non-default selector). A fresh instance per test keeps them independent: the signature,
 * bank and trail are all mutable, and symbol codes and clause ids depend on interning order.
 *
 * `weightOf` maps a symbol's arity to its KBO weight, defaulting to the shipped scheme (every symbol weighs 1).
 * A test needing weights the production schemes do not produce -- a weight-zero symbol, say -- passes its own,
 * since weights are fixed when a symbol is interned and cannot be changed afterwards.
 *
 * Literal selection is the bank's default, which is the refutation-complete one the prover ships
 * ([[Core.TermBank.selector]]); a test wanting one of the incomplete strategies assigns it explicitly. It is
 * worth stating because a saturated verdict means something quite different under the two: under this one it is
 * a genuine decision, under a one-literal selection it may only mean the selection could not reach the proof.
 */
class TermFixture(weightOf: Int => Int = WeightScheme.Const.weightOf):
  val sig: Signature = new Signature(weightOf)
  val bank: TermBank = new TermBank(sig)
  val trail: Trail = new Trail(bank)

  /**
   * The bank's shared KBO-based ordering. Safe to force here: the only thing that changes the ordering after
   * terms exist is `Precedence.assign`, which clears the orientation memo as its last act.
   */
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
