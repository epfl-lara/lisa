package lisa.automation.superposition

import org.scalatest.funsuite.AnyFunSuite

import lisa.utils.K.{_, given}

/**
 * SInE activation-gate tests ([[Sine.shouldFilter]]): the filter fires only when the problem is both large
 * enough (gate 1) and genuinely prunable (gate 2). Axioms are symbol co-occurrences (`a ∨ b`) so the trigger
 * relation is easy to trace.
 */
class SinePolicyTest extends AnyFunSuite:

  private def p(n: String): Expression = Constant(Identifier(n, 0), Prop)

  /** `n` disjoint noise axioms plus a 2-axiom chain reaching the conjecture symbol `goal` (so almost everything
   *  is irrelevant). Returns `(hypotheses, conjecture)`. */
  private def sparse(n: Int): (IndexedSeq[Expression], Expression) =
    val goal = p("goal")
    val chain = IndexedSeq(or(goal)(p("g1")), or(p("g1"))(p("g2")))     // 2 reachable from the goal
    val noise = (0 until n).map(i => or(p(s"n${i}a"))(p(s"n${i}b")))    // n pairwise-disjoint, unreachable
    (chain ++ noise, goal)

  test("gate 1: below the axiom floor ⇒ do not filter (even if very prunable)") {
    val (h, c) = sparse(200) // 202 axioms < default floor 400
    assert(!Sine.shouldFilter(h, c))
  }

  test("gate 1: a conjecture with no symbol to seed from ⇒ do not filter") {
    val (h, _) = sparse(500)
    assert(!Sine.shouldFilter(h, top))
  }

  test("gate 2: large + mostly-irrelevant ⇒ filter") {
    val (h, c) = sparse(500) // 502 axioms, only 2 reachable ⇒ keep-ratio ≈ 0.004
    assert(Sine.shouldFilter(h, c))
  }

  test("gate 2: large but fully connected (goal reaches everything) ⇒ do not filter") {
    // A path goal-s0-s1-…-s499: the BFS from `goal` reaches every axiom, so the probe keeps them all.
    val syms = p("goal") +: (0 until 500).map(i => p(s"s$i"))
    val h = (0 until 500).map(i => or(syms(i))(syms(i + 1)))
    assert(!Sine.shouldFilter(h, p("goal")))
  }
