package lisa.automation.superposition

import lisa.automation.Problem
import lisa.utils.K.{_, given}
import org.scalatest.funsuite.AnyFunSuite

/**
 * SInE axiom-selection tests: reachability through the trigger relation, the depth/tolerance/size guards, and
 * the no-conjecture pass-through. Axioms are symbol co-occurrences (`a ∨ b`, …) so the selection is easy to trace.
 */
class SineTest extends AnyFunSuite:

  private def p(n: String): Expression = Constant(Identifier(n, 0), Prop)
  private val (a, b, c, x, y, z) = (p("a"), p("b"), p("c"), p("x"), p("y"), p("z"))
  //  ax0: a∨b   ax1: b∨c   ax2: x∨y   ax3: y∨z   ax4: ⊤ (symbol-less).  Conjecture: c.
  private val hyps: IndexedSeq[Sequent] = IndexedSeq(or(a)(b), or(b)(c), or(x)(y), or(y)(z), top).map(h => () |- h)
  private val goal: Sequent = () |- c

  private def keptFor(cfg: SineConfig): Set[Int] = Sine.analyse(hyps, goal).select(cfg)

  test("SInE keeps the goal-reachable axioms and drops the disjoint ones") {
    // tolerance 2.0 lets the frequent symbol `b` (in `a∨b`) also trigger it, so reaching `b` pulls the whole chain.
    val keep = keptFor(SineConfig(tolerance = 2.0, depth = 0, minAxioms = 0))
    assert(keep.contains(0) && keep.contains(1), s"kept the a-b-c chain, got $keep")
    assert(!keep.contains(2) && !keep.contains(3), s"dropped the disjoint x-y-z chain, got $keep")
    assert(keep.contains(4), "always keeps a symbol-less axiom")
  }

  test("SInE depth bounds the reach") {
    // depth 1: one BFS round from `c` reaches only the directly-triggered `b∨c`, not `a∨b` behind it.
    val keep = keptFor(SineConfig(tolerance = 2.0, depth = 1, minAxioms = 0))
    assert(keep.contains(1) && !keep.contains(0), s"depth 1 keeps only the directly-triggered axiom, got $keep")
  }

  test("SInE keeps everything below minAxioms, and is a no-op without a conjecture") {
    assert(keptFor(SineConfig(minAxioms = 100)) == hyps.indices.toSet, "too few axioms ⇒ keep all")
    assert(Sine.selection(Problem(hyps, None), SineConfig(minAxioms = 0)).isEmpty, "no conjecture ⇒ no filtering")
  }

  test("selection gates and prunes in one pass, which is the path the prover takes") {
    val goalSym = p("goal")
    val chain = IndexedSeq(or(goalSym)(p("g1")), or(p("g1"))(p("g2"))) // reachable from the conjecture
    val noise = (0 until 500).map(i => or(p(s"n${i}a"))(p(s"n${i}b"))) // pairwise disjoint, unreachable
    val problem = Problem((chain ++ noise).map(h => () |- h), Some(() |- goalSym))
    assert(Sine.selection(problem, SineConfig(tolerance = 2.0, depth = 0)).contains(Set(0, 1)))
  }

  test("both sides of a multi-literal hypothesis are read, not just one") {
    // `a ⊢ c` is the clause `¬a ∨ c`; seeding from `a` must reach it through the symbol on the left.
    val two: IndexedSeq[Sequent] = IndexedSeq(Sequent(Set(a), Set(c)), () |- or(x)(y))
    val keep = Sine.analyse(two, () |- a).select(SineConfig(tolerance = 2.0, depth = 0, minAxioms = 0))
    assert(keep == Set(0), s"reached the left-hand literal and nothing else, got $keep")
  }
