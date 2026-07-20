package lisa.automation.superposition

import org.scalatest.funsuite.AnyFunSuite

import lisa.utils.K.{_, given}
import lisa.automation.clausification.Clausification

/**
 * SInE axiom-selection tests: reachability through the trigger relation, the depth/tolerance/size guards, and
 * the no-conjecture pass-through. Axioms are symbol co-occurrences (`a ∨ b`, …) so the selection is easy to trace.
 */
class SineTest extends AnyFunSuite:

  private def p(n: String): Expression = Constant(Identifier(n, 0), Prop)
  private val (a, b, c, x, y, z) = (p("a"), p("b"), p("c"), p("x"), p("y"), p("z"))
  //  ax0: a∨b   ax1: b∨c   ax2: x∨y   ax3: y∨z   ax4: ⊤ (symbol-less).  Conjecture: c.
  private val hyps: IndexedSeq[Expression] = IndexedSeq(or(a)(b), or(b)(c), or(x)(y), or(y)(z), top)

  test("SInE keeps the goal-reachable axioms and drops the disjoint ones") {
    // tolerance 2.0 lets the frequent symbol `b` (in `a∨b`) also trigger it, so reaching `b` pulls the whole chain.
    val keep = Sine.selectIndices(hyps, c, SineConfig(tolerance = 2.0, depth = 0, minAxioms = 0))
    assert(keep.contains(0) && keep.contains(1), s"kept the a-b-c chain, got $keep")
    assert(!keep.contains(2) && !keep.contains(3), s"dropped the disjoint x-y-z chain, got $keep")
    assert(keep.contains(4), "always keeps a symbol-less axiom")
  }

  test("SInE depth bounds the reach") {
    // depth 1: one BFS round from `c` reaches only the directly-triggered `b∨c`, not `a∨b` behind it.
    val keep = Sine.selectIndices(hyps, c, SineConfig(tolerance = 2.0, depth = 1, minAxioms = 0))
    assert(keep.contains(1) && !keep.contains(0), s"depth 1 keeps only the directly-triggered axiom, got $keep")
  }

  test("SInE keeps everything below minAxioms, and is a no-op without a conjecture") {
    assert(Sine.selectIndices(hyps, c, SineConfig(minAxioms = 100)) == hyps.indices.toSet, "too few axioms ⇒ keep all")
    val problem = Clausification.Problem(hyps.map(h => Sequent(Set.empty, Set(h))), None)
    assert(Sine.select(problem, SineConfig(minAxioms = 0)) == problem, "no conjecture ⇒ unchanged")
  }
