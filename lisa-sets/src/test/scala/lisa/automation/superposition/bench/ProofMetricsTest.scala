package lisa.automation.superposition
package bench

import org.scalatest.funsuite.AnyFunSuite

import lisa.utils.K.*

/** Tests for [[ProofMetrics]]: how the two sizes relate, and that both descend into subproofs. */
class ProofMetricsTest extends AnyFunSuite:

  private val a = Variable(Identifier("a"), Prop)
  private val b = Variable(Identifier("b"), Prop)
  private val x = Variable(Identifier("x"), Ind)
  private val p = Variable(Identifier("p"), Ind >>: Prop)

  /** `p(x)`, an expression of three nodes: the application, `p`, and `x`. */
  private val px: Expression = p(x)

  test("a one step proof: sizes are the node counts of its conclusion") {
    // Both sides hold the same object.
    val proof = SCProof(IndexedSeq(Hypothesis(a |- a, a)), IndexedSeq.empty)
    val m = ProofMetrics.of(proof)
    assert(m.steps == 1)
    assert(m.rawSize == 2, "one node on each side")
    assert(m.sharedSize == 1, "the same object on both sides is one distinct subexpression")
    assert(m.maxSequent == 2)
    assert(m.imports == 0)
  }

  test("shared never exceeds raw, and they agree when nothing repeats") {
    val proof = SCProof(IndexedSeq(Weakening(a |- b, -1)), IndexedSeq(a |- b))
    val m = ProofMetrics.of(proof)
    assert(m.rawSize == m.sharedSize, s"no repetition, so the counts should agree: $m")
    assert(m.sharedSize <= m.rawSize)
  }

  test("a repeated compound subformula is counted once by shared and twice by raw") {
    // Hash-consing makes both occurrences one object.
    val both = SCProof(IndexedSeq(Hypothesis(px |- px, px)), IndexedSeq.empty)
    val m = ProofMetrics.of(both)
    assert(m.rawSize == 6, "three nodes on each side")
    assert(m.sharedSize == 3, "one application, one p, one x")
  }

  test("imports are excluded from the sizes and reported as a count") {
    val withImport = SCProof(IndexedSeq(Weakening(a |- a, -1)), IndexedSeq(px |- px))
    val m = ProofMetrics.of(withImport)
    assert(m.imports == 1)
    assert(m.rawSize == 2, "the import's six nodes are not counted, only the step's two")
  }

  test("subproofs are descended into, for steps and for both sizes") {
    val inner = SCProof(IndexedSeq(Hypothesis(px |- px, px)), IndexedSeq.empty)
    val outer = SCProof(IndexedSeq(SCSubproof(inner, IndexedSeq.empty)), IndexedSeq.empty)
    val flat = ProofMetrics.of(inner)
    val nested = ProofMetrics.of(outer)
    assert(nested.steps == flat.steps + 1, "a subproof counts as its body plus one, as `totalLength` does")
    // The subproof's conclusion repeats the inner one.
    assert(nested.rawSize == flat.rawSize * 2)
    assert(nested.sharedSize == flat.sharedSize, "the repeat is the same object, so shared is unchanged")
  }

  test("steps agrees with the kernel's own count") {
    val inner = SCProof(IndexedSeq(Hypothesis(a |- a, a)), IndexedSeq.empty)
    val outer = SCProof(IndexedSeq(Hypothesis(b |- b, b), SCSubproof(inner, IndexedSeq.empty)), IndexedSeq.empty)
    assert(ProofMetrics.of(outer).steps == outer.totalLength)
  }
