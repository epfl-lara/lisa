package lisa.kernel

import lisa.kernel.fol.FOL._
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SCProofChecker
import lisa.kernel.proof.SequentCalculus._
import org.scalatest.exceptions.TestFailedException
import org.scalatest.funsuite.AnyFunSuite

/**
 * Anti-vacuity guard for [[KernelProof]].
 *
 * Callers route their proof assertions through these helpers and then pass, which is only informative if the
 * helpers can fail. `assertCorrectProofNoSorry` exists precisely to catch what `isValid` cannot, so the
 * fabricated proof it must reject is pinned here rather than assumed.
 */
class KernelProofTest extends AnyFunSuite:

  private val emptySequent = Sequent(Set.empty, Set.empty)
  private val a = Variable(Identifier("a"), Prop)

  /**
   * `⊢` "proved" by a single `Sorry` — accepted by the checker, flagged as `usesSorry`.
   */
  private val fabricated = SCProof(IndexedSeq(Sorry(emptySequent)), IndexedSeq.empty)

  /**
   * `a ⊢ a` by `Hypothesis` — a genuine one-step proof.
   */
  private val genuine = SCProof(IndexedSeq(Hypothesis(Sequent(Set(a), Set(a)), a)), IndexedSeq.empty)

  /**
   * `Hypothesis` whose conclusion does not contain the hypothesised formula.
   */
  private val bogus = SCProof(IndexedSeq(Hypothesis(emptySequent, a)), IndexedSeq.empty)

  test("the kernel accepts a Sorry proof, so `isValid` alone cannot be the oracle") {
    // The fact that makes `assert(checkSCProof(p).isValid)` satisfiable by a proof of nothing.
    assert(SCProofChecker.checkSCProof(fabricated).isValid)
  }

  test("assertCorrectProofNoSorry rejects a Sorry proof") {
    val e = intercept[TestFailedException](KernelProof.assertCorrectProofNoSorry(fabricated, "fabricated"))
    assert(e.getMessage.contains("Sorry"), s"the failure should name the cause, got: ${e.getMessage}")
  }

  test("assertCorrectProofNoSorry accepts a genuine proof") {
    KernelProof.assertCorrectProofNoSorry(genuine, "genuine")
  }

  test("assertCorrectProofNoSorry rejects a proof the kernel rejects") {
    intercept[TestFailedException](KernelProof.assertCorrectProofNoSorry(bogus, "bogus"))
  }

  test("assertCorrectProof tolerates Sorry but still rejects an invalid proof") {
    KernelProof.assertCorrectProof(fabricated, "stubbed")
    intercept[TestFailedException](KernelProof.assertCorrectProof(bogus, "bogus"))
  }
