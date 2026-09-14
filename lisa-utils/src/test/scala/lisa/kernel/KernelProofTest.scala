package lisa.kernel

import lisa.kernel.fol.FOL._
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SCProofChecker
import lisa.kernel.proof.SequentCalculus._
import org.scalatest.exceptions.TestFailedException
import org.scalatest.funsuite.AnyFunSuite

/**
 * Checks that the [[KernelProof]] helpers can fail, in particular on a `Sorry` proof the checker accepts.
 */
class KernelProofTest extends AnyFunSuite:

  private val emptySequent = Sequent(Set.empty, Set.empty)
  private val a = Variable(Identifier("a"), Prop)

  /**
   * `⊢` by a single `Sorry`: valid for the checker, but `usesSorry`.
   */
  private val fabricated = SCProof(IndexedSeq(Sorry(emptySequent)), IndexedSeq.empty)

  /**
   * `a ⊢ a` by `Hypothesis`.
   */
  private val genuine = SCProof(IndexedSeq(Hypothesis(Sequent(Set(a), Set(a)), a)), IndexedSeq.empty)

  /**
   * `Hypothesis` whose conclusion lacks the hypothesis.
   */
  private val bogus = SCProof(IndexedSeq(Hypothesis(emptySequent, a)), IndexedSeq.empty)

  test("the kernel accepts a Sorry proof, so `isValid` alone cannot be the oracle") {
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
