package lisa.kernel

import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SCProofChecker
import lisa.kernel.proof.SCProofCheckerJudgement
import org.scalatest.Assertions

/**
 * Assertions on a kernel judgement, for any test that produces an [[SCProof]].
 *
 * `SCProofChecker.checkSCProof` returns `SCValidProof(_, usesSorry)`, and `isValid` is `true` for **both**
 * values of that flag: a `Sorry` step is accepted by the checker and merely reported. So the natural
 * `assert(checkSCProof(p).isValid)` is satisfied by `SCProof(IndexedSeq(Sorry(bot)))` — a proof of anything at
 * all, establishing nothing. Any test that builds a proof in order to show something *was proved* needs the
 * stronger check, and the weaker one reads identically at the call site.
 *
 * Hence two named assertions rather than one predicate, so a test states which contract it is checking instead
 * of leaving it to be inferred from how the proof was obtained. Both take a `what` label that is prefixed to
 * the failure message.
 */
object KernelProof:

  /**
   * The proof is accepted by the kernel. `Sorry` is permitted, so this asserts only that the proof is
   * *well-formed* — every step follows from its premises. Use it when a `Sorry` is deliberate, e.g. when a
   * sub-derivation is stubbed out to test the surrounding construction on its own.
   */
  def assertCorrectProof(p: SCProof, what: String): Unit =
    SCProofChecker.checkSCProof(p) match
      case SCProofCheckerJudgement.SCValidProof(_, _) => ()
      case j => Assertions.fail(s"$what: kernel rejected the proof: $j")

  /**
   * The proof is accepted by the kernel **and** free of `Sorry` — i.e. it genuinely establishes its
   * conclusion. This is the check to use whenever the proof is the result under test.
   */
  def assertCorrectProofNoSorry(p: SCProof, what: String): Unit =
    SCProofChecker.checkSCProof(p) match
      case SCProofCheckerJudgement.SCValidProof(_, false) => ()
      case SCProofCheckerJudgement.SCValidProof(_, true) =>
        Assertions.fail(s"$what: the kernel accepted the proof, but it uses `Sorry` — it proves nothing")
      case j => Assertions.fail(s"$what: kernel rejected the proof: $j")
