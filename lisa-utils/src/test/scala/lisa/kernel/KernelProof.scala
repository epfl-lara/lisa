package lisa.kernel

import lisa.utils.kernel.ProofCertificate
import org.scalatest.Assertions

/** Assert certificate acceptance, distinguishing checked proofs from deliberate Sorry stubs. */
object KernelProof:
  /** Check every inference, permitting deliberate Sorry steps. */
  def assertCorrectProof(proof: ProofCertificate, what: String): Unit =
    proof.check match
      case Right(_) => ()
      case Left(error) => Assertions.fail(s"$what: kernel rejected the certificate: $error")

  /** Check every inference and reject any dependency on Sorry. */
  def assertCorrectProofNoSorry(proof: ProofCertificate, what: String): Unit =
    proof.check match
      case Right(theorem) if !theorem.usesSorry => ()
      case Right(_) => Assertions.fail(s"$what: the certificate depends on Sorry")
      case Left(error) => Assertions.fail(s"$what: kernel rejected the certificate: $error")
