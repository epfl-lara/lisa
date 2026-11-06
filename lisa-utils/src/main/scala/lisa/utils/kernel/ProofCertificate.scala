package lisa.utils.kernel

import lisa.kernel.proof.Sequent
import lisa.kernel.proof.Theory
import lisa.kernel.proof.Thm

import scala.collection.mutable.ArrayBuffer
import scala.util.control.NonFatal

type CertificateStep = ProofStep | Subproof

/** Embed a certificate by supplying one parent premise for each of its imports. */
final case class Subproof(proof: ProofCertificate, premises: Seq[Int]):
  def statement: Sequent = proof.conclusion

/** Build a nested certificate, then flatten and check it through the linear checker. */
final case class ProofCertificate(steps: IndexedSeq[CertificateStep], imports: IndexedSeq[Sequent] = IndexedSeq.empty):
  def conclusion: Sequent = steps.last match
    case step: ProofStep => step.statement
    case step: Subproof => step.statement

  def withNewSteps(extra: IndexedSeq[CertificateStep]): ProofCertificate = copy(steps = steps ++ extra)

  /** Count certificate nodes, including subproof wrappers and their bodies. */
  def totalLength: Int = steps.foldLeft(0): (size, step) =>
    size + (step match
      case Subproof(inner, _) => 1 + inner.totalLength
      case _: ProofStep => 1)

  /** Flatten subproofs, retaining restatements at nonidentical import boundaries.
   *
   * @throws IllegalArgumentException if a reference or subproof import mapping is malformed.
   */
  def toLinearProof: LinearProof =
    val output = ArrayBuffer.empty[ProofStep]

    def emit(proof: ProofCertificate, imported: Array[Int]): Int =
      require(proof.steps.nonEmpty, "A subproof must contain at least one step")
      val translated = new Array[Int](proof.steps.size)

      def resolve(ref: Int, before: Int): Int =
        if ref >= 0 then
          require(ref < before, s"Forward certificate reference: $ref at $before")
          translated(ref)
        else
          val index = -ref - 1
          require(index < imported.length, s"Invalid certificate import: $ref")
          imported(index)

      proof.steps.zipWithIndex.foreach: (step, index) =>
        translated(index) = step match
          case step: ProofStep =>
            output += ProofStep.mapPremises(step, resolve(_, index))
            output.size - 1
          case Subproof(inner, premises) =>
            require(inner.imports.size == premises.size, "Supply one premise for each subproof import")
            val innerImports = inner.imports.zip(premises).map: (expected, ref) =>
              val source = resolve(ref, index)
              val actual = if source < 0 then imports(-source - 1) else output(source).statement
              if actual == expected then source
              else
                // The linear checker must validate even an unused subproof import.
                output += Restate(expected, source)
                output.size - 1
            emit(inner, innerImports.toArray)
      translated.last

    if steps.nonEmpty then emit(this, imports.indices.map(i => -i - 1).toArray)
    LinearProof(output.toArray, imports.toArray)

  /** Flatten and check every step, reporting malformed certificate structure as a failure. */
  def check(using theory: Theory = Theory.empty): Either[Exception, Thm] =
    try toLinearProof.check(using theory)
    catch case NonFatal(error: Exception) => Left(error)

object ProofCertificate:
  def apply(step: CertificateStep): ProofCertificate = ProofCertificate(IndexedSeq(step))

  /** Wrap an already linear certificate without changing its steps or imports. */
  def fromLinearProof(proof: LinearProof): ProofCertificate =
    ProofCertificate(proof.steps.toIndexedSeq, proof.imports.toIndexedSeq)
