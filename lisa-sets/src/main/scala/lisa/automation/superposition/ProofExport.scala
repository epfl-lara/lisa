package lisa.automation.superposition

import lisa.utils.K
import lisa.utils.KernelHelpers.flattenProof
import lisa.utils.Serialization

import java.io.BufferedInputStream
import java.io.BufferedOutputStream
import java.io.DataInputStream
import java.io.DataOutputStream
import java.io.File
import java.io.FileInputStream
import java.io.FileOutputStream
import java.nio.charset.StandardCharsets
import java.nio.file.Files

/**
 * The formats a refutation can be written in. `CascTstp` is the prover's own derivation, written without building
 * a kernel proof; the others export the kernel proof of the certified pipeline.
 */
enum ProofFormat(val name: String):
  case NoProof extends ProofFormat("none")
  case CascTstp extends ProofFormat("casc-tstp")
  case LisaTstp extends ProofFormat("lisa-tstp")
  case ScTptp extends ProofFormat("sc-tptp")
  case Serialized extends ProofFormat("serialized")

  /**
   * Whether this format exports a kernel proof, and so needs the certified pipeline.
   */
  def fromKernel: Boolean = this == LisaTstp || this == ScTptp || this == Serialized

object ProofFormat:
  def parse(s: String): ProofFormat =
    values.find(_.name == s).getOrElse(sys.error(s"unknown proof format '$s'; have ${values.map(_.name).mkString(", ")}"))

/**
 * Writes refutations to files, under fixed names in a given directory: `proof.p` for a TSTP derivation,
 * `proof.trees` and `proof.proof` for a serialized kernel proof.
 */
object ProofExport:

  /**
   * Write the kernel proof `proof` of problem `name` into `dir` in `format`.
   */
  def writeKernel(format: ProofFormat, name: String, proof: K.SCProof, dir: File): Unit =
    require(format.fromKernel, s"${format.name} is not a kernel proof format")
    dir.mkdirs()
    format match
      case ProofFormat.Serialized => writeSerialized(name, proof, dir)
      case ProofFormat.LisaTstp => ???
      case ProofFormat.ScTptp => ???
      case _ => ()

  /**
   * Write a TSTP derivation, as [[Tstp.printRefutation]] prints it, to `dir/proof.p`.
   */
  def writeTstp(tstp: String, dir: File): Unit =
    dir.mkdirs()
    Files.writeString(new File(dir, "proof.p").toPath, tstp, StandardCharsets.UTF_8)

  /**
   * Whether `dir` holds a serialized proof.
   */
  def hasSerialized(dir: File): Boolean = new File(dir, "proof.trees").isFile && new File(dir, "proof.proof").isFile

  /**
   * The proof name and kernel proof serialized in `dir`.
   */
  def readSerialized(dir: File): (String, K.SCProof) =
    val trees = new DataInputStream(new BufferedInputStream(new FileInputStream(new File(dir, "proof.trees"))))
    val proofs = new DataInputStream(new BufferedInputStream(new FileInputStream(new File(dir, "proof.proof"))))
    try
      val (name, proof, _) = Serialization.proofsFromDataStream(trees, proofs).head
      (name, proof)
    finally
      trees.close()
      proofs.close()

  // The serializer does not support subproofs, so the proof is flattened first.
  private def writeSerialized(name: String, proof: K.SCProof, dir: File): Unit =
    val trees = new DataOutputStream(new BufferedOutputStream(new FileOutputStream(new File(dir, "proof.trees"))))
    val proofs = new DataOutputStream(new BufferedOutputStream(new FileOutputStream(new File(dir, "proof.proof"))))
    try Serialization.proofsToDataStream(trees, proofs, Seq((name, flattenProof(proof), Nil)))
    finally
      trees.close()
      proofs.close()
