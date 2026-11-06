package lisa.utils

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.Sequent
import lisa.utils.kernel.*
import org.scalatest.funsuite.AnyFunSuite

import java.io.*
import java.util.Base64
import java.nio.file.Files
import java.util.zip.{ZipEntry, ZipOutputStream}
import scala.util.Using

class SerializedProofCheckSuite extends AnyFunSuite:
  private val p = Variable(Identifier("p"), Prop)
  private val identity = Sequent(Set(p), Set(p))
  private val closed = LinearProof(Array(Hypothesis(identity, p)), Array.empty)

  private def encode(proofs: LinearProof*): (Array[Byte], Array[Byte]) =
    val trees = new ByteArrayOutputStream()
    val steps = new ByteArrayOutputStream()
    Serialization.proofsToDataStream(new DataOutputStream(trees), new DataOutputStream(steps),
      proofs.zipWithIndex.map((proof, index) => (s"proof$index", proof, Nil)))
    (trees.toByteArray, steps.toByteArray)

  private def check(bytes: (Array[Byte], Array[Byte])) =
    SerializedProofCheck.check(new ByteArrayInputStream(bytes._1), new ByteArrayInputStream(bytes._2))

  test("check a fixed proof exported by the non-LCF checker"):
    def fixture(extension: String): Array[Byte] =
      Using.resource(getClass.getResourceAsStream(s"/serialization/tptp-syn040-1.$extension.b64")): stream =>
        Base64.getMimeDecoder.decode(stream.readAllBytes())
    val results = check((fixture("trees"), fixture("proof")))
    assert(results.map(r => (r.name, r.steps, r.imports)) == Seq(("theBenchmark.p", 51, 5)))

  test("check every named proof and report declared imports"):
    val imported = LinearProof(Array(Restate(identity, -1)), Array(identity))
    val results = check(encode(closed, imported))
    assert(results.map(_.name) == Seq("proof0", "proof1"))
    assert(results.map(_.steps) == Seq(1, 1))
    assert(results.map(_.imports) == Seq(0, 1))

  test("reject invalid kernel steps rather than only decoding them"):
    val invalid = LinearProof(Array(Hypothesis(Sequent(Set.empty, Set(p)), p)), Array.empty)
    val error = intercept[IllegalArgumentException](check(encode(invalid)))
    assert(error.getCause.isInstanceOf[InvalidStepError])

  test("reject invalid premise references"):
    val invalid = LinearProof(Array(Restate(identity, -1)), Array.empty)
    val error = intercept[IllegalArgumentException](check(encode(invalid)))
    assert(error.getCause == InvalidImportError(-1))

  test("reject trusted steps even when unused"):
    Seq(Sorry(identity), Axiom(identity), Assume(identity)).foreach: trusted =>
      val proof = LinearProof(Array(trusted, Hypothesis(identity, p)), Array.empty)
      assert(intercept[IllegalArgumentException](check(encode(proof))).getMessage.contains("trusted proof step"))

  test("reject empty bundles and empty proofs"):
    intercept[IllegalArgumentException](check(encode()))
    intercept[IllegalArgumentException](check(encode(LinearProof(Array.empty, Array.empty))))

  test("reject truncated trees and proof records"):
    val (trees, steps) = encode(closed)
    intercept[Serialization.IncompleteTreeException](check((trees.dropRight(1), steps)))
    intercept[EOFException](check((trees, steps.dropRight(1))))

  test("reject trailing proof data"):
    val (trees, steps) = encode(closed)
    intercept[IllegalArgumentException](check((trees, steps ++ Array[Byte](0))))

  test("report missing pairs and continue checking the remaining archive"):
    val directory = Files.createTempDirectory("lisa-proof-check-")
    val archive = directory.resolve("proofs.zip")
    val report = directory.resolve("results.tsv")
    val (trees, steps) = encode(closed)
    try
      Using.resource(new ZipOutputStream(Files.newOutputStream(archive))): zip =>
        Seq("a/proof.trees" -> trees, "b/proof.trees" -> trees, "b/proof.proof" -> steps).foreach: (name, bytes) =>
          zip.putNextEntry(new ZipEntry(name))
          zip.write(bytes)
          zip.closeEntry()
      intercept[IllegalArgumentException](SerializedProofCheck.main(Array(archive.toString, report.toString)))
      val rows = Files.readString(report)
      assert(rows.contains("a/proof\t\tFAIL"))
      assert(rows.contains("b/proof\tproof0\tPASS"))
    finally
      Files.deleteIfExists(report)
      Files.deleteIfExists(archive)
      Files.deleteIfExists(directory)
