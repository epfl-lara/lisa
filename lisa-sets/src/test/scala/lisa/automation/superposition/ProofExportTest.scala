package lisa.automation.superposition

import lisa.automation.superposition.bench.FofEvaluation
import lisa.tptp.KernelParser.problemToKernel
import lisa.tptp.KernelParser.strictMapAtom
import lisa.tptp.KernelParser.strictMapTerm
import lisa.tptp.KernelParser.strictMapVariable
import lisa.utils.K
import org.scalatest.funsuite.AnyFunSuite

import java.io.File
import java.nio.file.Files

class ProofExportTest extends AnyFunSuite:

  // Needs equality, so the proof carries substitution steps.
  private val problemText =
    """fof(a1, axiom, ![X]: (p(X) => q(X))).
      |fof(a2, axiom, p(a)).
      |fof(a3, axiom, a = b).
      |fof(c, conjecture, q(b)).
      |""".stripMargin

  private def tempDir(): File = Files.createTempDirectory("proof-export").toFile

  private def problemFile(): File =
    val f = new File(tempDir(), "EXP001+1.p")
    Files.writeString(f.toPath, problemText)
    f

  private def assertValid(proof: K.SCProof): Unit =
    K.SCProofChecker.checkSCProof(proof) match
      case K.SCProofCheckerJudgement.SCValidProof(_, usesSorry) => assert(!usesSorry)
      case other => fail(s"invalid proof: $other")

  test("a serialized kernel proof reads back and checks") {
    val parsed = problemToKernel(problemFile())(using (strictMapAtom, strictMapTerm, strictMapVariable))
    val proof = Prover.proveKernel(Prover.fromTptp(parsed)).fold(o => fail(s"not refuted: $o"), identity)
    val dir = tempDir()
    ProofExport.writeKernel(ProofFormat.Serialized, "EXP001+1", proof, dir)
    val (name, back) = ProofExport.readSerialized(dir)
    assert(name == "EXP001+1")
    assert(back.conclusion == proof.conclusion)
    assert(back.imports == proof.imports)
    assert(!back.steps.exists(_.isInstanceOf[K.SCSubproof]))
    assertValid(back)
  }

  test("the Lisa TSTP and SC-TPTP exports are not implemented yet") {
    val proof = K.SCProof(IndexedSeq(K.RestateTrue(K.Sequent(Set.empty, Set(K.top)))))
    intercept[NotImplementedError](ProofExport.writeKernel(ProofFormat.LisaTstp, "x", proof, tempDir()))
    intercept[NotImplementedError](ProofExport.writeKernel(ProofFormat.ScTptp, "x", proof, tempDir()))
  }

  test("Harness one writes a serialized proof that check accepts") {
    val out = tempDir()
    FofEvaluation.main(Array("one", problemFile().getPath, out.getPath, "proof=serialized", "timeout=20000"))
    assert(ProofExport.hasSerialized(out))
    assertValid(ProofExport.readSerialized(out)._2)
    val report = new java.io.ByteArrayOutputStream()
    Console.withOut(report)(FofEvaluation.main(Array("check", out.getPath)))
    assert(report.toString.contains("1 of 1 proofs valid"), report.toString)
  }

  test("Harness one writes the CASC derivation to proof.p") {
    val out = tempDir()
    FofEvaluation.main(Array("one", problemFile().getPath, out.getPath, "mode=uncert", "proof=casc-tstp", "timeout=20000"))
    val tstp = new File(out, "proof.p")
    assert(tstp.isFile)
    assert(Files.readString(tstp.toPath).contains("SZS output start CNFRefutation"))
  }

  test("a proof format the pipeline cannot produce is rejected") {
    val out = tempDir().getPath
    intercept[RuntimeException](FofEvaluation.main(Array("one", problemFile().getPath, out, "mode=uncert", "proof=serialized")))
    intercept[RuntimeException](FofEvaluation.main(Array("one", problemFile().getPath, out, "proof=casc-tstp")))
  }
