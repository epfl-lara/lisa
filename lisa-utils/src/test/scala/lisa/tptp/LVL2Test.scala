package lisa.tptp

import org.scalatest.compatible.Assertion
import org.scalatest.funsuite.AnyFunSuite
import scala.io.Source
import java.io.File
import ProofParser.*
import KernelParser.*
import lisa.utils.K
import lisa.utils.K.{>>:, repr, lambda, given}
import K.SCProofChecker

import leo.modules.input.TPTPParser
import lisa.kernel.proof.SCProofCheckerJudgement.SCInvalidProof
import lisa.tptp.{ProofParser, KernelParser}

class LVL2Test extends AnyFunSuite {

  private val sources = getClass.getResource("/level2_steps").getPath
  println(s"Sources: $sources")

  private val problems = Seq[(String, String)](
    "instMult.p" -> "instMult rule tests"
  )

  for (p <- problems) {
    test(p._2) {
      try {
        val res = reconstructProof(File(s"$sources/${p._1}"))(using lisa.tptp.KernelParser.strictMapAtom, lisa.tptp.KernelParser.strictMapTerm, lisa.tptp.KernelParser.strictMapVariable)
        val judgement = SCProofChecker.checkSCProof(res)
        assert(judgement.isValid, K.prettySCProof(judgement))

        println(s"Parsed ${p._1}")
      } catch {
        case e: TPTPParser.TPTPParseException =>
          println(s"Parse error at line ${e.line}:${e.offset}: ${e.getMessage}")
          fail()
      }
    }
  }

}
