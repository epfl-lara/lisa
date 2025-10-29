package lisa.tptp

import leo.modules.input.TPTPParser
import lisa.kernel.proof.SCProofCheckerJudgement.SCInvalidProof
import lisa.tptp.KernelParser
import lisa.tptp.ProofParser
import lisa.utils.K
import lisa.utils.K.>>:
import lisa.utils.K.given
import lisa.utils.K.lambda
import lisa.utils.K.repr
import org.scalatest.compatible.Assertion
import org.scalatest.funsuite.AnyFunSuite

import java.io.File
import scala.io.Source

import ProofParser._
import KernelParser._
import K.SCProofChecker

class LVL1Test extends AnyFunSuite {

  private val sources = getClass.getResource("/steps_tests").getPath
  println(s"Sources: $sources")

  private val problems = Seq[(String, String)](
    "cut.p" -> "cut rule tests",
    "hyp.p" -> "hyp rule tests",
    "instFun.p" -> "instFun rule tests",
    "instPred.p" -> "instPred rule tests",
    "leftForall.p" -> "leftForall rule tests",
    "leftAnd.p" -> "leftAnd rule tests",
    "leftExists.p" -> "leftExists rule tests",
    "leftIff.p" -> "leftIff rule tests",
    "leftImplies.p" -> "leftImplies rule tests",
    "leftNot.p" -> "leftNot rule tests",
    "leftOr.p" -> "leftOr rule tests",
    "leftSubst.p" -> "leftSubst rule tests",
    "leftSubstIff.p" -> "leftSubstIff rule tests",
    "leftWeaken.p" -> "leftWeaken rule tests",
    "rightForall.p" -> "rightForall rule tests",
    "rightAnd.p" -> "rightAnd rule tests",
    "rightExists.p" -> "rightExists rule tests",
    "rightIff.p" -> "rightIff rule tests",
    "rightImplies.p" -> "rightImplies rule tests",
    "rightNot.p" -> "rightNot rule tests",
    "rightOr.p" -> "rightOr rule tests",
    "rightRefl.p" -> "rightRefl rule tests",
    "rightSubst.p" -> "rightSubst rule tests",
    "rightSubstIff.p" -> "rightSubstIff rule tests",
    "rightWeaken.p" -> "RightWeaken rule tests"
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
