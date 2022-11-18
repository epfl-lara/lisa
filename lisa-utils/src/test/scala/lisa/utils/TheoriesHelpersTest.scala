package lisa.utils

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheoryJudgement.InvalidJustification
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.Hypothesis
import lisa.test.TestTheory
import lisa.utils.Helpers.*
import org.scalatest.funsuite.AnyFunSuite

class TheoriesHelpersTest extends AnyFunSuite {
  export TestTheory.*

  test("theorem with incorrect statement") {
    val (s0, s1) = (ConstantFunctionLabel("0", 0), ConstantFunctionLabel("1", 0))
    runningTestTheory.addSymbol(s0)
    runningTestTheory.addSymbol(s1)
    val (c0, c1) = (s0(), s1())
    val judgement = runningTestTheory.theorem("False theorem", seq"1 = 0", SCProof(Hypothesis((c0 === c1) |- (c0 === c1), c0 === c1)), Seq())
    assert(!judgement.isValid)
    assert(judgement == InvalidJustification("The proof does not prove the claimed statement", None))

    // same theorem but with correct statement
    assert(runningTestTheory.theorem("True theorem", seq"1 = 0 |- 1 = 0", SCProof(Hypothesis((c0 === c1) |- (c0 === c1), c0 === c1)), Seq()).isValid)
  }

}
