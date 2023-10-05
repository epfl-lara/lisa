package lisa.test.utils

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheoryJudgement.InvalidJustification
import lisa.kernel.proof.RunningTheoryJudgement.InvalidJustificationException
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.Hypothesis
import lisa.test.TestTheory
import lisa.utils.KernelHelpers.{_, given}
import lisa.utils.{_, given}
import org.scalatest.funsuite.AnyFunSuite

class TheoriesHelpersTest extends AnyFunSuite {
  export TestTheory.*

  test("theorem with incorrect statement") {
    val (s0, s1) = (ConstantFunctionLabel("0", 0), ConstantFunctionLabel("1", 0))
    runningTestTheory.addSymbol(s0)
    runningTestTheory.addSymbol(s1)
    val (c0, c1) = (s0(), s1())
    val judgement = runningTestTheory.theorem("False theorem", c1 === c0, SCProof(Hypothesis((c0 === c1) |- (c0 === c1), c0 === c1)), Seq())
    assert(!judgement.isValid)
    try {
      judgement.get
      fail("Shouldn't be able to get a theorem from an invalid judgement")
    } catch {
      case InvalidJustificationException(msg, None) => assert(msg.matches("The proof proves .* instead of .*"))
    }

    // same theorem but with correct statement
    assert(runningTestTheory.theorem("True theorem", c1 === c0 |- c1 === c0, SCProof(Hypothesis((c0 === c1) |- (c0 === c1), c0 === c1)), Seq()).isValid)
  }

}
