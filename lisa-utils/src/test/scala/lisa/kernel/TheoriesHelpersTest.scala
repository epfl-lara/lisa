package lisa.test.kernel

import lisa.kernel.fol.FOL._
import lisa.kernel.proof.RunningTheoryJudgement.InvalidJustification
import lisa.kernel.proof.RunningTheoryJudgement.InvalidJustificationException
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.Hypothesis
import lisa.test.TestTheory
import lisa.utils.KernelHelpers.{_, given}
import lisa.utils.{_, given}
import org.scalatest.funsuite.AnyFunSuite

/**
 * Check that a simple incorrect theorem is not accepted and a single correct theorem is accepted.
 */
class TheoriesHelpersTest extends AnyFunSuite {
  export TestTheory.*

  test("theorem with incorrect statement") {
    val (c0, c1) = (Constant("Z", Ind), Constant("S", Ind))
    runningTestTheory.addSymbol(c0)
    runningTestTheory.addSymbol(c1)

    val judgement = runningTestTheory.theorem("False theorem", c1 === c0, SCProof(Hypothesis((c0 === c1) |- (c0 === c1), c0 === c1)), Seq())
    assert(!judgement.isValid)
    try {
      judgement.get
      fail("Shouldn't be able to get a theorem from an invalid judgement")
    } catch {
      case InvalidJustificationException(msg, None) => ()
    }

    // same theorem but with correct statement

    assert(
      runningTestTheory.theorem("True theorem", c1 === c0 |- c1 === c0, SCProof(Hypothesis((c0 === c1) |- (c0 === c1), c0 === c1)), Seq()).isValid,
      runningTestTheory.theorem("True theorem", c1 === c0 |- c1 === c0, SCProof(Hypothesis((c0 === c1) |- (c0 === c1), c0 === c1)), Seq()).repr
    )
  }

}
