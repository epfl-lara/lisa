package lisa.test

import lisa.kernel.proof.SequentCalculus as SC
import lisa.utils.prooflib.BasicMain
import lisa.utils.prooflib.BasicStepTactic.*
import lisa.utils.prooflib.Library
import lisa.utils.prooflib.ProofTacticLib
import org.scalatest.funsuite.AnyFunSuite

import scala.collection.immutable.LazyList
import leo.datastructures.TPTP.FOF.Term

trait ProofTacticTestLib extends AnyFunSuite with BasicMain {

  export lisa.test.TestTheoryLibrary.{_, given}

  private val x = variable[Ind]
  private val P = variable[Ind >>: Prop]

  // generate a placeholde theorem to take ownership of proofs for test
  val placeholderTheorem: THMFromProof = Theorem(P(x) |- P(x)) { have(P(x) |- P(x)) by Hypothesis }.asInstanceOf

  // generates an empty proof owned by the placeholder theorem for testing
  def generateTestProof() = new BaseProof(placeholderTheorem)

  // introduces a 'proofless' step without verification into a given proof object
  // the step cannot be passed through the kernel for verification in any way,
  // but does allow for using them as premise to test tactics
  // extreme jank :)
  def introduceSequent(using proof: Proof)(seq: Sequent) = proof.newProofStep(
    proof.ValidProofTactic(
      P(x),
      Seq(SC.Hypothesis(seq.underlying, P(x).underlying)),
      Seq()
    )(using Hypothesis)
  )

  // given a list of test cases and a function to pass them through a tactic, simply checks them
  def testTacticCases[A](using proof: Proof)(correct: List[A], incorrect: List[A])(t: A => proof.ProofTacticJudgement): Unit = {
    for (testCase <- correct)
      t(testCase) match {
        case j: proof.ValidProofTactic => true
        case j: proof.InvalidProofTactic => fail(s"Correct step failed! ${j.message}")
      }

    for (testCase <- incorrect)
      t(testCase) match {
        case j: proof.ValidProofTactic => fail(s"Incorrect step passed!")
        case j: proof.InvalidProofTactic => true
      }
  }

  // proof object constructed 'out of context' for testing
  // supports adding sequents for use as premises without verification
  // see `introduceSequent`
  val testProof = new BaseProof(placeholderTheorem)
  given Proof = testProof
}
