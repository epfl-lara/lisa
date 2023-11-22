package lisa.test

import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SCProofChecker.*
import lisa.kernel.proof.SCProofCheckerJudgement
import lisa.kernel.proof.SCProofCheckerJudgement.SCInvalidProof
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.kernel.proof.SequentCalculus.isSameSequent
import lisa.utils.FOLPrinter
import lisa.utils.KernelHelpers.{_, given}
import lisa.utils.Printer
import org.scalatest.funsuite.AnyFunSuite

import scala.language.adhocExtensions

abstract class ProofCheckerSuite(printer: Printer = FOLPrinter) extends AnyFunSuite {

  import lisa.kernel.fol.FOL.*

  protected val (xl, yl, zl, wl, xpl, ypl, zpl, wpl) = (
    VariableLabel("x"),
    VariableLabel("y"),
    VariableLabel("z"),
    VariableLabel("w"),
    VariableLabel("x1"),
    VariableLabel("y1"),
    VariableLabel("z1"),
    VariableLabel("w1")
  )
  protected val (x, y, z, w, xp, yp, zp, wp) = (
    VariableTerm(xl),
    VariableTerm(yl),
    VariableTerm(zl),
    VariableTerm(wl),
    VariableTerm(xpl),
    VariableTerm(ypl),
    VariableTerm(zpl),
    VariableTerm(wpl)
  )

  protected val (sl, tl, ul, vl) = (VariableLabel("s"), VariableLabel("t"), VariableLabel("u"), VariableLabel("v"))
  protected val (s, t, u, v) = (VariableTerm(sl), VariableTerm(tl), VariableTerm(ul), VariableTerm(vl))

  def checkProof(proof: SCProof): Unit = {
    val judgement = checkSCProof(proof)
    assert(judgement.isValid, printer.prettySCProof(judgement, true))
  }

  def checkProof(proof: SCProof, expected: Sequent): Unit = {
    val judgement = checkSCProof(proof)
    assert(judgement.isValid, "\n" + printer.prettySCProof(judgement))
    assert(isSameSequent(proof.conclusion, expected), s"(${printer.prettySequent(proof.conclusion)} did not equal ${printer.prettySequent(expected)})")
  }

  def checkIncorrectProof(incorrectProof: SCProof): Unit = {
    assert(
      !checkSCProof(incorrectProof).isValid,
      s"(incorrect proof with conclusion '${printer.prettySequent(incorrectProof.conclusion)}' was accepted by the proof checker)\nSequent: ${incorrectProof.conclusion}"
    )
  }
}
