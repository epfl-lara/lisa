package test

import utilities.Printer
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SCProofChecker._
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.kernel.proof.SequentCalculus.isSameSequent
import lisa.settheory.AxiomaticSetTheory
import org.scalatest.funsuite.AnyFunSuite
import utilities.Helpers._
import utilities.Helpers.given_Conversion_Boolean_List_String_Option

abstract class ProofCheckerSuite extends AnyFunSuite {
  import lisa.kernel.fol.FOL.*

  protected val (xl, yl, zl, wl, xpl, ypl, zpl, wpl) = (
    SchematicFunctionLabel("x", 0),
    SchematicFunctionLabel("y", 0),
    SchematicFunctionLabel("z", 0),
    SchematicFunctionLabel("w", 0),
    SchematicFunctionLabel("x'", 0),
    SchematicFunctionLabel("y'", 0),
    SchematicFunctionLabel("z'", 0),
    SchematicFunctionLabel("w'", 0)
  )
  protected val (x, y, z, w, xp, yp, zp, wp) = (
    FunctionTerm(xl, Seq.empty),
    FunctionTerm(yl, Seq.empty),
    FunctionTerm(zl, Seq.empty),
    FunctionTerm(wl, Seq.empty),
    FunctionTerm(xpl, Seq.empty),
    FunctionTerm(ypl, Seq.empty),
    FunctionTerm(zpl, Seq.empty),
    FunctionTerm(wpl, Seq.empty)
  )

  protected val (sl, tl, ul, vl) = (VariableLabel("s"), VariableLabel("t"), VariableLabel("u"), VariableLabel("v"))
  protected val (s, t, u, v) = (VariableTerm(sl), VariableTerm(tl), VariableTerm(ul), VariableTerm(vl))

  val axioms = AxiomaticSetTheory.axioms
  def checkProof(proof: SCProof): Unit = {
    val judgement = checkSCProof(proof)
    println(Printer.prettySCProof(judgement))
    println(s"\n(${proof.totalLength} proof steps in total)")
  }

  def checkProof(proof: SCProof, expected: Sequent): Unit = {
    val judgement = checkSCProof(proof)
    assert(judgement.isValid, "\n" + Printer.prettySCProof( judgement))
    assert(isSameSequent(proof.conclusion, expected), s"(${Printer.prettySequent(proof.conclusion)} did not equal ${Printer.prettySequent(expected)})")
  }

  def checkIncorrectProof(incorrectProof: SCProof): Unit = {
    assert(
      !checkSCProof(incorrectProof).isValid,
      s"(incorrect proof with conclusion '${Printer.prettySequent(incorrectProof.conclusion)}' was accepted by the proof checker)\nSequent: ${incorrectProof.conclusion}"
    )
  }
}
