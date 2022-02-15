package test

import lisa.kernel.Printer
import lisa.kernel.proof.SequentCalculus.{Sequent, isSameSequent}
import lisa.kernel.proof.SCProofChecker._
import lisa.settheory.AxiomaticSetTheory
import org.scalatest.funsuite.AnyFunSuite
import lisa.kernel.proof.SCProof
import lisa.KernelHelpers._
import lisa.KernelHelpers.given_Conversion_Boolean_List_String_Option

abstract class ProofCheckerSuite extends AnyFunSuite {
  import lisa.kernel.fol.FOL.*

  protected val (xl, yl, zl, wl, xpl, ypl, zpl, wpl) = (SchematicFunctionLabel("x", 0), SchematicFunctionLabel("y", 0), SchematicFunctionLabel("z", 0), SchematicFunctionLabel("w", 0), SchematicFunctionLabel("x'", 0), SchematicFunctionLabel("y'", 0), SchematicFunctionLabel("z'", 0), SchematicFunctionLabel("w'", 0))
  protected val (x, y, z, w, xp, yp, zp, wp) = (FunctionTerm(xl, Seq.empty), FunctionTerm(yl, Seq.empty), FunctionTerm(zl, Seq.empty), FunctionTerm(wl, Seq.empty), FunctionTerm(xpl, Seq.empty), FunctionTerm(ypl, Seq.empty), FunctionTerm(zpl, Seq.empty), FunctionTerm(wpl, Seq.empty))

  protected val (sl, tl, ul, vl) = (VariableLabel("s"), VariableLabel("t"), VariableLabel("u"), VariableLabel("v"))
  protected val (s, t, u, v) = (VariableTerm(sl), VariableTerm(tl), VariableTerm(ul), VariableTerm(vl))

  val axioms = AxiomaticSetTheory.axioms
  def checkProof(proof: SCProof): Unit = {
    val error = checkSCProof(proof)
    println(Printer.prettySCProof(proof, error))
    println(s"\n(${proof.totalLength} proof steps in total)")
  }

  def checkProof(proof: SCProof, expected: Sequent): Unit = {
    val error = checkSCProof(proof)
    assert(error._1, "\n"+Printer.prettySCProof(proof, error))
    assert(isSameSequent(proof.conclusion, expected), s"(${Printer.prettySequent(proof.conclusion)} did not equal ${Printer.prettySequent(expected)})")
  }

  def checkIncorrectProof(incorrectProof: SCProof): Unit = {
    assert(!checkSCProof(incorrectProof)._1, s"(incorrect proof with conclusion '${Printer.prettySequent(incorrectProof.conclusion)}' was accepted by the proof checker)\nSequent: ${incorrectProof.conclusion}")
  }
}
