import leo.datastructures.TPTP
import lisa.automation.Tableau
import lisa.automation.Tautology
import lisa.kernel.proof.SCProofChecker.checkSCProof
import lisa.tptp.KernelParser._
import lisa.tptp.ProofParser._
import lisa.tptp.ProofPrinter._
import lisa.tptp._
import lisa.utils.K
import lisa.utils.KernelHelpers._
import mainargs.Flag
import mainargs.ParserForMethods
import mainargs.arg
import mainargs.main

import java.io.File

import sys.process._

object TPTP_Lisa {

  @main
  def check(
      @arg(doc = "Input File")
      input: String
  ) = {
    val proof = reconstructProof(File(input))(using strictMapAtom, strictMapTerm, strictMapVariable)
    val judgement = checkSCProof(proof)
    if (judgement.isValid) {
      println("The translation of the proof in Lisa is valid.")
    } else {
      println("The translation of the proof in Lisa is invalid.")
      println(prettySCProof(judgement))
    }
  }

  @main
  def tableau(
      @arg(doc = "Input File")
      input: String
  ) = {
    try
      val problem = problemToKernel(File(input))(using strictMapAtom, strictMapTerm, strictMapVariable)
      val sequent = problemToSequent(problem)
      val axioms: Map[Int, (String, K.Sequent)] = problem.axioms.zipWithIndex.map { case (axiom, i) =>
        (i, (axiom.name, () |- axiom.toFormula.formula))
      }.toMap
      val optproof = Tableau.solve(sequent)
      val optproof2 = Tautology.solveSequent(sequent)
      optproof match {
        case Some(proof) =>
          val judgement = checkSCProof(proof)
          if (judgement.isValid) {
            println("% SZS status Theorem")
            val tptp_proof = proofToTPTP(proof, axioms, ("sequent_conjecture", sequent), true)
            val endproof = tptp_proof :+ {
              val prob_conj = leo.datastructures.TPTP.FOF.Logical(formulaToFOFFormula(problem.conjecture.toFormula.formula, Set(), true))
              val axioms_names = problem.axioms.map(_.name)
              leo.datastructures.TPTP.FOFAnnotated("final", "theorem", prob_conj, premisesToAnnotationsStr(axioms_names :+ tptp_proof.last.name, "big_cut"))
            }
            println("% SZS output start Proof")
            println(endproof.map(_.pretty).mkString("\n"))
            println("% SZS output end Proof")
          } else {
            println("% SZS status Error")
            println("A proof was found but rejected by the kernel checker.")
            println(prettySCProof(judgement))
          }

        case None =>
          println("Cannot prove " + sequent.repr)
          println("% SZS status GaveUp")

      }
    catch
      case e =>
        println("% SZS status Error")
        println(s"% Exception: ${e.getMessage}")
        e.getStackTrace().foreach(s => println("% " + s.toString))

  }

  def main(args: Array[String]): Unit = ParserForMethods(this).runOrThrow(args.toIndexedSeq)

}
