import leo.datastructures.TPTP

import lisa.kernel.proof.SCProofChecker.checkSCProof
import lisa.utils.KernelHelpers.* 
import lisa.automation.Tableau
import lisa.automation.Tautology
import lisa.tptp.*
import lisa.tptp.ProofParser.*
import lisa.tptp.ProofPrinter.*
import lisa.tptp.KernelParser.*


import mainargs.{main, arg, ParserForMethods, Flag}

import java.io.File
import sys.process._


object TPTP_Lisa {

  @main
  def check( @arg(doc = "Input File")
              input: String) = {
    val proof = reconstructProof(File("../"+input))(using strictMapAtom, strictMapTerm, strictMapVariable)
    val judgement = checkSCProof(proof)
    if (judgement.isValid) {
      println("The translation of the proof in Lisa is valid.")
    } else {
      println("The translation of the proof in Lisa is invalid.")
      println(prettySCProof(judgement))
    }
  }

  @main
  def tableau(@arg(doc = "Input File")
               input: String) = {
    val problem = problemToKernel(File("../"+input))(using strictMapAtom, strictMapTerm, strictMapVariable)
    val sequent = problemToSequent(problem)
    val optproof = Tableau.solve(sequent)
    val optproof2 = Tautology.solveSequent(sequent)
    optproof match {
      case Some(proof) =>
        val judgement = checkSCProof(proof)
        if (judgement.isValid) {
          println("% SZS status Theorem")
          val tptp_proof = proofToTPTP(proof, Map(), ("sequent_conjecture", sequent), true)
          val endproof = tptp_proof :+ {
            val prob_conj = leo.datastructures.TPTP.FOF.Logical(formulaToFOFFormula(problem.conjecture.toFormula.formula, Set(), true))
            val axioms_names = problem.axioms.map(_.name)
            leo.datastructures.TPTP.FOFAnnotated("final", "plain", prob_conj, premisesToAnnotationsStr(axioms_names, "big_cut"))
          }
          println("TPTP proof:")
          endproof.foreach { p => println(p.pretty) }
        } else {
          println("% SZS status Error")
          println("A proof was found but rejected by the kernel checker.")
          println(prettySCProof(judgement))
        }
        
      case None =>
          println("Cannot prove " + sequent.repr)
          println("% SZS status GaveUp")
        
    }


  }



/*

    val dr2proof = flattenProof(drinkers2.kernelProof.get)
    java.lang.Thread.sleep(5)
    checkProof(dr2proof)
    java.lang.Thread.sleep(5)
    val tptpproof = ProofPrinter.proofToTPTP(dr2proof, Map(), ("drinkers2", drinkers2.statement.underlying))
    tptpproof.foreach { p => println(p.pretty)}
*/

  def main(args: Array[String]): Unit = ParserForMethods(this).runOrThrow(args.toIndexedSeq)


}
