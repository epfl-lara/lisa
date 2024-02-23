package lisa.utils.tptp

import leo.modules.input.{TPTPParser => Parser}
import Parser.TPTPParseException
import leo.datastructures.TPTP.FOFAnnotated

import ProofParser.*
import KernelParser.*
import lisa.utils.K
import java.io.File

object Test {
  def main(args: Array[String]): Unit = {
    val stringfof = """fof(intersection_defn,axiom,
    ! [B,C,D] :  member(D,intersection(B,C)), inference(hyp, param(4, $fot(X), 5, 6), [i1, i2]))."""

    val stringfof2 = """fof(intersection_defn,axiom,
    [ ! [B,C,D] :  member(D,intersection(B,C)) ] --> [ ! [B,C,D] :  member(D,intersection(B,C)) ] )."""


    val annotatedFormulaFOF = Parser.annotatedFOF(stringfof)
    println(annotatedFormulaFOF.annotations)
    println("--")
    println(annotatedFormulaFOF.annotations match {
      case Inference(stepName, parameters, numbers) => println(parameters)
    })
    //println(s"${annotatedFormulaFOF.name} is an ${annotatedFormulaFOF.role}. It has annotations ${annotatedFormulaFOF.annotations}.")

    val annotatedFormulaFOF2 = Parser.annotatedFOF(stringfof2)
    //println(s"${annotatedFormulaFOF2.name} is an ${annotatedFormulaFOF2.role}. It has annotations ${annotatedFormulaFOF2.annotations}.")

    println("--------- Now, stringfof3")

    val stringfof3 = "fof(i6, plain, [~(~(($true & ((~(a_1) & a_1) | (~(b_2) & b_2))))), ($true & ((~(a_1) & a_1) | (~(b_2) & b_2))), $true, ((~(a_1) & a_1) | (~(b_2) & b_2)), (~(a_1) & a_1), ~(a_1), a_1] --> [], inference(leftHyp, param(6, 5), [])). "
    val annotatedFormulaFOF3 = Parser.annotatedFOF(stringfof3)
    given numbermap: (String => Int) = _ => 0
    annotatedFormulaFOF3 match {
      case Inference.Hypothesis(step, name) => println(s"Found a proof:\n ${lisa.utils.parsing.FOLPrinter.prettySCProof(K.SCProof(step))}")
      case _ => println(s"Did not find a hypothesis")
    }


    println("Now, full proof")
    val proofFile = new File("/home/sguilloud/Desktop/tstpProblem.p")
    val proof = reconstructProof(proofFile)
    println(s"Proof:\n${lisa.utils.parsing.FOLPrinter.prettySCProof(proof)}")
    println("Proof successfuly constructed!")
    val jdg = K.SCProofChecker.checkSCProof(proof)
    println(s"Proof is correct: ${jdg.isValid}")

    println("--------- Now, producing files")

    import K.*
    val x = variable
    val P = predicate(1)
    val sequent = () |- P(x)


  }

}

/* 

    // Alpha rules
    case gs3.NNOT:        resultingString, childrenHypotheses = alphaStep(proof, hypotheses, target, "leftNotNot")
    case gs3.AND:        resultingString, childrenHypotheses = alphaStep(proof, hypotheses, target, "leftAnd")
    case gs3.NOR:        resultingString, childrenHypotheses = alphaStep(proof, hypotheses, target, "leftNotOr")
    case gs3.NIMP:        resultingString, childrenHypotheses = alphaStep(proof, hypotheses, target, "leftNotImp")
    // Beta rules
    case gs3.NEQU:        resultingString, childrenHypotheses = betaStep(proof, hypotheses, target, "leftNotEqu")
    case gs3.NAND:        resultingString, childrenHypotheses = betaStep(proof, hypotheses, target, "leftNotAnd")
    case gs3.OR:        resultingString, childrenHypotheses = betaStep(proof, hypotheses, target, "leftOr")
    case gs3.IMP:        resultingString, childrenHypotheses = betaStep(proof, hypotheses, target, "leftImp")
    // Delta rules
    case gs3.NALL:        resultingString, childrenHypotheses = deltaStep(proof, hypotheses, target, "leftNotForall")
    case gs3.EX:        resultingString, childrenHypotheses = deltaStep(proof, hypotheses, target, "leftEx")
    // Gamma rules
    case gs3.ALL:        resultingString, childrenHypotheses = gammaStep(proof, hypotheses, target, "leftForall")
    case gs3.NEX:        resultingString, childrenHypotheses = gammaStep(proof, hypotheses, target, "leftNotEx")
    // Weakening rule
    case gs3.W:        
*/