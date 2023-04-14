package lisa.kernel

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.*
import lisa.test.ProofCheckerSuite
import lisa.utils.KernelHelpers._
import lisa.utils.KernelHelpers.given_Conversion_Identifier_String
import lisa.utils.KernelHelpers.given_Conversion_String_Identifier

import scala.collection.immutable.SortedSet
import scala.language.implicitConversions

class IncorrectProofsTests extends ProofCheckerSuite {
  // These tests help to ensure that the proof checker correctly rejects incorrect proofs
  // The cases are designed to be almost correct (but still incorrect) proofs to check various parts of the system

  test("Minimal incorrect proofs") {
    // Shorthand
    implicit def proofStepToProof(proofStep: SCProofStep): SCProof = SCProof(proofStep)

    val (fl, gl, hl) = (VariableFormulaLabel("f"), VariableFormulaLabel("g"), VariableFormulaLabel("h"))
    val f = PredicateFormula(fl, Seq.empty) // Some arbitrary formulas
    val g = PredicateFormula(gl, Seq.empty)
    val h = PredicateFormula(hl, Seq.empty)

    val incorrectProofs: Seq[SCProof] = List(
      SCProof(
        Hypothesis(emptySeq +<< (x === x) +>> (x === x), x === x),
        LeftRefl(emptySeq +>> (x === y), 0, x === x)
      ),
      SCProof(
        Hypothesis(emptySeq +<< (x === y) +>> (x === y), x === y),
        LeftRefl(emptySeq +>> (x === y), 0, x === y)
      ),
      RightRefl(emptySeq +>> (x === y), x === y),
      RightRefl(emptySeq +>> f, x === x),
      RightRefl(emptySeq +>> (x === x), f),
      // Correct proof would be: x=y |- x=y \ x=y,x=z |- z=y

      SCProof(
        Hypothesis(emptySeq +<< (x === y) +>> (x === y), x === y),
        RightSubstEq(emptySeq +<< (x === y) +<< (x === z) +>> (z === y), 0, List((x, z)), LambdaTermFormula(Seq(yl), x === y)) // wrong variable replaced
      ),
      SCProof(
        Hypothesis(emptySeq +<< (x === y) +>> (x === y), x === y),
        RightSubstEq(emptySeq +<< (x === y) +>> (z === y), 0, List((x, z)), LambdaTermFormula(Seq(xl), x === y)) // missing hypothesis
      ),
      SCProof(
        Hypothesis(emptySeq +<< (x === y) +>> (x === y), x === y),
        RightSubstEq(emptySeq +<< (x === y) +<< (x === z) +>> (z === y), 0, List((x, z)), LambdaTermFormula(Seq(xl), x === z)) // replacement mismatch
      ),
      SCProof(
        Hypothesis(emptySeq +<< (x === y) +>> (x === y), x === y),
        LeftSubstEq(emptySeq +<< (z === y) +<< (x === z) +>> (x === y), 0, List((x, z)), LambdaTermFormula(Seq(yl), x === y))
      ),
      SCProof(
        Hypothesis(emptySeq +<< (f <=> g) +>> (f <=> g), f <=> g),
        LeftSubstIff(emptySeq +<< (h <=> g) +<< (f <=> h) +>> (f <=> g), 0, List((f, h)), LambdaFormulaFormula(Seq(gl), f <=> g))
      ),
      SCProof(
        Hypothesis(emptySeq +<< f +>> f, f),
        LeftAnd(emptySeq +<< g +>> f, 0, f, g)
      ),
      SCProof(
        Hypothesis(emptySeq +<< f +>> f, f),
        Hypothesis(emptySeq +<< g +>> g, g),
        LeftImplies(emptySeq +<< (g ==> f) +<< f +>> g, 0, 1, f, g)
      ),
      SCProof(
        Hypothesis(emptySeq +<< f +>> f, f),
        Hypothesis(emptySeq +<< g +>> g, g),
        LeftOr(emptySeq +<< (f \/ g) +<< f +>> g, Seq(0, 1), Seq(f, g))
      ),
      SCProof(
        Hypothesis(emptySeq +<< f +>> f, f),
        LeftNot(emptySeq +<< f +>> f, 0, f)
      ),
      SCProof(
        Hypothesis(emptySeq +<< f +>> f, f),
        Hypothesis(emptySeq +<< g +>> g, g),
        RightAnd(emptySeq +<< f +>> (f /\ g), Seq(0, 1), Seq(f, g)) // missing left g
      ),
      SCProof(
        Hypothesis(emptySeq +<< f +>> f, f),
        RightOr(emptySeq +<< f +>> (f \/ g) +>> g, 0, f, g) // supplemental right g
      )
    )

    incorrectProofs.foreach(checkIncorrectProof)
  }

}
