package lisa.test.utils

import org.scalatest.funsuite.AnyFunSuite

import scala.language.adhocExtensions
/*
import utilities.Helpers.*
import utilities.Printer
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.*
import lisa.kernel.proof.SequentCalculus.*
import lisa.settheory.AxiomaticSetTheory.*
import lisa.kernel.proof.SCProofCheckerJudgement.*
import org.scalatest.funsuite.AnyFunSuite
import me.cassayre.florian.masterproject.util.SCProofBuilder.{_{_, given}

import util.chaining.*
import scala.util.{Failure, Success, Try}
 */
class SCProofStepFinderTests extends AnyFunSuite {
  /*
  test("proof steps reconstruction") {
    // These tests ensure that all the kernel proof steps can be generated
    // To achieve that, we design proofs that require these steps to be used at some point

    val (x, y, z) = (VariableLabel("x"), VariableLabel("y"), VariableLabel("z"))
    val theory = new RunningTheory()
    val (la, lb, lc) = (ConstantPredicateLabel("a", 0), ConstantPredicateLabel("b", 0), ConstantPredicateLabel("c", 0))
    Seq(la, lb, lc).foreach(theory.addSymbol)
    val (a, b, c) = (PredicateFormula(la, Seq.empty), PredicateFormula(lb, Seq.empty), PredicateFormula(lc, Seq.empty))
    val (ls, lt) = (ConstantFunctionLabel("s", 0), ConstantFunctionLabel("t", 0))
    Seq(ls, lt).foreach(theory.addSymbol)
    val (s, t) = (FunctionTerm(ls, Seq.empty), FunctionTerm(lt, Seq.empty))

    implicit class VariableLabelEq(l: VariableLabel) { // Helper due to conflicts with scalatest's `===`
      def ====(r: Term): Formula = PredicateFormula(equality, Seq(VariableTerm(l), r))
      def ====(r: VariableLabel): Formula = PredicateFormula(equality, Seq(VariableTerm(l), VariableTerm(r)))
    }
    implicit class FunctionLabelEq(l: FunctionLabel) {
      def ====(r: Term): Formula = PredicateFormula(equality, Seq(FunctionTerm(l, Seq.empty), r))
      def ====(r: FunctionLabel): Formula = PredicateFormula(equality, Seq(FunctionTerm(l, Seq.empty), FunctionTerm(r, Seq.empty)))
    }
    implicit class TermEq(l: Term) {
      def ====(r: Term): Formula = PredicateFormula(equality, Seq(l, r))
      def ====(r: FunctionLabel): Formula = PredicateFormula(equality, Seq(l, FunctionTerm(r, Seq.empty)))
    }

    val proofs: Seq[((String, SCProofBuilder), PartialFunction[SCProofStep, Unit])] = Seq(
      // (1.1)
      "Hypothesis" -> SCProofBuilder(
        a |- a,
      ) -> { case _: Hypothesis => () },
      "Cut" -> SCProofBuilder(
        a |- a,
        Seq(a, b) |- a by 0,
        c |- c,
        c |- Seq(b, c) by 2,
        Seq(a, c) |- Seq(a, c) by (1, 3),
      ) -> { case _: Cut => () },
      "LeftAnd" -> SCProofBuilder(
        a |- a,
        (a /\ b) |- a by 0,
      ) -> { case _: LeftAnd => () },
      "RightAnd" -> SCProofBuilder(
        a |- a,
        b |- b,
        Seq(a, b) |- (a /\ b) by (0, 1),
      ) -> { case _: RightAnd => () },
      "LeftOr" -> SCProofBuilder(
        a |- a,
        b |- b,
        Seq(a, b, a \/ b) |- Seq(a, b) by (0, 1)
      ) -> { case _: LeftOr => () },
      "RightOr" -> SCProofBuilder(
        a |- a,
        a |- (a \/ b) by 0,
      ) -> { case _: RightOr => () },
      "LeftImplies" -> SCProofBuilder(
        a |- a,
        b |- b,
        Seq(a, a ==> b) |- b by (0, 1),
      ) -> { case _: LeftImplies => () },
      "RightImplies" -> SCProofBuilder(
        a |- a,
        a |- Seq(a, a ==> a) by 0,
      ) -> { case _: RightImplies => () },
      "LeftIff" -> SCProofBuilder(
        (a ==> b) |- (a ==> b),
        (a <=> b) |- (a ==> b) by 0,
      ) -> { case _: LeftIff => () },
      "RightIff" -> SCProofBuilder(
        (a ==> b) |- (a ==> b),
        (b ==> a) |- (b ==> a),
        Seq(a ==> b, b ==> a) |- (a <=> b) by (0, 1),
      ) -> { case _: RightIff => () },
      "LeftNot" -> SCProofBuilder(
        a |- a,
        a |- Seq(a, b) by 0,
        Seq(a, !b) |- a by 1,
      ) -> { case _: LeftNot => () },
      "RightNot" -> SCProofBuilder(
        a |- a,
        Seq(a, b) |- a by 0,
        a |- Seq(a, !b) by 1,
      ) -> { case _: RightNot => () },
      "LeftForall" -> SCProofBuilder(
        (y ==== z) |- (y ==== z),
        forall(x, x ==== z) |- (y ==== z) by 0,
      ) -> { case _: LeftForall => () },
      "RightForall" -> SCProofBuilder(
        (y ==== z) |- (y ==== z),
        (y ==== z) |- forall(x, y ==== z) by 0,
      ) -> { case _: RightForall => () },
      "LeftExists" -> SCProofBuilder(
        (y ==== z) |- (y ==== z),
        exists(x, y ==== z) |- (y ==== z) by 0,
      ) -> { case _: LeftExists => () },
      "RightExists" -> SCProofBuilder(
        (y ==== z) |- (y ==== z),
        (y ==== z) |- exists(x, x ==== z) by 0,
      ) -> { case _: RightExists => () },
      "LeftExistsOne" -> SCProofBuilder(
        exists(y, forall(x, (x ==== y) <=> a)).pipe(f => f |- f),
        existsOne(x, a) |- exists(y, forall(x, (x ==== y) <=> a)) by 0,
      ) -> { case _: LeftExistsOne => () },
      "RightExistsOne" -> SCProofBuilder(
        exists(y, forall(x, (x ==== y) <=> a)).pipe(f => f |- f),
        exists(y, forall(x, (x ==== y) <=> a)) |- existsOne(x, a) by 0,
      ) -> { case _: RightExistsOne => () },
      "(Left)Weakening" -> SCProofBuilder(
        a |- a,
        Seq(a, b) |- a by 0,
      ) -> { case _: Weakening => () },
      "(Right)Weakening" -> SCProofBuilder(
        a |- a,
        a |- Seq(a, b) by 0,
      ) -> { case _: Weakening => () },
      // (1.2)
      "LeftSubstEq" -> SCProofBuilder(
        (s ==== emptySet) |- (s ==== emptySet),
        Seq(s ==== t, t ==== emptySet) |- (s ==== emptySet) by 0,
      ) -> { case _: LeftSubstEq => () },
      "RightSubstEq" -> SCProofBuilder(
        (s ==== emptySet) |- (s ==== emptySet),
        Seq(s ==== emptySet, s ==== t) |- Seq(s ==== emptySet, t ==== emptySet) by 0,
      ) -> { case _: RightSubstEq => () },
      "LeftSubstIff" -> SCProofBuilder(
        a |- a,
        Seq(b, a <=> b) |- a by 0,
      ) -> { case _: LeftSubstIff => () },
      "RightSubstIff" -> SCProofBuilder(
        a |- a,
        Seq(a, a <=> b) |- b by 0,
      ) -> { case _: RightSubstIff => () },
      "LeftRefl" -> SCProofBuilder(
        a |- a,
        Seq(a, b) |- a by 0,
        Seq(a, b, emptySet ==== emptySet) |- a by 1,
        Seq(a, b) |- a by 2,
      ) -> { case _: LeftRefl => () },
      "RightRefl" -> SCProofBuilder(
        () |- (emptySet ==== emptySet),
      ) -> { case _: RightRefl => () },
    )

    proofs.foreach { case ((testname, proofBuilder), partialFunction) =>
      val filter: SCProofStep => Boolean = partialFunction.lift(_).nonEmpty
      Try(proofBuilder.build) match {
        case Success(proof) =>
          SCProofChecker.checkSCProof(proof) match {
            case SCValidProof(_) => // OK
              println(testname)
              println(FOLPrinter.prettySCProof(proof))
              println()
              // Dirty, but only way to test that
              val proofWithoutLast = proof.copy(steps = proof.steps.init)
              proofBuilder.steps.last match {
                case SCImplicitProofStep(conclusion, premises, imports) =>
                  val view = SCProofStepFinder.findPossibleProofSteps(proofWithoutLast, conclusion, premises)
                  assert(view.exists(filter), s"The proof step finder was not able to find the step '$testname'")
                case SCExplicitProofStep(step) => assert(false)
              }
            case invalid: SCInvalidProof => throw new AssertionError(s"The reconstructed proof for '$testname' is incorrect:\n${FOLPrinter.prettySCProof(invalid)}")
          }
        case Failure(exception) => throw new AssertionError(s"Couldn't reconstruct the proof for '$testname'", exception) // Couldn't reconstruct this proof
      }
    }
  }
   */
}
