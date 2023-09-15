package lisa.utilities

import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.SequentCalculus as SC
import lisa.prooflib.Substitution
import lisa.utils.ProofTacticTestLib
import lisa.utils.parsing.FOLParser.*
import lisa.utils.parsing.FOLPrinter.*
import org.scalatest.funsuite.AnyFunSuite

class SubstitutionTacticTest extends ProofTacticTestLib {

  // subst with formula list
  test("Tactic Tests: Substitution - From theorems and formulas (LR)") {
    val correct = List(
      // (
      //     "sequent before substitution", "sequent after substitution",
      //     List("substSequent1", "|- p <=> q", ...), List("substFormula1", "p <=> q", "p = q",...)
      // ),
      (
        "'P('x) |- 'P('x)",
        "'P('x); 'x = 'y |- 'P('y)",
        List(),
        List("'x = 'y")
      ),
      (
        "'P('x) |- 'P('x)",
        "'P('x); 'x = 'y |- 'P('x)",
        List(),
        List("'x = 'y")
      ),
      (
        "'P('x) |- 'P('x)",
        "'P('x) |- 'P('y)",
        List("|- 'x = 'y"),
        List()
      ),
      (
        "'P('x) |- 'P('x)",
        "'P('x) |- 'P('x)",
        List("|- 'x = 'y"),
        List()
      ),
      (
        "'P('x) |- 'P('x) \\/ 'R('y)",
        "'P('x); 'R('y) <=> 'Q('x) |- 'P('x) \\/ 'Q('x)",
        List("|- 'x = 'y"),
        List("'R('y) <=> 'Q('x)")
      ),
      (
        "'P('x) |- 'P('x) \\/ 'R('y)",
        "'P('x); 'R('y) <=> 'Q('x) |- 'P('x) \\/ 'Q('x)",
        List("|- 'x = 'y", "|- 'R('y) <=> 'Q('x)"),
        List()
      ),
      (
        "'P('x) |- 'P('x) \\/ 'R('y)",
        "'P('x); 'R('y) <=> 'Q('x) |- 'P('x) \\/ 'R('y)",
        List("|- 'x = 'y"),
        List("'R('y) <=> 'Q('x)")
      ),
      (
        "'P('x) |- 'P('x) \\/ 'R('y)",
        "'P('x); 'R('y) <=> 'Q('x) |- 'P('x) \\/ 'R('y)",
        List("|- 'x = 'y", "|- 'R('y) <=> 'Q('x)"),
        List()
      )
    )

    val incorrect = List(
      // (
      //     "sequent before substitution", "sequent after substitution",
      //     List("substSequent1", "|- p <=> q", ...), List("substFormula1", "p <=> q", "p = q",...)
      // ),
      (
        "'P('x); 'Q('z) |- 'P('x)",
        "'P('x); 'Q('z); 'x = 'y |- 'P('y)",
        List(),
        List("'z = 'y")
      ),
      (
        "'P('x) |- 'P('x)",
        "'P('x); 'x = 'y |- 'P('z)",
        List(),
        List("'x = 'y")
      ),
      (
        "'P('x); 'Q('z) |- 'P('x)",
        "'P('x); 'Q('z) |- 'P('y)",
        List("|- 'x = 'z"),
        List()
      ),
      (
        "'P('x); 'Q('y) |- 'P('x)",
        "'P('x); 'Q('y) |- 'P('z)",
        List("|- 'x = 'y"),
        List()
      ),
      (
        "'P('x) |- 'P('x) \\/ 'R('y)",
        "'P('x) |- 'P('z) \\/ 'Q('x)",
        List("|- 'x = 'y"),
        List("'R('y) <=> 'Q('x)")
      )
    )

    testTacticCases(using testProof)(correct, incorrect) { (stmt1, stmt2, premiseSequents, formSubsts) =>
      val prem = introduceSequent(using testProof)(stmt1)
      val substPrem: Seq[testProof.Fact | Formula | RunningTheory#Justification] = premiseSequents.map(introduceSequent(using testProof)(_))
      val substForm: Seq[testProof.Fact | Formula | RunningTheory#Justification] = formSubsts.map(parseFormula(_))
      val substJust: Seq[testProof.Fact | Formula | RunningTheory#Justification] = Nil
      Substitution
        .ApplyRules(using lisa.test.TestTheoryLibrary, testProof)(
          (substPrem ++ substForm ++ substJust).asInstanceOf[Seq[testProof.Fact | Formula | RunningTheory#Justification]]: _*
        )(prem)(lisa.utils.parsing.FOLParser.parseSequent(stmt2))
    }
  }

}
