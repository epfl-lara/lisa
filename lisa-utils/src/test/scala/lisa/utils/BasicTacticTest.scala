package lisa.utils

import lisa.kernel.proof.{SequentCalculus as SC}
import lisa.utils.Library
import lisa.utils.tactics.BasicStepTactic.*
import lisa.utils.tactics.ProofTacticLib
import org.scalatest.funsuite.AnyFunSuite

import scala.collection.immutable.LazyList

class BasicTacticTest extends AnyFunSuite with BasicMain {

    export lisa.test.TestTheoryLibrary.{_, given}

    // hypothesis
    test("Tactic Tests: Hypothesis") {
        val correct = List(
            "'P('x) |- 'P('x)", 
            "'P('x) |- 'P('x); 'Q('x)",
            "'P('x); 'Q('x) |- 'P('x); 'Q('x)",
            "'P('x); 'Q('x) |- 'P('x)"
        )

        val incorrect = List(
            "'P('x) |- ",
            " |- 'P('x)",
            " |- 'P('x); 'Q('x)",
            "'Q('x) |- "
        )

        val placeholderTheorem = makeTHM("'P('x) |- 'P('x)") {have("'P('x) |- 'P('x)") by Hypothesis}
        val emptyProof = new BaseProof(placeholderTheorem)

        given Proof = emptyProof

        for (stmt <- correct) {
            Hypothesis(stmt) match {
                case j: emptyProof.ValidProofTactic => true
                case j: emptyProof.InvalidProofTactic => fail("Correct step failed!")
                case _ => fail("Invalid result received from tactic!") 
            }
        }

        for (stmt <- incorrect) {
            Hypothesis(stmt) match {
                case j: emptyProof.ValidProofTactic => fail("Incorrect step passed!")
                case j: emptyProof.InvalidProofTactic => true
                case _ => fail("Invalid result received from tactic!") 
            }
        }
    }

    // rewrite
    // TODO: make this use equivalence checker tests
    test("Tactic Tests: Rewrite") {
        val correct = List(
            ("'P('x); 'Q('x) |- 'R('x)", "'P('x) /\\ 'Q('x) |- 'R('x)"),
            ("'P('x) |- 'R('x); 'Q('x)", "'P('x) |- 'R('x) \\/ 'Q('x)"),
        )

        val incorrect = List(
            ("'P('x); 'Q('x) |- 'R('x)", "'P('x) |- 'R('x)"),
            ("'P('x); 'Q('x) |- 'R('x)", "'P('x) \\/ 'Q('x) |- 'R('x)"),
            ("'P('x) |- 'R('x); 'Q('x)", "'P('x) |- 'R('x) /\\'Q('x) ")
        )

        val placeholderTheorem = makeTHM("'P('x) |- 'P('x)") {have("'P('x) |- 'P('x)") by Hypothesis}
        val emptyProof = new BaseProof(placeholderTheorem)

        // so much jank
        def introduceSequent(seq: String) = emptyProof.newProofStep(
            emptyProof.ValidProofTactic(
                Seq(SC.Hypothesis(FOLParser.parseSequent(seq), FOLParser.parseFormula("'P('x)"))), 
                Seq()
                )(using Hypothesis)
                )

        given Proof = emptyProof

        for ((stmt1, stmt2) <- correct) {
            val prem = introduceSequent(stmt1)
            Rewrite(using emptyProof)(prem)(stmt2) match {
                case j: emptyProof.ValidProofTactic => true
                case j: emptyProof.InvalidProofTactic => fail("Correct step failed!")
                case _ => fail("Invalid result received from tactic!") 
            }
        }

        for ((stmt1, stmt2) <- incorrect) {
            val prem = introduceSequent(stmt1)
            Rewrite(using emptyProof)(prem)(stmt2) match {
                case j: emptyProof.ValidProofTactic => fail("Incorrect step passed!")
                case j: emptyProof.InvalidProofTactic => true
                case _ => fail("Invalid result received from tactic!") 
            }
        }
    }

    // cut
    test("Tactic Tests: Cut - Parameter Inference") {
        val correct = List(
            ("'P('x) |- 'R('x)", "'R('x) |- 'Q('x)", "'P('x) |- 'Q('x)"),
            ("'P('x); 'R('x) |- 'R('x)", "'R('x) |- 'Q('x)", "'P('x); 'R('x) |- 'Q('x)"),
            // ("'P('x); 'R('x) |- 'R('x)", "'R('x) |- 'Q('x)", "'P('x) /\\ 'R('x) |- 'Q('x)"), // can't infer params out of conjunctions yet
            // ("'P('x) /\\ 'R('x) |- 'R('x)", "'R('x) |- 'Q('x)", "'P('x); 'R('x) |- 'Q('x)"),
            ("'P('x) /\\ 'R('x) |- 'R('x)", "'R('x) |- 'Q('x)", "'P('x) /\\ 'R('x) |- 'Q('x)"),
            ("'P('x); 'R('x) |- 'R('x)", "'R('x) |- 'Q('x); 'R('x)", "'P('x); 'R('x) |- 'Q('x); 'R('x)")
        )

        val incorrect = List(
            ("'P('x) |- 'R('x)", "'R('x) |- 'Q('x)", "'R('x) |- 'R('x)"),
            ("'P('x); 'R('x) |- 'R('x)", "'Q('x); 'R('x) |- 'Q('x)", "'P('x); 'R('x) |- 'Q('x)"),
            ("'P('x) |- 'R('x)", "'R('x); 'P('x) |- 'Q('x)", "'R('x) |- 'Q('x)")
        )

        val placeholderTheorem = makeTHM("'P('x) |- 'P('x)") {have("'P('x) |- 'P('x)") by Hypothesis}
        val emptyProof = new BaseProof(placeholderTheorem)

        def introduceSequent(seq: String) = emptyProof.newProofStep(
            emptyProof.ValidProofTactic(
                Seq(SC.Hypothesis(FOLParser.parseSequent(seq), FOLParser.parseFormula("'P('x)"))), 
                Seq()
                )(using Hypothesis)
                )

        given Proof = emptyProof

        for ((stmt1, stmt2, stmt3) <- correct) {
            val prem1 = introduceSequent(stmt1)
            val prem2 = introduceSequent(stmt2)
            Cut(using emptyProof)(prem1, prem2)(stmt3) match {
                case j: emptyProof.ValidProofTactic => true
                case j: emptyProof.InvalidProofTactic => fail("Correct step failed!")
                case _ => fail("Invalid result received from tactic!") 
            }
        }

        for ((stmt1, stmt2, stmt3) <- incorrect) {
            val prem1 = introduceSequent(stmt1)
            val prem2 = introduceSequent(stmt2)
            Cut(using emptyProof)(prem1, prem2)(stmt3) match {
                case j: emptyProof.ValidProofTactic => fail("Incorrect step passed!")
                case j: emptyProof.InvalidProofTactic => true
                case _ => fail("Invalid result received from tactic!") 
            }
        }
    }

    test("Tactic Tests: Cut - Explicit Parameters") {
        val correct = List(
            ("'P('x) |- 'R('x)", "'R('x) |- 'Q('x)", "'P('x) |- 'Q('x)", "'R('x)"),
            ("'P('x); 'R('x) |- 'R('x)", "'R('x) |- 'Q('x)", "'P('x); 'R('x) |- 'Q('x)", "'R('x)"),
            ("'P('x) /\\ 'R('x) |- 'R('x)", "'R('x) |- 'Q('x)", "'P('x) /\\ 'R('x) |- 'Q('x)", "'R('x)"),
            ("'P('x); 'R('x) |- 'R('x)", "'R('x) |- 'Q('x); 'R('x)", "'P('x); 'R('x) |- 'Q('x); 'R('x)", "'R('x)")
        )

        val incorrect = List(
            ("'P('x) |- 'R('x)", "'R('x) |- 'Q('x)", "'R('x) |- 'R('x)", "'R('x)"),
            ("'P('x); 'R('x) |- 'R('x)", "'Q('x); 'R('x) |- 'Q('x)", "'P('x); 'R('x) |- 'Q('x)", "'R('x)"),
            ("'P('x) |- 'R('x)", "'R('x) |- 'Q('x)", "'P('x) |- 'Q('x)", "'P('x)"),
            ("'P('x); 'R('x) |- 'R('x)", "'R('x) |- 'Q('x)", "'P('x); 'R('x) |- 'Q('x)", "'R('x) /\\ 'P('x)"),
            ("'P('x) |- 'R('x)", "'R('x); 'P('x) |- 'Q('x)", "'R('x) |- 'Q('x)", "'R('x)")
        )

        val placeholderTheorem = makeTHM("'P('x) |- 'P('x)") {have("'P('x) |- 'P('x)") by Hypothesis}
        val emptyProof = new BaseProof(placeholderTheorem)

        def introduceSequent(seq: String) = emptyProof.newProofStep(
            emptyProof.ValidProofTactic(
                Seq(SC.Hypothesis(FOLParser.parseSequent(seq), FOLParser.parseFormula("'P('x)"))), 
                Seq()
                )(using Hypothesis)
                )

        given Proof = emptyProof

        for ((stmt1, stmt2, stmt3, form) <- correct) {
            val prem1 = introduceSequent(stmt1)
            val prem2 = introduceSequent(stmt2)
            Cut.withParameters(using emptyProof)(FOLParser.parseFormula(form))(prem1, prem2)(stmt3) match {
                case j: emptyProof.ValidProofTactic => true
                case j: emptyProof.InvalidProofTactic => fail("Correct step failed!")
                case _ => fail("Invalid result received from tactic!") 
            }
        }

        for ((stmt1, stmt2, stmt3, form) <- incorrect) {
            val prem1 = introduceSequent(stmt1)
            val prem2 = introduceSequent(stmt2)
            Cut.withParameters(using emptyProof)(FOLParser.parseFormula(form))(prem1, prem2)(stmt3) match {
                case j: emptyProof.ValidProofTactic => fail("Incorrect step passed!")
                case j: emptyProof.InvalidProofTactic => true
                case _ => fail("Invalid result received from tactic!") 
            }
        }
    }

    // left rules

    //     left and
    test("Tactic Tests: Left And - Parameter Inference") {
        val correct = List(
            ("'P('x); 'Q('x) |- 'R('x)", "'P('x); 'Q('x) /\\ 'S('x) |- 'R('x)"),
            ("'P('x); 'Q('x); 'S('x) |- 'R('x)", "'P('x); 'Q('x) /\\ 'S('x) |- 'R('x)"),
            ("'P('x); 'Q('x); 'S('x) |- 'R('x)", "'P('x); 'Q('x); 'S('x) |- 'R('x)"),
            ("'P('x); 'Q('x); 'S('x) /\\ 'A('x) |- 'R('x)", "'P('x); 'Q('x) /\\ ('S('x) /\\ 'A('x)) |- 'R('x)"),
        )

        val incorrect = List(
            ("'P('x); 'Q('x) |- 'R('x)", "'P('x); 'Q('x) \\/ 'S('x) |- 'R('x)"),
            ("'P('x); 'Q('x); 'S('x) |- 'R('x)", "'P('x); 'Q('x) \\/ 'S('x) |- 'R('x)"),
            ("'P('x); 'Q('x); 'S('x) |- 'R('x)", "'P('x); 'Q('x) /\\ 'P('x) |- 'R('x)"),
            ("'P('x); 'Q('x); 'S('x); 'A('x) |- 'R('x)", "'P('x); 'Q('x) /\\ 'S('x) /\\ 'A('x) |- 'R('x)"),
            ("'P('x); 'Q('x); 'S('x) |- 'R('x)", "'P('x); 'Q('x) |- 'R('x)"),
        )

        val placeholderTheorem = makeTHM("'P('x) |- 'P('x)") {have("'P('x) |- 'P('x)") by Hypothesis}
        val emptyProof = new BaseProof(placeholderTheorem)

        def introduceSequent(seq: String) = emptyProof.newProofStep(
            emptyProof.ValidProofTactic(
                Seq(SC.Hypothesis(FOLParser.parseSequent(seq), FOLParser.parseFormula("'P('x)"))), 
                Seq()
                )(using Hypothesis)
                )

        given Proof = emptyProof

        for ((stmt1, stmt2) <- correct) {
            val prem = introduceSequent(stmt1)
            LeftAnd(using emptyProof)(prem)(stmt2) match {
                case j: emptyProof.ValidProofTactic => true
                case j: emptyProof.InvalidProofTactic => fail("Correct step failed!")
                case _ => fail("Invalid result received from tactic!") 
            }
        }

        for ((stmt1, stmt2) <- incorrect) {
            val prem = introduceSequent(stmt1)
            LeftAnd(using emptyProof)(prem)(stmt2) match {
                case j: emptyProof.ValidProofTactic => fail("Incorrect step passed!")
                case j: emptyProof.InvalidProofTactic => true
                case _ => fail("Invalid result received from tactic!") 
            }
        }
    }

    test("Tactic Tests: Left And - Explicit Parameters") {
        val correct = List(
            ("'P('x); 'Q('x) |- 'R('x)", "'P('x); 'Q('x) /\\ 'S('x) |- 'R('x)", "'Q('x)", "'S('x)"),
            ("'P('x); 'Q('x); 'S('x) |- 'R('x)", "'P('x); 'Q('x) /\\ 'S('x) |- 'R('x)", "'Q('x)", "'S('x)"),
            ("'P('x); 'Q('x); 'S('x) /\\ 'A('x) |- 'R('x)", "'P('x); 'Q('x) /\\ ('S('x) /\\ 'A('x)) |- 'R('x)", "'Q('x)", "'S('x) /\\ 'A('x)"),
        )

        val incorrect = List(
            ("'P('x); 'Q('x) |- 'R('x)", "'P('x); 'Q('x) \\/ 'S('x) |- 'R('x)", "'Q('x)", "'S('x)"),
            ("'P('x); 'Q('x); 'S('x) |- 'R('x)", "'P('x); 'Q('x) \\/ 'S('x) |- 'R('x)", "'Q('x)", "'S('x)"),
            ("'P('x); 'Q('x); 'S('x) |- 'R('x)", "'P('x); 'Q('x) /\\ 'P('x) |- 'R('x)", "'Q('x)", "'S('x)"),
            ("'P('x); 'Q('x); 'S('x); 'A('x) |- 'R('x)", "'P('x); 'Q('x) /\\ 'S('x) /\\ 'A('x) |- 'R('x)", "'Q('x)", "'S('x) /\\ 'A('x)"),
            ("'P('x); 'Q('x); 'S('x) |- 'R('x)", "'P('x); 'Q('x) |- 'R('x)", "'Q('x)", "'S('x)"),
            ("'P('x); 'Q('x) |- 'R('x)", "'P('x); 'Q('x) /\\ 'S('x) |- 'R('x)", "'Q('x)", "'P('x)"),
            ("'P('x); 'Q('x); 'S('x) |- 'R('x)", "'P('x); 'Q('x) /\\ 'S('x) |- 'R('x)", "'P('x)", "'S('x)"),
            ("'P('x); 'Q('x); 'S('x) /\\ 'A('x) |- 'R('x)", "'P('x); 'Q('x) /\\ ('S('x) /\\ 'A('x)) |- 'R('x)", "'Q('x)", "'S('x)"),
        )

        val placeholderTheorem = makeTHM("'P('x) |- 'P('x)") {have("'P('x) |- 'P('x)") by Hypothesis}
        val emptyProof = new BaseProof(placeholderTheorem)

        def introduceSequent(seq: String) = emptyProof.newProofStep(
            emptyProof.ValidProofTactic(
                Seq(SC.Hypothesis(FOLParser.parseSequent(seq), FOLParser.parseFormula("'P('x)"))), 
                Seq()
                )(using Hypothesis)
                )

        given Proof = emptyProof

        for ((stmt1, stmt2, phi, psi) <- correct) {
            val prem = introduceSequent(stmt1)
            LeftAnd.withParameters(using emptyProof)(FOLParser.parseFormula(phi), FOLParser.parseFormula(psi))(prem)(stmt2) match {
                case j: emptyProof.ValidProofTactic => true
                case j: emptyProof.InvalidProofTactic => fail("Correct step failed!")
                case _ => fail("Invalid result received from tactic!") 
            }
        }

        for ((stmt1, stmt2, phi, psi) <- incorrect) {
            val prem = introduceSequent(stmt1)
            LeftAnd.withParameters(using emptyProof)(FOLParser.parseFormula(phi), FOLParser.parseFormula(psi))(prem)(stmt2) match {
                case j: emptyProof.ValidProofTactic => fail("Incorrect step passed!")
                case j: emptyProof.InvalidProofTactic => true
                case _ => fail("Invalid result received from tactic!") 
            }
        }
    }

    //     left or
    test("Tactic Tests: Left Or - Parameter Inference") {
        val correct = List(
            (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"),  "'P('x) \\/ 'R('x) |- 'Q('x); 'S('x)"),
            (List("'W('x); 'P('x) |- 'S('x)", "'R('x); 'O('x) |- 'Q('x); 'T('x)"),  "'P('x) \\/ 'R('x); 'O('x); 'W('x) |- 'Q('x); 'S('x); 'T('x)"),
            (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"),  "'P('x) \\/ 'R('x); 'P('x) |- 'Q('x); 'S('x)"),
            (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"),  "'E('x) \\/ 'T('x); 'P('x) |- 'Q('x); 'S('x)"),
            (List("'P('x) |- 'S('x)"),  "'P('x) |- 'S('x)"),
        )

        val incorrect = List(
            (List(),  "'P('x) |- 'S('x)"),
            (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"),  "'P('x) \\/ 'R('x) |- 'T('x); 'S('x)"),
            (List("'P('x) |- 'R('x)", "'R('x) |- 'Q('x)", "'R('x) |- 'R('x)")),
            (List("'P('x); 'T('x) |- 'R('x)", "'R('x) |- 'Q('x)", "'R('x) |- 'R('x)")),
            (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"),  "'P('x) \\/ 'R('x); 'T('x) |- 'Q('x); 'S('x)"),
        )

        val placeholderTheorem = makeTHM("'P('x) |- 'P('x)") {have("'P('x) |- 'P('x)") by Hypothesis}
        val emptyProof = new BaseProof(placeholderTheorem)

        def introduceSequent(seq: String) = emptyProof.newProofStep(
            emptyProof.ValidProofTactic(
                Seq(SC.Hypothesis(FOLParser.parseSequent(seq), FOLParser.parseFormula("'P('x)"))), 
                Seq()
                )(using Hypothesis)
                )

        given Proof = emptyProof

        for ((stmts: List[String], stmt2: String) <- correct) {
            val prems = stmts.map(introduceSequent(_))
            LeftOr(using emptyProof)(prems: _*)(stmt2) match {
                case j: emptyProof.ValidProofTactic => true
                case j: emptyProof.InvalidProofTactic => fail("Correct step failed!")
                case _ => fail("Invalid result received from tactic!") 
            }
        }

        for ((stmts: List[String], stmt2: String) <- incorrect) {
            val prems = stmts.map(introduceSequent(_))
            LeftOr(using emptyProof)(prems: _*)(stmt2) match {
                case j: emptyProof.ValidProofTactic => fail("Incorrect step passed!")
                case j: emptyProof.InvalidProofTactic => true
                case _ => fail("Invalid result received from tactic!") 
            }
        }
    }

    test("Tactic Tests: Left Or - Explicit Parameters") {
        val correct = List(
            (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"),  "'P('x) \\/ 'R('x) |- 'Q('x); 'S('x)", List("'P('x)", "'R('x)")),
            (List("'W('x); 'P('x) |- 'S('x)", "'R('x); 'O('x) |- 'Q('x); 'T('x)"),  "'P('x) \\/ 'R('x); 'O('x); 'W('x) |- 'Q('x); 'S('x); 'T('x)", List("'P('x)", "'R('x)")),
            (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"),  "'P('x) \\/ 'R('x); 'P('x) |- 'Q('x); 'S('x)", List("'P('x)", "'R('x)")),
            (List("'P('x) |- 'S('x)"),  "'P('x) |- 'S('x)", List("'P('x)")),
        )

        val incorrect = List(
            (List(),  "'P('x) |- 'S('x)", List()),
            (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"),  "'P('x) \\/ 'R('x) |- 'Q('x); 'S('x)", List("'P('x)", "'Q('x)")),
            (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"),  "'P('x) \\/ 'R('x) |- 'Q('x); 'S('x)", List("'P('x)")),
            (List("'P('x) |- 'S('x)", "'R('x); 'O('x) |- 'Q('x); 'T('x)"),  "'P('x) \\/ 'R('x); 'O('x); 'W('x) |- 'Q('x); 'S('x); 'T('x)", List("'P('x)", "'R('x)")),
            (List("'W('x); 'P('x) |- 'S('x)", "'R('x); 'O('x) |- 'Q('x); 'T('x)"),  "'P('x) \\/ 'R('x); 'O('x) |- 'Q('x); 'S('x); 'T('x)", List("'P('x)", "'R('x)")),
            (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"),  "'P('x) \\/ 'R('x); 'P('x) |- 'Q('x); 'S('x)", List("'E('x)", "'R('x)")),
            (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"),  "'E('x) \\/ 'T('x) |- 'Q('x); 'S('x)", List("'E('x)", "'T('x)")),
        )

        val placeholderTheorem = makeTHM("'P('x) |- 'P('x)") {have("'P('x) |- 'P('x)") by Hypothesis}
        val emptyProof = new BaseProof(placeholderTheorem)

        def introduceSequent(seq: String) = emptyProof.newProofStep(
            emptyProof.ValidProofTactic(
                Seq(SC.Hypothesis(FOLParser.parseSequent(seq), FOLParser.parseFormula("'P('x)"))), 
                Seq()
                )(using Hypothesis)
                )

        given Proof = emptyProof

        for ((stmts, stmt2, forms) <- correct) {
            val prems = stmts.map(introduceSequent(_))
            LeftOr.withParameters(using emptyProof)(forms.map(FOLParser.parseFormula(_)): _*)(prems: _*)(stmt2) match {
                case j: emptyProof.ValidProofTactic => true
                case j: emptyProof.InvalidProofTactic => {showCurrentProof(); fail("Correct step failed!")}
                case _ => fail("Invalid result received from tactic!") 
            }
        }

        for ((stmts, stmt2, forms) <- incorrect) {
            val prems = stmts.map(introduceSequent(_))
            LeftOr.withParameters(using emptyProof)(forms.map(FOLParser.parseFormula(_)): _*)(prems: _*)(stmt2) match {
                case j: emptyProof.ValidProofTactic => fail("Incorrect step passed!")
                case j: emptyProof.InvalidProofTactic => true
                case _ => fail("Invalid result received from tactic!") 
            }
        }
    }

    //     left implies
    //     left iff
    //     left not
    //     left forall
    //     left exists
    //     left existsone

    // right rules
    //     right and 
    //     right or
    //     right implies
    //     right iff
    //     right not 
    //     right forall 
    //     right exists
    //     right existsone

    // left refl
    // right refl

    // left substeq
    // right substeq

    // left substiff
    // right substiff

    // instfunschema
    // instpredschema 

    // subproof  
}
