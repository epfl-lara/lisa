package lisa.utils

import lisa.kernel.proof.{SequentCalculus as SC}
import lisa.utils.Library
import lisa.utils.Printer
import lisa.utils.ProofTacticTestLib
import lisa.utils.tactics.BasicStepTactic.*
import lisa.utils.tactics.ProofTacticLib
import org.scalatest.funsuite.AnyFunSuite

class BasicTacticTest extends ProofTacticTestLib {

    // hypothesis
    test("Tactic Tests: Hypothesis") {
        val correct = List(
            ("'P('x) |- 'P('x)"), 
            ("'P('x) |- 'P('x); 'Q('x)"),
            ("'P('x); 'Q('x) |- 'P('x); 'Q('x)"),
            ("'P('x); 'Q('x) |- 'P('x)"),
        )

        val incorrect = List(
            ("'P('x) |- "),
            (" |- 'P('x)"),
            (" |- 'P('x); 'Q('x)"),
            ("'Q('x) |- "),
        )

        val testProof = generateTestProof()

        testTacticCases(correct, incorrect){
            Hypothesis(_)
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

        val testProof = generateTestProof()

        testTacticCases(correct, incorrect){ (stmt1, stmt2) =>
            val prem = introduceSequent(stmt1)
            Rewrite(prem)(stmt2)
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

        val testProof = generateTestProof()

        testTacticCases(correct, incorrect){ (stmt1, stmt2, stmt3) =>
            val prem1 = introduceSequent(stmt1)
            val prem2 = introduceSequent(stmt2)
            Cut(prem1, prem2)(stmt3)
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

        testTacticCases(correct, incorrect){ (stmt1, stmt2, stmt3, form) =>
            val prem1 = introduceSequent(stmt1)
            val prem2 = introduceSequent(stmt2)
            Cut.withParameters(FOLParser.parseFormula(form))(prem1, prem2)(stmt3)
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

        testTacticCases(correct, incorrect){ (stmt1, stmt2) =>
            val prem = introduceSequent(stmt1)
            LeftAnd(prem)(stmt2)
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

        testTacticCases(correct, incorrect){ (stmt1, stmt2, phi, psi) =>
            val prem = introduceSequent(stmt1)
            LeftAnd.withParameters(FOLParser.parseFormula(phi), FOLParser.parseFormula(psi))(prem)(stmt2)
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
            (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"),  "'P('x) \\/ 'R('x); 'T('x) |- 'Q('x); 'S('x)"),
        )

        testTacticCases(correct, incorrect){ (stmts, stmt2) =>
            val prems = stmts.map(introduceSequent(_))
            LeftOr(prems: _*)(stmt2)
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

        testTacticCases(correct, incorrect){ (stmts, stmt2, forms) =>
            val prems = stmts.map(introduceSequent(_))
            LeftOr.withParameters(forms.map(FOLParser.parseFormula(_)): _*)(prems: _*)(stmt2)
        }
    }

    //     left implies

    test("Tactic Tests: Left Implies - Parameter Inference") {
        val correct = List(
            ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); 'R('x) ==> 'S('x) |- 'Q('x)"),
            ("'P('x) |- 'R('x); 'Q('x)", "'S('x) |- 'Q('x)", "'P('x); 'R('x) ==> 'S('x) |- 'Q('x)"),
            ("'P('x) |- 'R('x); 'Q('x)", "'S('x) |- 'Q('x)", "'P('x); 'R('x) ==> 'P('x) |- 'Q('x); 'R('x)"),
            ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); 'R('x) ==> 'S('x); 'S('x) |- 'Q('x)"),
            ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); 'R('x) ==> 'P('x); 'S('x) |- 'Q('x); 'T('x)"),
            ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); (!'R('x)) \\/ 'S('x) |- 'Q('x)"),
            ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); !'R('x) \\/ 'S('x) |- 'Q('x)"),
        )

        val incorrect = List(
            ("'P('x) |- 'R('x)", "'S('x) |- 'T('x)", "'P('x); 'R('x) ==> 'S('x) |- 'Q('x)"),
            ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); 'R('x) ==> 'T('x) |- 'Q('x)"),
            ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); 'T('x) ==> 'S('x) |- 'Q('x)"),
            ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); 'R('x) ==> 'S('x) |- 'T('x)"),
            ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); 'R('x) \\/ 'S('x) |- 'Q('x)"),
            ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); 'R('x) /\\ 'S('x) |- 'Q('x)"),
            ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x) |- 'Q('x)"),
        )

        testTacticCases(correct, incorrect){ (stmt1, stmt2, stmt3) =>
            val prem1 = introduceSequent(stmt1)
            val prem2 = introduceSequent(stmt2)
            LeftImplies(prem1, prem2)(stmt3)
        }
    }

    test("Tactic Tests: Left Implies - Explicit Parameters") {
        val correct = List(
            ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); 'R('x) ==> 'S('x) |- 'Q('x)", "'R('x)", "'S('x)"),
            ("'P('x) |- 'R('x); 'Q('x)", "'S('x) |- 'Q('x)", "'P('x); 'R('x) ==> 'S('x) |- 'Q('x)", "'R('x)", "'S('x)"),
            ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); 'R('x) ==> 'S('x); 'S('x) |- 'Q('x)", "'R('x)", "'S('x)"),
            ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); (!'R('x)) \\/ 'S('x) |- 'Q('x)", "'R('x)", "'S('x)"),
            ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); !'R('x) \\/ 'S('x) |- 'Q('x)", "'R('x)", "'S('x)"),
        )

        val incorrect = List(
            ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); 'R('x) ==> 'S('x) |- 'Q('x)", "'R('x)", "'P('x)"),
            ("'P('x) |- 'R('x); 'Q('x)", "'S('x) |- 'Q('x)", "'P('x); 'R('x) ==> 'S('x) |- 'Q('x)", "'P('x)", "'Q('x)"),
            ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); 'R('x) ==> 'S('x); 'S('x) |- 'Q('x)", "'P('x)", "'S('x)"),
            ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); (!'R('x)) \\/ 'S('x) |- 'Q('x)", "'P('x)", "'S('x)"),
            ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); !'R('x) \\/ 'S('x) |- 'Q('x)", "'P('x)", "'S('x)"),
            ("'P('x) |- 'R('x)", "'S('x) |- 'T('x)", "'P('x); 'R('x) ==> 'S('x) |- 'Q('x)", "'R('x)", "'S('x)"),
            ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); 'R('x) ==> 'T('x) |- 'Q('x)", "'R('x)", "'S('x)"),
            ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); 'T('x) ==> 'S('x) |- 'Q('x)", "'R('x)", "'S('x)"),
            ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); 'R('x) ==> 'S('x) |- 'T('x)", "'R('x)", "'S('x)"),
            ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); 'R('x) \\/ 'S('x) |- 'Q('x)", "'R('x)", "'S('x)"),
            ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); 'R('x) /\\ 'S('x) |- 'Q('x)", "'R('x)", "'S('x)"),
            ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x) |- 'Q('x)", "'R('x)", "'S('x)"),
        )

        testTacticCases(correct, incorrect){ (stmt1, stmt2, stmt3, form1, form2) =>
            val prem1 = introduceSequent(stmt1)
            val prem2 = introduceSequent(stmt2)
            LeftImplies.withParameters(FOLParser.parseFormula(form1), FOLParser.parseFormula(form2))(prem1, prem2)(stmt3)
        }
    }

    //     left iff
    test("Tactic Tests: Left Iff - Parameter Inference") {
        val correct = List(
            ("'P('x); 'Q('x) ==> 'S('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'S('x) |- 'R('x)"),
            ("'P('x); 'Q('x) ==> 'S('x); 'S('x) ==> 'Q('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'S('x) |- 'R('x)"),
            ("'P('x); 'Q('x) ==> 'S('x); 'Q('x) <=> 'S('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'S('x) |- 'R('x)"),
        )

        val incorrect = List(
            // TODO: FIX AND UNCOMMENT THESE TESTS
            ("'P('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'R('x)"),
            ("'P('x); !'Q('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'R('x)"),
            ("'P('x); 'Q('x) ==> 'S('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'S('x) |- 'R('x); 'P('x)"),
            ("'P('x); 'Q('x) ==> 'S('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'T('x) |- 'R('x)"),
        )

        testTacticCases(correct, incorrect){ (stmt1, stmt2) =>
            val prem = introduceSequent(stmt1)
            LeftIff(prem)(stmt2)
        }
    }

    test("Tactic Tests: Left Iff - Explicit Parameters") {
        val correct = List(
            ("'P('x); 'Q('x) ==> 'S('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'S('x) |- 'R('x)", "'Q('x)", "'S('x)"),
            ("'P('x); 'Q('x) ==> 'S('x); 'S('x) ==> 'Q('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'S('x) |- 'R('x)", "'Q('x)", "'S('x)"),
            ("'P('x); 'Q('x) ==> 'S('x); 'Q('x) <=> 'S('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'S('x) |- 'R('x)", "'Q('x)", "'S('x)"),
        )

        val incorrect = List(
            ("'P('x); 'Q('x) ==> 'S('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'S('x) |- 'R('x)", "'Q('x)", "'P('x)"),
            ("'P('x); 'Q('x) ==> 'S('x); 'S('x) ==> 'Q('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'S('x) |- 'R('x)", "'P('x)", "'S('x)"),
            ("'P('x); 'Q('x) ==> 'S('x); 'Q('x) <=> 'S('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'S('x) |- 'R('x)", "'P('x)", "'R('x)"),
            ("'P('x); 'Q('x) ==> 'S('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'S('x) |- 'R('x); 'P('x)", "'Q('x)", "'S('x)"),
            ("'P('x); 'Q('x) ==> 'S('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'T('x) |- 'R('x)", "'Q('x)", "'S('x)"),
            ("'P('x); 'Q('x) ==> 'S('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'T('x) |- 'R('x)", "'Q('x)", "'T('x)"),
        )

        testTacticCases(correct, incorrect){ (stmt1, stmt2, form1, form2) =>
            val prem = introduceSequent(stmt1)
            LeftIff.withParameters(FOLParser.parseFormula(form1), FOLParser.parseFormula(form2))(prem)(stmt2)
        }
    }

    //     left not
    test("Tactic Tests: Left Not - Parameter Inference") {
        val correct = List(
            ("'P('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'R('x)"),
            ("'P('x); !'Q('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'R('x)"),
            ("'P('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'Q('x); 'R('x)"),
            ("'P('x); !'Q('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'R('x)"),
        )

        val incorrect = List(
            // TODO: FIX AND UNCOMMENT THESE TESTS
            ("'P('x); 'Q('x) ==> 'S('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'S('x) |- 'R('x); 'P('x)"),
            ("'P('x); 'Q('x) ==> 'S('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'T('x) |- 'R('x)"),
            ("'P('x) |- 'Q('x); 'R('x)", "'P('x); 'Q('x) |- 'R('x)"),
            ("'P('x) |- 'Q('x); 'R('x)", "'P('x) |- 'R('x); !'Q('x)"),
            // TODO: should this be allowed::
            ("'P('x) |- 'Q('x); 'R('x)", "'P('x) |- 'R('x); 'Q('x)"),
            ("'P('x) |- 'Q('x); 'R('x)", "'P('x) |- 'R('x)"),
        )

        testTacticCases(correct, incorrect){ (stmt1, stmt2) =>
            val prem = introduceSequent(stmt1)
            LeftNot(prem)(stmt2)
        }
    }

    test("Tactic Tests: Left Not - Explicit Parameters") {
        val correct = List(
            ("'P('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'R('x)", "'Q('x)"),
            ("'P('x); !'Q('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'R('x)", "'Q('x)"),
            ("'P('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'Q('x); 'R('x)", "'Q('x)"),
            ("'P('x); !'Q('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'R('x)", "'Q('x)"),
        )

        val incorrect = List(
            ("'P('x) |- 'Q('x); 'R('x)", "'P('x); 'Q('x) |- 'R('x)", "'Q('x)"),
            ("'P('x) |- 'Q('x); 'R('x)", "'P('x) |- 'R('x); !'Q('x)", "'Q('x)"),
            ("'P('x) |- 'Q('x); 'R('x)", "'P('x) |- 'R('x)", "'Q('x)"),
            ("'P('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'R('x)", "'P('x)"),
            ("'P('x); !'Q('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'R('x)", "'R('x)"),
            ("'P('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'Q('x); 'R('x)", "'P('x)"),
            ("'P('x); !'Q('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'R('x)", "'R('x)"),
        )

        testTacticCases(correct, incorrect){ (stmt1, stmt2, form) =>
            val prem = introduceSequent(stmt1)
            LeftNot.withParameters(FOLParser.parseFormula(form))(prem)(stmt2)
        }
    }

    //     left forall
    test("Tactic Tests: Left Forall - Parameter Inference") {
        val correct = List(
            ("'P('x) |- 'R('x)", "∀x. 'P('x) |- 'R('x)", "'x"),
            ("'P('x) |- 'R('x)", "∀y. 'P('y) |- 'R('x)", "'x"),
            ("'P('x) |- 'R('x)", "∀y. 'P('x) |- 'R('x)", "'x"),
            ("'A('x, 'x) |- 'R('x)", "∀y. 'A('y, 'x) |- 'R('x)", "'x"),
            ("'P('x); 'Q('x) |- 'R('x)", "∀x. 'P('x); 'Q('x) |- 'R('x)", "'x"),
            ("'P('x) /\\ 'Q('x) |- 'R('x)", "∀x. ('P('x) /\\ 'Q('x))|- 'R('x)", "'x"),
            ("'P('f('g('x, 'y), 'z, 'h, 'j)) |- 'R('f('g('x, 'x), 'j, 'z, 'h))", "∀x. 'P('x)|- 'R('f('g('x, 'x), 'j, 'z, 'h))", "'f('g('x, 'y), 'z, 'h, 'j)"),
        )

        val incorrect = List(
            ("'P('x) |- 'R('x)", "∀x. 'Q('x) |- 'R('x)", "'x"),
            ("'P('x) |- 'R('x)", "∀y. 'P('y) |- 'R('y)", "'x"),
            ("'P('x) |- 'R('x)", "∀x. 'Q('x) |- 'R('x)", "'y"),
            // TODO: should this be allowed?
            ("'P('x) |- 'R('x)", "'P('x) |- 'R('x)", "'x"),
            ("'P('x); 'Q('x) |- 'R('x)", "∀y. 'P('x); 'Q('y) |- 'R('x)", "'x"),
            ("'P('f('g('x, 'y), 'z, 'h, 'j)) |- 'R('f('g('x, 'x), 'j, 'z, 'h))", "∀x. 'P('x)|- 'R('f('g('x, 'x), 'j, 'z, 'h))", "'f('g('x, 'x), 'j, 'z, 'h)"),
        )

        testTacticCases(correct, incorrect){ (stmt1, stmt2, term) =>
            val prem = introduceSequent(stmt1)
            LeftForall(FOLParser.parseTerm(term))(prem)(stmt2)
        }
    }

    test("Tactic Tests: Left Forall - Explicit Parameters") {
        val correct = List(
            ("'P('x) |- 'R('x)", "∀x. 'P('x) |- 'R('x)", "'P('x)", "x", "'x"),
            ("'P('x) |- 'R('x)", "∀y. 'P('y) |- 'R('x)", "'P('y)", "y", "'x"),
            ("'P('x) |- 'R('x)", "∀y. 'P('x) |- 'R('x)", "'P('x)", "y", "'x"),
            ("'A('x, 'x) |- 'R('x)", "∀y. 'A('y, 'x) |- 'R('x)", "'A('y, 'x)", "y", "'x"),
            ("'P('x); 'Q('x) |- 'R('x)", "∀x. 'P('x); 'Q('x) |- 'R('x)", "'P('x)", "x", "'x"),
            ("'P('x) /\\ 'Q('x) |- 'R('x)", "∀x. ('P('x) /\\ 'Q('x))|- 'R('x)", "('P('x) /\\ 'Q('x))", "x", "'x"),
            ("'P('f('g('x, 'y), 'z, 'h, 'j)) |- 'R('f('g('x, 'x), 'j, 'z, 'h))", "∀x. 'P('x)|- 'R('f('g('x, 'x), 'j, 'z, 'h))", "'P('x)", "x", "'f('g('x, 'y), 'z, 'h, 'j)"),
        )

        val incorrect = List(
            ("'P('x) |- 'R('x)", "∀x. 'Q('x) |- 'R('x)", "'P('x)", "x", "'x"),
            ("'P('x) |- 'R('x)", "∀y. 'P('y) |- 'R('y)", "'P('x)", "y", "'x"),
            ("'P('x) |- 'R('x)", "∀x. 'Q('x) |- 'R('x)", "'Q('x)", "x", "'x"),
            ("'P('x) |- 'R('x)", "'P('x) |- 'R('x)", "'P('x)", "x", "'x"),
            ("'P('x); 'Q('x) |- 'R('x)", "∀y. 'P('x); 'Q('y) |- 'R('x)", "'P('x)", "y", "'x"),
            ("'P('f('g('x, 'y), 'z, 'h, 'j)) |- 'R('f('g('x, 'x), 'j, 'z, 'h))", "∀x. 'P('x)|- 'R('f('g('x, 'x), 'j, 'z, 'h))", "'P('x)", "x", "'f('g('x, 'x), 'j, 'z, 'h)"),
        )

        testTacticCases(correct, incorrect){ (stmt1, stmt2, form, variable, term) =>
            val prem = introduceSequent(stmt1)
            LeftForall.withParameters(FOLParser.parseFormula(form), variable, FOLParser.parseTerm(term))(prem)(stmt2)
        }
    }

    //     left exists
    test("Tactic Tests: Left Exists - Parameter Inference") {
        val correct = List(
            ("'P('x) |- 'R('y)", "∃x. 'P('x) |- 'R('y)"),
            ("'A('y, 'x) |- 'R('x)", "∃y. 'A('y, 'x) |- 'R('x)"),
            ("'P('z); 'Q('x) |- 'R('x)", "∃z. 'P('z); 'Q('x) |- 'R('x)"),
            ("'P('x) /\\ 'Q('x) |- 'R('y)", "∃x. ('P('x) /\\ 'Q('x))|- 'R('y)"),
            ("'P('f('g('x, 'y), 'z, 'h, 'j)) |- 'R('f('g('x, 'x), 'e, 'z, 'h))", "∃j. 'P('f('g('x, 'y), 'z, 'h, 'j))|- 'R('f('g('x, 'x), 'e, 'z, 'h))"),
        )

        val incorrect = List(
            // TODO: FIX or kernel error
            ("'P('x) |- 'R('y); 'Q('z)", "'P('x) |- 'R('y)"),
            ("'P('x) |- 'R('y)", "∃y. 'P('x) |- 'R('y)"),
            // TODO: should we allow this? ::
            ("'P('x) |- 'R('y)", "'P('x) |- 'R('y)"),
            ("'P('x) |- 'R('x)", "∃x. 'P('x) |- 'R('x)"),
            ("'A('y, 'x) |- 'R('x)", "∃x. 'A('y, 'x) |- 'R('x)"),
            ("'P('x); 'Q('x) |- 'R('x)", "∃z. 'P('z); 'Q('x) |- 'R('x)"),
            ("'P('x) /\\ 'Q('x) |- 'R('y)", "∃x. ('P('x) /\\ 'Q('y))|- 'R('y)"),
            ("'P('f('g('x, 'y), 'z, 'h, 'j)) |- 'R('f('g('x, 'x), 'j, 'z, 'h))", "∃j. 'P('f('g('x, 'y), 'z, 'h, 'j))|- 'R('f('g('x, 'x), 'e, 'j, 'h))"),
        )

        testTacticCases(correct, incorrect){ (stmt1, stmt2) =>
            val prem = introduceSequent(stmt1)
            LeftExists(prem)(stmt2)
        }
    }

    test("Tactic Tests: Left Exists - Explicit Parameters") {
        val correct = List(
            ("'P('x) |- 'R('y)", "∃x. 'P('x) |- 'R('y)", "'P('x)", "x"),
            ("'A('y, 'x) |- 'R('x)", "∃y. 'A('y, 'x) |- 'R('x)", "'A('y, 'x)", "y"),
            ("'P('z); 'Q('x) |- 'R('x)", "∃z. 'P('z); 'Q('x) |- 'R('x)", "'P('z)", "z"),
            ("'P('x) /\\ 'Q('x) |- 'R('y)", "∃x. ('P('x) /\\ 'Q('x))|- 'R('y)", "('P('x) /\\ 'Q('x))", "x"),
            ("'P('f('g('x, 'y), 'z, 'h, 'j)) |- 'R('f('g('x, 'x), 'e, 'z, 'h))", "∃j. 'P('f('g('x, 'y), 'z, 'h, 'j))|- 'R('f('g('x, 'x), 'e, 'z, 'h))", "'P('f('g('x, 'y), 'z, 'h, 'j))", "j"),
        )

        val incorrect = List(
            ("'P('x) |- 'R('y)", "∃x. 'P('x) |- 'R('y)", "'P('y)", "x"),
            ("'A('y, 'x) |- 'R('x)", "∃y. 'A('y, 'x) |- 'R('x)", "'A('y, 'y)", "y"),
            ("'P('z); 'Q('x) |- 'R('x)", "∃z. 'P('z); 'Q('x) |- 'R('x)", "'P('x)", "z"),
            ("'P('x) /\\ 'Q('x) |- 'R('y)", "∃x. ('P('x) /\\ 'Q('x))|- 'R('y)", "('P('x) /\\ 'Q('y))", "x"),
            ("'P('f('g('x, 'y), 'z, 'h, 'j)) |- 'R('f('g('x, 'x), 'e, 'z, 'h))", "∃j. 'P('f('g('x, 'y), 'z, 'h, 'j))|- 'R('f('g('x, 'x), 'e, 'z, 'h))", "'P('f('g('x, 'y), 'z, 'h, 'j))", "h"),
            ("'P('x) |- 'R('y)", "∃y. 'P('x) |- 'R('y)", "'P('x)", "y"),
            ("'P('x) |- 'R('x)", "∃x. 'P('x) |- 'R('x)", "'P('x)", "x"),
            ("'A('y, 'x) |- 'R('x)", "∃x. 'A('y, 'x) |- 'R('x)", "'A('y, 'x)", "x"),
            ("'P('x); 'Q('x) |- 'R('x)", "∃z. 'P('z); 'Q('x) |- 'R('x)", "'P('z)", "z"),
            ("'P('x) /\\ 'Q('x) |- 'R('y)", "∃x. ('P('x) /\\ 'Q('y))|- 'R('y)", "('P('x) /\\ 'Q('y))", "x"),
            ("'P('f('g('x, 'y), 'z, 'h, 'j)) |- 'R('f('g('x, 'x), 'j, 'z, 'h))", "∃j. 'P('f('g('x, 'y), 'z, 'h, 'j))|- 'R('f('g('x, 'x), 'e, 'j, 'h))", "'P('f('g('x, 'y), 'z, 'h, 'j))", "j"),
        )

        testTacticCases(correct, incorrect){ (stmt1, stmt2, form, variable) =>
            val prem = introduceSequent(stmt1)
            LeftExists.withParameters(FOLParser.parseFormula(form), variable)(prem)(stmt2)
        }
    }

    //     left existsone
    test("Tactic Tests: Left ExistsOne - Parameter Inference") {
        val correct = List(
            ("∃x.∀y. ('y = 'x <=> 'P('y)) |- 'R('z)", "∃!y. 'P('y) |- 'R('z)"),
            ("∃x.∀y. ('y = 'x <=> 'P('w)) |- 'R('z)", "∃!y. 'P('w) |- 'R('z)"),
            ("∃x.∀y. ('y = 'x <=> 'P('w)) |- 'R('y)", "∃!y. 'P('w) |- 'R('y)"),
        )

        val incorrect = List(
            // TODO: FIX or KERNEL ERROR
            ("'P('x) |- 'R('y); 'Q('z)", "'P('x) |- 'R('y)"),
            ("∃x.∀y. ('y = 'x <=> 'P('w)) |- 'R('y)", "∃!y. 'P('w) |- 'R('z)"),
            ("∃x.∀y. ('y = 'x <=> 'P('w)) |- 'R('y)", "∃!y. 'P('y) |- 'R('y)"),
            ("∃x.∀y. ('y = 'x <=> 'P('x)) |- 'R('y)", "∃!x. 'P('x) |- 'R('y)"),
        )

        testTacticCases(correct, incorrect){ (stmt1, stmt2) =>
            val prem = introduceSequent(stmt1)
            LeftExistsOne(prem)(stmt2)
        }
    }

    test("Tactic Tests: Left ExistsOne - Explicit Parameters") {
        val correct = List(
            ("∃y.∀x.( ('x = 'y) <=> 'P('z)) |- 'R('w)", "∃!x. 'P('z) |- 'R('w)", "'P('z)", "x"),
            ("∃y.∀x.( ('x = 'y) <=> 'P('x)) |- 'R('w)", "∃!x. 'P('x) |- 'R('w)", "'P('x)", "x"),
            ("∃y.∀x.( ('x = 'y) <=> 'P('x)) |- 'R('x)", "∃!x. 'P('x) |- 'R('x)", "'P('x)", "x"),
        )

        val incorrect = List(
            ("∃y.∀x.( ('x = 'y) <=> 'P('z)) |- 'R('w)", "∃!x. 'P('z) |- 'R('y)", "'P('z)", "x"),
            // TODO: this looks v broken::
            ("∃y.∀x.( ('x = 'y) <=> 'P('x)) |- 'R('w)", "∃!x. 'P('x) |- 'R('w)", "'P('x)", "z"),
            ("∃y.∀x.( ('x = 'y) <=> 'P('x)) |- 'R('x)", "∃!x. 'P('z) |- 'R('x)", "'P('z)", "x"),
            ("∃x.∀y. ('y = 'x <=> 'P('w)) |- 'R('y)", "∃!y. 'P('w) |- 'R('z)", "'P('w)", "w"),
            ("∃x.∀y. ('y = 'x <=> 'P('w)) |- 'R('y)", "∃!y. 'P('y) |- 'R('y)", "'P('y)", "y"),
            ("∃x.∀y. ('y = 'x <=> 'P('x)) |- 'R('y)", "∃!x. 'P('x) |- 'R('y)", "'P('x)", "x"),
        )

        testTacticCases(correct, incorrect){ (stmt1, stmt2, form, variable) =>
            val prem = introduceSequent(stmt1)
            LeftExistsOne.withParameters(FOLParser.parseFormula(form), variable)(prem)(stmt2)
        }
    }

    // right rules

    //     right and
    test("Tactic Tests: Right And - Parameter Inference") {
        val correct = List(
            (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"),  "'P('x); 'R('x) |- 'Q('x) /\\ 'S('x)"),
            (List("'W('x); 'P('x) |- 'S('x)", "'R('x); 'O('x) |- 'Q('x); 'T('x)"),  "'P('x); 'R('x); 'O('x); 'W('x) |- 'Q('x) /\\ 'S('x); 'T('x)"),
            (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"),  "'R('x); 'P('x) |- 'Q('x) /\\ 'S('x); 'Q('x)"),
            // TODO: should this be allowed? ::
            (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"),  "'P('x) |- 'Q('x); 'S('x); 'E('x) \\/ 'T('x)"),
            (List("'P('x) |- 'S('x)"),  "'P('x) |- 'S('x)"),
        )

        val incorrect = List(
            (List(),  "'P('x) |- 'S('x)"),
            (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"),  "'P('x); 'T('x) |- 'Q('x) /\\'S('x)"),
            (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"),  "'P('x); 'R('x); 'T('x) |- 'Q('x) /\\ 'S('x)"),
        )

        testTacticCases(correct, incorrect){ (stmts, stmt2) =>
            val prems = stmts.map(introduceSequent(_))
            RightAnd(prems: _*)(stmt2)
        }
    }

    test("Tactic Tests: Right And - Explicit Parameters") {
        val correct = List(
            (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"),  "'P('x); 'R('x) |- 'Q('x) /\\ 'S('x)", List("'Q('x)", "'S('x)")),
            (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"),  "'P('x); 'R('x) |- 'Q('x) /\\ 'S('x)", List("'S('x)", "'Q('x)")),
            (List("'W('x); 'P('x) |- 'S('x)", "'R('x); 'O('x) |- 'Q('x); 'T('x)"),  "'P('x); 'R('x); 'O('x); 'W('x) |- 'Q('x) /\\ 'S('x); 'T('x)", List("'Q('x)", "'S('x)")),
            (List("'W('x); 'P('x) |- 'S('x)", "'R('x); 'O('x) |- 'Q('x); 'T('x)"),  "'P('x); 'R('x); 'O('x); 'W('x) |- 'Q('x) /\\ 'S('x); 'T('x)", List("'S('x)", "'Q('x)")),
            (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"),  "'P('x); 'R('x) |- 'Q('x) /\\ 'S('x); 'S('x)", List("'Q('x)", "'S('x)")),
            (List("'P('x) |- 'S('x)"),  "'P('x) |- 'S('x)", List("'P('x)")),
        )

        val incorrect = List(
            (List(),  "'P('x) |- 'S('x)", List()),
            (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"),  "'P('x); 'R('x) |- 'Q('x) /\\ 'S('x)", List("'P('x)", "'Q('x)")),
            (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"),  "'P('x); 'R('x) |- 'Q('x) /\\ 'S('x)", List("'P('x)")),
            (List("'P('x) |- 'S('x)", "'R('x); 'O('x) |- 'Q('x); 'T('x)"),  "'P('x); 'R('x); 'O('x); 'W('x) |- 'Q('x) /\\ 'S('x); 'T('x)", List("'P('x)", "'R('x)")),
            (List("'W('x); 'P('x) |- 'S('x)", "'R('x); 'O('x) |- 'Q('x); 'T('x)"),  "'P('x); 'R('x); 'O('x) |- 'Q('x) \\/ 'S('x); 'T('x)", List("'P('x)", "'R('x)")),
            (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"),  "'R('x); 'P('x) |- 'Q('x) \\/ 'S('x); 'S('x)", List("'E('x)", "'R('x)")),
            (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"),  "'P('x); 'R('x) |- 'E('x) \\/ 'T('x)", List("'E('x)", "'T('x)")),
        )

        testTacticCases(correct, incorrect){ (stmts, stmt2, forms) =>
            val prems = stmts.map(introduceSequent(_))
            RightAnd.withParameters(forms.map(FOLParser.parseFormula(_)): _*)(prems: _*)(stmt2)
        }
    }

    //     right or
    test("Tactic Tests: Right Or - Parameter Inference") {
        val correct = List(
            ("'R('x) |- 'P('x); 'Q('x)", "'R('x) |- 'P('x); 'Q('x) \\/ 'S('x)"),
            ("'R('x) |- 'P('x); 'Q('x); 'S('x)", "'R('x) |- 'P('x); 'Q('x) \\/ 'S('x)"),
            ("'R('x) |- 'P('x); 'Q('x); 'S('x)", "'R('x) |- 'P('x); 'Q('x); 'S('x)"),
            ("'R('x) |- 'P('x); 'Q('x); 'S('x) \\/ 'A('x)", "'R('x) |- 'P('x); 'Q('x) \\/ ('S('x) \\/ 'A('x))"),
        )

        val incorrect = List(
            ("'R('x) |- 'P('x); 'Q('x)", "'R('x) |- 'P('x); 'Q('x) /\\ 'S('x)"),
            ("'R('x) |- 'P('x); 'Q('x); 'S('x)", "'R('x) |- 'P('x); 'Q('x) /\\ 'S('x)"),
            ("'R('x) |- 'P('x); 'Q('x); 'S('x)", "'R('x) |- 'P('x); 'Q('x) \\/ 'P('x)"),
            ("'R('x) |- 'P('x); 'Q('x); 'S('x); 'A('x)", "'R('x) |- 'P('x); 'Q('x) \\/ 'S('x) \\/ 'A('x)"),
            ("'R('x) |- 'P('x); 'Q('x); 'S('x)", "'R('x) |- 'P('x); 'Q('x)"),
        )

        testTacticCases(correct, incorrect){ (stmt1, stmt2) =>
            val prem = introduceSequent(stmt1)
            RightOr(prem)(stmt2)
        }
    }

    test("Tactic Tests: Right Or - Explicit Parameters") {
        val correct = List(
            ("'R('x) |- 'P('x); 'Q('x)", "'R('x) |- 'P('x); 'Q('x) \\/ 'S('x)", "'Q('x)", "'S('x)"),
            ("'R('x) |- 'P('x); 'Q('x); 'S('x)", "'R('x) |- 'P('x); 'Q('x) \\/ 'S('x)", "'Q('x)", "'S('x)"),
            ("'R('x) |- 'P('x); 'Q('x); 'S('x) \\/ 'A('x)", "'R('x) |- 'P('x); 'Q('x) \\/ ('S('x) \\/ 'A('x))", "'Q('x)", "'S('x) \\/ 'A('x)"),
            ("'R('x) |- 'P('x); 'Q('x); 'S('x) \\/ 'A('x)", "'R('x) |- 'P('x); 'Q('x) \\/ 'S('x) \\/ 'A('x)", "'Q('x)", "'S('x) \\/ 'A('x)"),
        )

        val incorrect = List(
            ("'R('x) |- 'P('x); 'Q('x)", "'R('x) |- 'P('x); 'Q('x) /\\ 'S('x)", "'Q('x)", "'S('x)"),
            ("'R('x) |- 'P('x); 'Q('x); 'S('x)", "'R('x) |- 'P('x); 'Q('x) /\\ 'S('x)", "'Q('x)", "'S('x)"),
            ("'R('x) |- 'P('x); 'Q('x); 'S('x)", "'R('x) |- 'P('x); 'Q('x) \\/ 'P('x)", "'Q('x)", "'S('x)"),
            ("'R('x) |- 'P('x); 'Q('x); 'S('x)", "'R('x) |- 'P('x); 'Q('x) /\\ 'S('x)", "'Q('x)", "'S('x)"),
            ("'R('x) |- 'P('x); 'Q('x)", "'R('x) |- 'P('x); 'Q('x) \\/ 'S('x)", "'Q('x)", "'P('x)"),
            ("'R('x) |- 'P('x); 'Q('x); 'S('x)", "'R('x) |- 'P('x); 'Q('x) \\/ 'S('x)", "'P('x)", "'S('x)"),
            ("'R('x) |- 'P('x); 'Q('x); 'S('x) \\/ 'A('x)", "'R('x) |- 'P('x); 'Q('x) \\/ ('S('x) \\/ 'A('x))", "'Q('x)", "'S('x)"),
        )

        testTacticCases(correct, incorrect){ (stmt1, stmt2, phi, psi) =>
            val prem = introduceSequent(stmt1)
            RightOr.withParameters(FOLParser.parseFormula(phi), FOLParser.parseFormula(psi))(prem)(stmt2)
        }
    }

    //     right implies
    test("Tactic Tests: Right Implies - Parameter Inference") {
        val correct = List(
            ("'P('x); 'Q('x) |- 'R('x)", "'P('x) |- 'Q('x) ==> 'R('x)"),
            ("'Q('x) |- 'R('x)", " |- 'Q('x) ==> 'R('x)"),
            ("'P('x); 'Q('x); 'S('x) |- 'R('x)", "'P('x); 'S('x) |- 'Q('x) ==> 'R('x)"),
            ("'P('x); 'Q('x) |- 'R('x)", "'P('x) |- !'Q('x) \\/ 'R('x)"),
        )

        val incorrect = List(
            ("'P('x); 'Q('x) |- 'R('x)", "'P('x) |- 'Q('x); 'R('x)"),
            ("'P('x); 'Q('x) |- 'R('x)", " |- 'Q('x); 'R('x)"),
            ("'P('x); 'Q('x) |- 'R('x)", "'P('x) |- 'Q('x) /\\ 'R('x)"),
            ("'P('x); 'Q('x) |- 'R('x)", "'P('x) |- 'Q('x) \\/ 'R('x)"),
            ("'P('x); 'Q('x) |- 'R('x)", "'P('x); 'S('x) |- 'Q('x) ==> 'R('x)"),
            ("'P('x); 'Q('x); 'S('x) |- 'R('x)", "'P('x) |- 'Q('x) ==> 'R('x)"),
        )

        testTacticCases(correct, incorrect){ (stmt1, stmt2) =>
            val prem = introduceSequent(stmt1)
            RightImplies(prem)(stmt2)
        }
    }

    test("Tactic Tests: Right Implies - Explicit Parameters") {
        val correct = List(
            ("'P('x); 'Q('x) |- 'R('x)", "'P('x) |- 'Q('x) ==> 'R('x)", "'Q('x)", "'R('x)"),
            ("'Q('x) |- 'R('x)", " |- 'Q('x) ==> 'R('x)", "'Q('x)", "'R('x)"),
            ("'P('x); 'Q('x); 'S('x) |- 'R('x)", "'P('x); 'S('x) |- 'Q('x) ==> 'R('x)", "'Q('x)", "'R('x)"),
            ("'P('x); 'Q('x) |- 'R('x)", "'P('x) |- !'Q('x) \\/ 'R('x)", "'Q('x)", "'R('x)"),
        )

        val incorrect = List(
            ("'P('x); 'Q('x) |- 'R('x)", "'P('x) |- 'Q('x) ==> 'R('x)", "'Q('x)", "'P('x)"),
            ("'Q('x) |- 'R('x)", " |- 'Q('x) ==> 'R('x)", "'P('x)", "'R('x)"),
            ("'P('x); 'Q('x); 'S('x) |- 'R('x)", "'P('x); 'S('x) |- 'Q('x) ==> 'R('x)", "'P('x)", "'S('x)"),
            ("'P('x); 'Q('x) |- 'R('x)", "'P('x) |- !'Q('x) \\/ 'R('x)", "'R('x)", "'R('x)"),
            ("'P('x); 'Q('x) |- 'R('x)", "'P('x) |- 'Q('x); 'R('x)", "'Q('x)", "'R('x)"),
            ("'P('x); 'Q('x) |- 'R('x)", " |- 'Q('x); 'R('x)", "'Q('x)", "'R('x)"),
            ("'P('x); 'Q('x) |- 'R('x)", "'P('x) |- 'Q('x) /\\ 'R('x)", "'Q('x)", "'R('x)"),
            ("'P('x); 'Q('x) |- 'R('x)", "'P('x) |- 'Q('x) \\/ 'R('x)", "'Q('x)", "'R('x)"),
            ("'P('x); 'Q('x) |- 'R('x)", "'P('x); 'S('x) |- 'Q('x) ==> 'R('x)", "'Q('x)", "'R('x)"),
            ("'P('x); 'Q('x); 'S('x) |- 'R('x)", "'P('x) |- 'Q('x) ==> 'R('x)", "'Q('x)", "'R('x)"),
        )

        testTacticCases(correct, incorrect){ (stmt1, stmt2, form1, form2) =>
            val prem = introduceSequent(stmt1)
            RightImplies.withParameters(FOLParser.parseFormula(form1), FOLParser.parseFormula(form2))(prem)(stmt2)
        }
    }
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
