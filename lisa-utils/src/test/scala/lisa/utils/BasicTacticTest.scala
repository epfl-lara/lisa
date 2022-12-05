package lisa.utils

import lisa.kernel.proof.{SequentCalculus as SC}
import lisa.utils.Library
import lisa.utils.tactics.BasicStepTactic.*
import lisa.utils.tactics.ProofTacticLib
import org.scalatest.funsuite.AnyFunSuite
import lisa.utils.ProofTacticTestLib

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
