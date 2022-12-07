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
      ("'P('x); 'Q('x) |- 'P('x)")
    )

    val incorrect = List(
      ("'P('x) |- "),
      (" |- 'P('x)"),
      (" |- 'P('x); 'Q('x)"),
      ("'Q('x) |- ")
    )

    testTacticCases(correct, incorrect) {
      Hypothesis(_)
    }
  }

  // rewrite
  // TODO: make this use equivalence checker tests
  test("Tactic Tests: Rewrite") {
    val correct = List(
      ("'P('x); 'Q('x) |- 'R('x)", "'P('x) /\\ 'Q('x) |- 'R('x)"),
      ("'P('x) |- 'R('x); 'Q('x)", "'P('x) |- 'R('x) \\/ 'Q('x)")
    )

    val incorrect = List(
      ("'P('x); 'Q('x) |- 'R('x)", "'P('x) |- 'R('x)"),
      ("'P('x); 'Q('x) |- 'R('x)", "'P('x) \\/ 'Q('x) |- 'R('x)"),
      ("'P('x) |- 'R('x); 'Q('x)", "'P('x) |- 'R('x) /\\'Q('x) ")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2) =>
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

    testTacticCases(correct, incorrect) { (stmt1, stmt2, stmt3) =>
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

    testTacticCases(correct, incorrect) { (stmt1, stmt2, stmt3, form) =>
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
      ("'P('x); 'Q('x); 'S('x) /\\ 'A('x) |- 'R('x)", "'P('x); 'Q('x) /\\ ('S('x) /\\ 'A('x)) |- 'R('x)")
    )

    val incorrect = List(
      ("'P('x); 'Q('x) |- 'R('x)", "'P('x); 'Q('x) \\/ 'S('x) |- 'R('x)"),
      ("'P('x); 'Q('x); 'S('x) |- 'R('x)", "'P('x); 'Q('x) \\/ 'S('x) |- 'R('x)"),
      ("'P('x); 'Q('x); 'S('x) |- 'R('x)", "'P('x); 'Q('x) /\\ 'P('x) |- 'R('x)"),
      ("'P('x); 'Q('x); 'S('x); 'A('x) |- 'R('x)", "'P('x); 'Q('x) /\\ 'S('x) /\\ 'A('x) |- 'R('x)"),
      ("'P('x); 'Q('x); 'S('x) |- 'R('x)", "'P('x); 'Q('x) |- 'R('x)")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2) =>
      val prem = introduceSequent(stmt1)
      LeftAnd(prem)(stmt2)
    }
  }

  test("Tactic Tests: Left And - Explicit Parameters") {
    val correct = List(
      ("'P('x); 'Q('x) |- 'R('x)", "'P('x); 'Q('x) /\\ 'S('x) |- 'R('x)", "'Q('x)", "'S('x)"),
      ("'P('x); 'Q('x); 'S('x) |- 'R('x)", "'P('x); 'Q('x) /\\ 'S('x) |- 'R('x)", "'Q('x)", "'S('x)"),
      ("'P('x); 'Q('x); 'S('x) /\\ 'A('x) |- 'R('x)", "'P('x); 'Q('x) /\\ ('S('x) /\\ 'A('x)) |- 'R('x)", "'Q('x)", "'S('x) /\\ 'A('x)"),
      ("'P('x); 'Q('x); 'S('x) /\\ 'A('x) |- 'R('x)", "'P('x); 'Q('x) /\\ 'S('x) /\\ 'A('x) |- 'R('x)", "'Q('x)", "'S('x) /\\ 'A('x)")
    )

    val incorrect = List(
      ("'P('x); 'Q('x) |- 'R('x)", "'P('x); 'Q('x) \\/ 'S('x) |- 'R('x)", "'Q('x)", "'S('x)"),
      ("'P('x); 'Q('x); 'S('x) |- 'R('x)", "'P('x); 'Q('x) \\/ 'S('x) |- 'R('x)", "'Q('x)", "'S('x)"),
      ("'P('x); 'Q('x); 'S('x) |- 'R('x)", "'P('x); 'Q('x) /\\ 'P('x) |- 'R('x)", "'Q('x)", "'S('x)"),
      ("'P('x); 'Q('x); 'S('x); 'A('x) |- 'R('x)", "'P('x); 'Q('x) /\\ 'S('x) /\\ 'A('x) |- 'R('x)", "'Q('x)", "'S('x) /\\ 'A('x)"),
      ("'P('x); 'Q('x); 'S('x) |- 'R('x)", "'P('x); 'Q('x) |- 'R('x)", "'Q('x)", "'S('x)"),
      ("'P('x); 'Q('x) |- 'R('x)", "'P('x); 'Q('x) /\\ 'S('x) |- 'R('x)", "'Q('x)", "'P('x)"),
      ("'P('x); 'Q('x); 'S('x) |- 'R('x)", "'P('x); 'Q('x) /\\ 'S('x) |- 'R('x)", "'P('x)", "'S('x)"),
      ("'P('x); 'Q('x); 'S('x) /\\ 'A('x) |- 'R('x)", "'P('x); 'Q('x) /\\ ('S('x) /\\ 'A('x)) |- 'R('x)", "'Q('x)", "'S('x)")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2, phi, psi) =>
      val prem = introduceSequent(stmt1)
      LeftAnd.withParameters(FOLParser.parseFormula(phi), FOLParser.parseFormula(psi))(prem)(stmt2)
    }
  }

  //     left or
  test("Tactic Tests: Left Or - Parameter Inference") {
    val correct = List(
      (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"), "'P('x) \\/ 'R('x) |- 'Q('x); 'S('x)"),
      (List("'W('x); 'P('x) |- 'S('x)", "'R('x); 'O('x) |- 'Q('x); 'T('x)"), "'P('x) \\/ 'R('x); 'O('x); 'W('x) |- 'Q('x); 'S('x); 'T('x)"),
      (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"), "'P('x) \\/ 'R('x); 'P('x) |- 'Q('x); 'S('x)"),
      (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"), "'E('x) \\/ 'T('x); 'P('x) |- 'Q('x); 'S('x)"),
      (List("'P('x) |- 'S('x)"), "'P('x) |- 'S('x)")
    )

    val incorrect = List(
      (List(), "'P('x) |- 'S('x)"),
      (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"), "'P('x) \\/ 'R('x) |- 'T('x); 'S('x)"),
      (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"), "'P('x) \\/ 'R('x); 'T('x) |- 'Q('x); 'S('x)")
    )

    testTacticCases(correct, incorrect) { (stmts, stmt2) =>
      val prems = stmts.map(introduceSequent(_))
      LeftOr(prems: _*)(stmt2)
    }
  }

  test("Tactic Tests: Left Or - Explicit Parameters") {
    val correct = List(
      (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"), "'P('x) \\/ 'R('x) |- 'Q('x); 'S('x)", List("'P('x)", "'R('x)")),
      (List("'W('x); 'P('x) |- 'S('x)", "'R('x); 'O('x) |- 'Q('x); 'T('x)"), "'P('x) \\/ 'R('x); 'O('x); 'W('x) |- 'Q('x); 'S('x); 'T('x)", List("'P('x)", "'R('x)")),
      (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"), "'P('x) \\/ 'R('x); 'P('x) |- 'Q('x); 'S('x)", List("'P('x)", "'R('x)")),
      (List("'P('x) |- 'S('x)"), "'P('x) |- 'S('x)", List("'P('x)"))
    )

    val incorrect = List(
      (List(), "'P('x) |- 'S('x)", List()),
      (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"), "'P('x) \\/ 'R('x) |- 'Q('x); 'S('x)", List("'P('x)", "'Q('x)")),
      (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"), "'P('x) \\/ 'R('x) |- 'Q('x); 'S('x)", List("'P('x)")),
      (List("'P('x) |- 'S('x)", "'R('x); 'O('x) |- 'Q('x); 'T('x)"), "'P('x) \\/ 'R('x); 'O('x); 'W('x) |- 'Q('x); 'S('x); 'T('x)", List("'P('x)", "'R('x)")),
      (List("'W('x); 'P('x) |- 'S('x)", "'R('x); 'O('x) |- 'Q('x); 'T('x)"), "'P('x) \\/ 'R('x); 'O('x) |- 'Q('x); 'S('x); 'T('x)", List("'P('x)", "'R('x)")),
      (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"), "'P('x) \\/ 'R('x); 'P('x) |- 'Q('x); 'S('x)", List("'E('x)", "'R('x)")),
      (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"), "'E('x) \\/ 'T('x) |- 'Q('x); 'S('x)", List("'E('x)", "'T('x)"))
    )

    testTacticCases(correct, incorrect) { (stmts, stmt2, forms) =>
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
      ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); !'R('x) \\/ 'S('x) |- 'Q('x)")
    )

    val incorrect = List(
      ("'P('x) |- 'R('x)", "'S('x) |- 'T('x)", "'P('x); 'R('x) ==> 'S('x) |- 'Q('x)"),
      ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); 'R('x) ==> 'T('x) |- 'Q('x)"),
      ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); 'T('x) ==> 'S('x) |- 'Q('x)"),
      ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); 'R('x) ==> 'S('x) |- 'T('x)"),
      ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); 'R('x) \\/ 'S('x) |- 'Q('x)"),
      ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); 'R('x) /\\ 'S('x) |- 'Q('x)"),
      ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x) |- 'Q('x)")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2, stmt3) =>
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
      ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x); !'R('x) \\/ 'S('x) |- 'Q('x)", "'R('x)", "'S('x)")
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
      ("'P('x) |- 'R('x)", "'S('x) |- 'Q('x)", "'P('x) |- 'Q('x)", "'R('x)", "'S('x)")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2, stmt3, form1, form2) =>
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
      ("'P('x); 'Q('x) ==> 'S('x); 'Q('x) <=> 'S('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'S('x) |- 'R('x)")
    )

    val incorrect = List(
      ("'P('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'R('x)"),
      ("'P('x); !'Q('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'R('x)"),
      ("'P('x); 'Q('x) ==> 'S('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'S('x) |- 'R('x); 'P('x)"),
      ("'P('x); 'Q('x) ==> 'S('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'T('x) |- 'R('x)")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2) =>
      val prem = introduceSequent(stmt1)
      LeftIff(prem)(stmt2)
    }
  }

  test("Tactic Tests: Left Iff - Explicit Parameters") {
    val correct = List(
      ("'P('x); 'Q('x) ==> 'S('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'S('x) |- 'R('x)", "'Q('x)", "'S('x)"),
      ("'P('x); 'Q('x) ==> 'S('x); 'S('x) ==> 'Q('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'S('x) |- 'R('x)", "'Q('x)", "'S('x)"),
      ("'P('x); 'Q('x) ==> 'S('x); 'Q('x) <=> 'S('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'S('x) |- 'R('x)", "'Q('x)", "'S('x)")
    )

    val incorrect = List(
      ("'P('x); 'Q('x) ==> 'S('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'S('x) |- 'R('x)", "'Q('x)", "'P('x)"),
      ("'P('x); 'Q('x) ==> 'S('x); 'S('x) ==> 'Q('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'S('x) |- 'R('x)", "'P('x)", "'S('x)"),
      ("'P('x); 'Q('x) ==> 'S('x); 'Q('x) <=> 'S('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'S('x) |- 'R('x)", "'P('x)", "'R('x)"),
      ("'P('x); 'Q('x) ==> 'S('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'S('x) |- 'R('x); 'P('x)", "'Q('x)", "'S('x)"),
      ("'P('x); 'Q('x) ==> 'S('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'T('x) |- 'R('x)", "'Q('x)", "'S('x)"),
      ("'P('x); 'Q('x) ==> 'S('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'T('x) |- 'R('x)", "'Q('x)", "'T('x)")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2, form1, form2) =>
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
      ("'P('x); !'Q('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'R('x)")
    )

    val incorrect = List(
      ("'P('x); 'Q('x) ==> 'S('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'S('x) |- 'R('x); 'P('x)"),
      ("'P('x); 'Q('x) ==> 'S('x) |- 'R('x)", "'P('x); 'Q('x) <=> 'T('x) |- 'R('x)"),
      ("'P('x) |- 'Q('x); 'R('x)", "'P('x); 'Q('x) |- 'R('x)"),
      ("'P('x) |- 'Q('x); 'R('x)", "'P('x) |- 'R('x); !'Q('x)"),
      ("'P('x) |- 'Q('x); 'R('x)", "'P('x) |- 'R('x)")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2) =>
      val prem = introduceSequent(stmt1)
      LeftNot(prem)(stmt2)
    }
  }

  test("Tactic Tests: Left Not - Explicit Parameters") {
    val correct = List(
      ("'P('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'R('x)", "'Q('x)"),
      ("'P('x); !'Q('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'R('x)", "'Q('x)"),
      ("'P('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'Q('x); 'R('x)", "'Q('x)"),
      ("'P('x); !'Q('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'R('x)", "'Q('x)")
    )

    val incorrect = List(
      ("'P('x) |- 'Q('x); 'R('x)", "'P('x); 'Q('x) |- 'R('x)", "'Q('x)"),
      ("'P('x) |- 'Q('x); 'R('x)", "'P('x) |- 'R('x); !'Q('x)", "'Q('x)"),
      ("'P('x) |- 'Q('x); 'R('x)", "'P('x) |- 'R('x)", "'Q('x)"),
      ("'P('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'R('x)", "'P('x)"),
      ("'P('x); !'Q('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'R('x)", "'R('x)"),
      ("'P('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'Q('x); 'R('x)", "'P('x)"),
      ("'P('x); !'Q('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'R('x)", "'R('x)")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2, form) =>
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
      ("'P('f('g('x, 'y), 'z, 'h, 'j)) |- 'R('f('g('x, 'x), 'j, 'z, 'h))", "∀x. 'P('x)|- 'R('f('g('x, 'x), 'j, 'z, 'h))", "'f('g('x, 'y), 'z, 'h, 'j)")
    )

    val incorrect = List(
      ("'P('x) |- 'R('x)", "∀x. 'Q('x) |- 'R('x)", "'x"),
      ("'P('x) |- 'R('x)", "∀y. 'P('y) |- 'R('y)", "'x"),
      ("'P('x) |- 'R('x)", "∀x. 'Q('x) |- 'R('x)", "'y"),
      ("'P('x); 'Q('x) |- 'R('x)", "∀y. 'P('x); 'Q('y) |- 'R('x)", "'x"),
      ("'P('f('g('x, 'y), 'z, 'h, 'j)) |- 'R('f('g('x, 'x), 'j, 'z, 'h))", "∀x. 'P('x)|- 'R('f('g('x, 'x), 'j, 'z, 'h))", "'f('g('x, 'x), 'j, 'z, 'h)")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2, term) =>
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
      ("'P('f('g('x, 'y), 'z, 'h, 'j)) |- 'R('f('g('x, 'x), 'j, 'z, 'h))", "∀x. 'P('x)|- 'R('f('g('x, 'x), 'j, 'z, 'h))", "'P('x)", "x", "'f('g('x, 'y), 'z, 'h, 'j)")
    )

    val incorrect = List(
      ("'P('x) |- 'R('x)", "∀x. 'Q('x) |- 'R('x)", "'P('x)", "x", "'x"),
      ("'P('x) |- 'R('x)", "∀y. 'P('y) |- 'R('y)", "'P('x)", "y", "'x"),
      ("'P('x) |- 'R('x)", "∀x. 'Q('x) |- 'R('x)", "'Q('x)", "x", "'x"),
      ("'P('x) |- 'R('x)", "'P('x) |- 'R('x)", "'P('x)", "x", "'x"),
      ("'P('x); 'Q('x) |- 'R('x)", "∀y. 'P('x); 'Q('y) |- 'R('x)", "'P('x)", "y", "'x"),
      ("'P('f('g('x, 'y), 'z, 'h, 'j)) |- 'R('f('g('x, 'x), 'j, 'z, 'h))", "∀x. 'P('x)|- 'R('f('g('x, 'x), 'j, 'z, 'h))", "'P('x)", "x", "'f('g('x, 'x), 'j, 'z, 'h)")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2, form, variable, term) =>
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
      ("'P('f('g('x, 'y), 'z, 'h, 'j)) |- 'R('f('g('x, 'x), 'e, 'z, 'h))", "∃j. 'P('f('g('x, 'y), 'z, 'h, 'j))|- 'R('f('g('x, 'x), 'e, 'z, 'h))")
    )

    val incorrect = List(
      ("'P('x) |- 'R('y); 'Q('z)", "'P('x) |- 'R('y)"),
      ("'P('x) |- 'R('y)", "∃y. 'P('x) |- 'R('y)"),
      ("'P('x) |- 'R('x)", "∃x. 'P('x) |- 'R('x)"),
      ("'A('y, 'x) |- 'R('x)", "∃x. 'A('y, 'x) |- 'R('x)"),
      ("'P('x); 'Q('x) |- 'R('x)", "∃z. 'P('z); 'Q('x) |- 'R('x)"),
      ("'P('x) /\\ 'Q('x) |- 'R('y)", "∃x. ('P('x) /\\ 'Q('y))|- 'R('y)"),
      ("'P('f('g('x, 'y), 'z, 'h, 'j)) |- 'R('f('g('x, 'x), 'j, 'z, 'h))", "∃j. 'P('f('g('x, 'y), 'z, 'h, 'j))|- 'R('f('g('x, 'x), 'e, 'j, 'h))")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2) =>
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
      ("'P('f('g('x, 'y), 'z, 'h, 'j)) |- 'R('f('g('x, 'x), 'e, 'z, 'h))", "∃j. 'P('f('g('x, 'y), 'z, 'h, 'j))|- 'R('f('g('x, 'x), 'e, 'z, 'h))", "'P('f('g('x, 'y), 'z, 'h, 'j))", "j")
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
      ("'P('f('g('x, 'y), 'z, 'h, 'j)) |- 'R('f('g('x, 'x), 'j, 'z, 'h))", "∃j. 'P('f('g('x, 'y), 'z, 'h, 'j))|- 'R('f('g('x, 'x), 'e, 'j, 'h))", "'P('f('g('x, 'y), 'z, 'h, 'j))", "j")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2, form, variable) =>
      val prem = introduceSequent(stmt1)
      LeftExists.withParameters(FOLParser.parseFormula(form), variable)(prem)(stmt2)
    }
  }

  //     left existsone
  test("Tactic Tests: Left ExistsOne - Parameter Inference") {
    val correct = List(
      ("∃x.∀y. ('y = 'x <=> 'P('y)) |- 'R('z)", "∃!y. 'P('y) |- 'R('z)"),
      ("∃x.∀y. ('y = 'x <=> 'P('w)) |- 'R('z)", "∃!y. 'P('w) |- 'R('z)"),
      ("∃x.∀y. ('y = 'x <=> 'P('w)) |- 'R('y)", "∃!y. 'P('w) |- 'R('y)")
    )

    val incorrect = List(
      ("'P('x) |- 'R('y); 'Q('z)", "'P('x) |- 'R('y)"),
      ("∃x.∀y. ('y = 'x <=> 'P('w)) |- 'R('y)", "∃!y. 'P('w) |- 'R('z)"),
      ("∃x.∀y. ('y = 'x <=> 'P('w)) |- 'R('y)", "∃!y. 'P('y) |- 'R('y)"),
      ("∃x.∀y. ('y = 'x <=> 'P('x)) |- 'R('y)", "∃!x. 'P('x) |- 'R('y)")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2) =>
      val prem = introduceSequent(stmt1)
      LeftExistsOne(prem)(stmt2)
    }
  }

  test("Tactic Tests: Left ExistsOne - Explicit Parameters") {
    val correct = List(
      ("∃y.∀x.( ('x = 'y) <=> 'P('z)) |- 'R('w)", "∃!x. 'P('z) |- 'R('w)", "'P('z)", "x"),
      ("∃y.∀x.( ('x = 'y) <=> 'P('x)) |- 'R('w)", "∃!x. 'P('x) |- 'R('w)", "'P('x)", "x"),
      ("∃y.∀x.( ('x = 'y) <=> 'P('x)) |- 'R('x)", "∃!x. 'P('x) |- 'R('x)", "'P('x)", "x")
    )

    val incorrect = List(
      ("∃y.∀x.( ('x = 'y) <=> 'P('z)) |- 'R('w)", "∃!x. 'P('z) |- 'R('y)", "'P('z)", "x"),
      // TODO: this looks v broken::
      ("∃y.∀x.( ('x = 'y) <=> 'P('x)) |- 'R('w)", "∃!x. 'P('x) |- 'R('w)", "'P('x)", "z"),
      ("∃y.∀x.( ('x = 'y) <=> 'P('x)) |- 'R('x)", "∃!x. 'P('z) |- 'R('x)", "'P('z)", "x"),
      ("∃x.∀y. ('y = 'x <=> 'P('w)) |- 'R('y)", "∃!y. 'P('w) |- 'R('z)", "'P('w)", "w"),
      ("∃x.∀y. ('y = 'x <=> 'P('w)) |- 'R('y)", "∃!y. 'P('y) |- 'R('y)", "'P('y)", "y"),
      ("∃x.∀y. ('y = 'x <=> 'P('x)) |- 'R('y)", "∃!x. 'P('x) |- 'R('y)", "'P('x)", "x")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2, form, variable) =>
      val prem = introduceSequent(stmt1)
      LeftExistsOne.withParameters(FOLParser.parseFormula(form), variable)(prem)(stmt2)
    }
  }

  // right rules

  //     right and
  test("Tactic Tests: Right And - Parameter Inference") {
    val correct = List(
      (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"), "'P('x); 'R('x) |- 'Q('x) /\\ 'S('x)"),
      (List("'W('x); 'P('x) |- 'S('x)", "'R('x); 'O('x) |- 'Q('x); 'T('x)"), "'P('x); 'R('x); 'O('x); 'W('x) |- 'Q('x) /\\ 'S('x); 'T('x)"),
      (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"), "'R('x); 'P('x) |- 'Q('x) /\\ 'S('x); 'Q('x)"),
      (List("'P('x) |- 'S('x)"), "'P('x) |- 'S('x)")
    )

    val incorrect = List(
      (List(), "'P('x) |- 'S('x)"),
      (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"), "'P('x); 'T('x) |- 'Q('x) /\\'S('x)"),
      (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"), "'P('x); 'R('x); 'T('x) |- 'Q('x) /\\ 'S('x)")
    )

    testTacticCases(correct, incorrect) { (stmts, stmt2) =>
      val prems = stmts.map(introduceSequent(_))
      RightAnd(prems: _*)(stmt2)
    }
  }

  test("Tactic Tests: Right And - Explicit Parameters") {
    val correct = List(
      (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"), "'P('x); 'R('x) |- 'Q('x) /\\ 'S('x)", List("'Q('x)", "'S('x)")),
      (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"), "'P('x); 'R('x) |- 'Q('x) /\\ 'S('x)", List("'S('x)", "'Q('x)")),
      (List("'W('x); 'P('x) |- 'S('x)", "'R('x); 'O('x) |- 'Q('x); 'T('x)"), "'P('x); 'R('x); 'O('x); 'W('x) |- 'Q('x) /\\ 'S('x); 'T('x)", List("'Q('x)", "'S('x)")),
      (List("'W('x); 'P('x) |- 'S('x)", "'R('x); 'O('x) |- 'Q('x); 'T('x)"), "'P('x); 'R('x); 'O('x); 'W('x) |- 'Q('x) /\\ 'S('x); 'T('x)", List("'S('x)", "'Q('x)")),
      (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"), "'P('x); 'R('x) |- 'Q('x) /\\ 'S('x); 'S('x)", List("'Q('x)", "'S('x)")),
      (List("'P('x) |- 'S('x)"), "'P('x) |- 'S('x)", List("'P('x)"))
    )

    val incorrect = List(
      (List(), "'P('x) |- 'S('x)", List()),
      (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"), "'P('x); 'R('x) |- 'Q('x) /\\ 'S('x)", List("'P('x)", "'Q('x)")),
      (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"), "'P('x); 'R('x) |- 'Q('x) /\\ 'S('x)", List("'P('x)")),
      (List("'P('x) |- 'S('x)", "'R('x); 'O('x) |- 'Q('x); 'T('x)"), "'P('x); 'R('x); 'O('x); 'W('x) |- 'Q('x) /\\ 'S('x); 'T('x)", List("'P('x)", "'R('x)")),
      (List("'W('x); 'P('x) |- 'S('x)", "'R('x); 'O('x) |- 'Q('x); 'T('x)"), "'P('x); 'R('x); 'O('x) |- 'Q('x) \\/ 'S('x); 'T('x)", List("'P('x)", "'R('x)")),
      (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"), "'R('x); 'P('x) |- 'Q('x) \\/ 'S('x); 'S('x)", List("'E('x)", "'R('x)")),
      (List("'P('x) |- 'S('x)", "'R('x) |- 'Q('x)"), "'P('x); 'R('x) |- 'E('x) \\/ 'T('x)", List("'E('x)", "'T('x)"))
    )

    testTacticCases(correct, incorrect) { (stmts, stmt2, forms) =>
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
      ("'R('x) |- 'P('x); 'Q('x); 'S('x) \\/ 'A('x)", "'R('x) |- 'P('x); 'Q('x) \\/ ('S('x) \\/ 'A('x))")
    )

    val incorrect = List(
      ("'R('x) |- 'P('x); 'Q('x)", "'R('x) |- 'P('x); 'Q('x) /\\ 'S('x)"),
      ("'R('x) |- 'P('x); 'Q('x); 'S('x)", "'R('x) |- 'P('x); 'Q('x) /\\ 'S('x)"),
      ("'R('x) |- 'P('x); 'Q('x); 'S('x)", "'R('x) |- 'P('x); 'Q('x) \\/ 'P('x)"),
      ("'R('x) |- 'P('x); 'Q('x); 'S('x); 'A('x)", "'R('x) |- 'P('x); 'Q('x) \\/ 'S('x) \\/ 'A('x)"),
      ("'R('x) |- 'P('x); 'Q('x); 'S('x)", "'R('x) |- 'P('x); 'Q('x)")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2) =>
      val prem = introduceSequent(stmt1)
      RightOr(prem)(stmt2)
    }
  }

  test("Tactic Tests: Right Or - Explicit Parameters") {
    val correct = List(
      ("'R('x) |- 'P('x); 'Q('x)", "'R('x) |- 'P('x); 'Q('x) \\/ 'S('x)", "'Q('x)", "'S('x)"),
      ("'R('x) |- 'P('x); 'Q('x); 'S('x)", "'R('x) |- 'P('x); 'Q('x) \\/ 'S('x)", "'Q('x)", "'S('x)"),
      ("'R('x) |- 'P('x); 'Q('x); 'S('x) \\/ 'A('x)", "'R('x) |- 'P('x); 'Q('x) \\/ ('S('x) \\/ 'A('x))", "'Q('x)", "'S('x) \\/ 'A('x)"),
      ("'R('x) |- 'P('x); 'Q('x); 'S('x) \\/ 'A('x)", "'R('x) |- 'P('x); 'Q('x) \\/ 'S('x) \\/ 'A('x)", "'Q('x)", "'S('x) \\/ 'A('x)")
    )

    val incorrect = List(
      ("'R('x) |- 'P('x); 'Q('x)", "'R('x) |- 'P('x); 'Q('x) /\\ 'S('x)", "'Q('x)", "'S('x)"),
      ("'R('x) |- 'P('x); 'Q('x); 'S('x)", "'R('x) |- 'P('x); 'Q('x) /\\ 'S('x)", "'Q('x)", "'S('x)"),
      ("'R('x) |- 'P('x); 'Q('x); 'S('x)", "'R('x) |- 'P('x); 'Q('x) \\/ 'P('x)", "'Q('x)", "'S('x)"),
      ("'R('x) |- 'P('x); 'Q('x); 'S('x)", "'R('x) |- 'P('x); 'Q('x) /\\ 'S('x)", "'Q('x)", "'S('x)"),
      ("'R('x) |- 'P('x); 'Q('x)", "'R('x) |- 'P('x); 'Q('x) \\/ 'S('x)", "'Q('x)", "'P('x)"),
      ("'R('x) |- 'P('x); 'Q('x); 'S('x)", "'R('x) |- 'P('x); 'Q('x) \\/ 'S('x)", "'P('x)", "'S('x)"),
      ("'R('x) |- 'P('x); 'Q('x); 'S('x) \\/ 'A('x)", "'R('x) |- 'P('x); 'Q('x) \\/ ('S('x) \\/ 'A('x))", "'Q('x)", "'S('x)")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2, phi, psi) =>
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
      ("'P('x); 'Q('x) |- 'R('x)", "'P('x) |- !'Q('x) \\/ 'R('x)")
    )

    val incorrect = List(
      ("'P('x); 'Q('x) |- 'R('x)", "'P('x) |- 'Q('x); 'R('x)"),
      ("'P('x); 'Q('x) |- 'R('x)", " |- 'Q('x); 'R('x)"),
      ("'P('x); 'Q('x) |- 'R('x)", "'P('x) |- 'Q('x) /\\ 'R('x)"),
      ("'P('x); 'Q('x) |- 'R('x)", "'P('x) |- 'Q('x) \\/ 'R('x)"),
      ("'P('x); 'Q('x) |- 'R('x)", "'P('x); 'S('x) |- 'Q('x) ==> 'R('x)"),
      ("'P('x); 'Q('x); 'S('x) |- 'R('x)", "'P('x) |- 'Q('x) ==> 'R('x)")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2) =>
      val prem = introduceSequent(stmt1)
      RightImplies(prem)(stmt2)
    }
  }

  test("Tactic Tests: Right Implies - Explicit Parameters") {
    val correct = List(
      ("'P('x); 'Q('x) |- 'R('x)", "'P('x) |- 'Q('x) ==> 'R('x)", "'Q('x)", "'R('x)"),
      ("'Q('x) |- 'R('x)", " |- 'Q('x) ==> 'R('x)", "'Q('x)", "'R('x)"),
      ("'P('x); 'Q('x); 'S('x) |- 'R('x)", "'P('x); 'S('x) |- 'Q('x) ==> 'R('x)", "'Q('x)", "'R('x)"),
      ("'P('x); 'Q('x) |- 'R('x)", "'P('x) |- !'Q('x) \\/ 'R('x)", "'Q('x)", "'R('x)")
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
      ("'P('x); 'Q('x); 'S('x) |- 'R('x)", "'P('x) |- 'Q('x) ==> 'R('x)", "'Q('x)", "'R('x)")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2, form1, form2) =>
      val prem = introduceSequent(stmt1)
      RightImplies.withParameters(FOLParser.parseFormula(form1), FOLParser.parseFormula(form2))(prem)(stmt2)
    }
  }

  //     right iff
  test("Tactic Tests: Right Iff - Parameter Inference") {
    val correct = List(
      ("'P('x) |- 'R('x); 'Q('x) ==> 'S('x)", "'T('x) |- 'W('x); 'S('x) ==> 'Q('x) ", "'P('x); 'T('x) |- 'R('x); 'W('x); 'Q('x) <=> 'S('x)"),
      ("'P('x) |- 'R('x); 'Q('x) ==> 'S('x)", "'T('x) |- 'R('x); 'S('x) ==> 'Q('x) ", "'P('x); 'T('x) |- 'R('x); 'Q('x) <=> 'S('x)"),
      ("'P('x) |- 'R('x); 'Q('x) ==> 'S('x)", "'P('x) |- 'W('x); 'S('x) ==> 'Q('x) ", "'P('x) |- 'R('x); 'W('x); 'Q('x) <=> 'S('x)"),
      ("'P('x) |- 'R('x); 'Q('x) ==> 'S('x)", "'P('x) |- 'R('x); 'S('x) ==> 'Q('x) ", "'P('x) |- 'R('x); 'Q('x) <=> 'S('x)"),
      ("'P('x) |- 'S('x); 'Q('x) ==> 'S('x)", "'P('x) |- 'S('x); 'S('x) ==> 'Q('x) ", "'P('x) |- 'S('x); 'Q('x) <=> 'S('x)"),
      ("'P('x) |- 'R('x); 'Q('x) <=> 'S('x)", "'T('x) |- 'W('x); 'S('x) ==> 'Q('x) ", "'P('x); 'T('x) |- 'R('x); 'W('x); 'Q('x) <=> 'S('x)")
    )

    val incorrect = List(
      ("'P('x) |- 'R('x); 'Q('x) ==> 'S('x)", "'P('x) |- 'R('x); 'S('x) ==> 'Q('x) ", "'P('x) |- 'T('x); 'Q('x) <=> 'S('x)"),
      ("'P('x) |- 'S('x); 'Q('x) ==> 'S('x)", "'P('x) |- 'S('x); 'S('x) ==> 'Q('x) ", "'T('x) |- 'S('x); 'Q('x) <=> 'S('x)")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2, stmt3) =>
      val prem1 = introduceSequent(stmt1)
      val prem2 = introduceSequent(stmt2)
      RightIff(prem1, prem2)(stmt3)
    }
  }

  test("Tactic Tests: Right Iff - Explicit Parameters") {
    val correct = List(
      ("'P('x) |- 'R('x); 'Q('x) ==> 'S('x)", "'T('x) |- 'W('x); 'S('x) ==> 'Q('x) ", "'P('x); 'T('x) |- 'R('x); 'W('x); 'Q('x) <=> 'S('x)", "'Q('x)", "'S('x)"),
      ("'P('x) |- 'R('x); 'Q('x) ==> 'S('x)", "'T('x) |- 'R('x); 'S('x) ==> 'Q('x) ", "'P('x); 'T('x) |- 'R('x); 'Q('x) <=> 'S('x)", "'Q('x)", "'S('x)"),
      ("'P('x) |- 'R('x); 'Q('x) ==> 'S('x)", "'P('x) |- 'W('x); 'S('x) ==> 'Q('x) ", "'P('x) |- 'R('x); 'W('x); 'Q('x) <=> 'S('x)", "'Q('x)", "'S('x)"),
      ("'P('x) |- 'R('x); 'Q('x) ==> 'S('x)", "'P('x) |- 'R('x); 'S('x) ==> 'Q('x) ", "'P('x) |- 'R('x); 'Q('x) <=> 'S('x)", "'Q('x)", "'S('x)"),
      ("'P('x) |- 'S('x); 'Q('x) ==> 'S('x)", "'P('x) |- 'S('x); 'S('x) ==> 'Q('x) ", "'P('x) |- 'S('x); 'Q('x) <=> 'S('x)", "'Q('x)", "'S('x)")
    )

    val incorrect = List(
      ("'P('x) |- 'R('x); 'Q('x) ==> 'S('x)", "'T('x) |- 'W('x); 'S('x) ==> 'Q('x) ", "'P('x); 'T('x) |- 'R('x); 'W('x); 'Q('x) <=> 'S('x)", "'S('x)", "'S('x)"),
      ("'P('x) |- 'R('x); 'Q('x) ==> 'S('x)", "'T('x) |- 'R('x); 'S('x) ==> 'Q('x) ", "'P('x); 'T('x) |- 'R('x); 'Q('x) <=> 'S('x)", "'R('x)", "'R('x)"),
      ("'P('x) |- 'R('x); 'Q('x) ==> 'S('x)", "'T('x) |- 'R('x); 'S('x) ==> 'Q('x) ", "'P('x); 'T('x) |- 'R('x); 'Q('x) <=> 'S('x)", "'P('x)", "'S('x)"),
      ("'P('x) |- 'R('x); 'Q('x) ==> 'S('x)", "'P('x) |- 'W('x); 'S('x) ==> 'Q('x) ", "'P('x) |- 'R('x); 'W('x); 'Q('x) <=> 'S('x)", "'T('x)", "'S('x)"),
      ("'P('x) |- 'R('x); 'Q('x) ==> 'S('x)", "'P('x) |- 'R('x); 'S('x) ==> 'Q('x) ", "'P('x) |- 'R('x); 'Q('x) <=> 'S('x)", "'W('x)", "'S('x)"),
      ("'P('x) |- 'S('x); 'Q('x) ==> 'S('x)", "'P('x) |- 'S('x); 'S('x) ==> 'Q('x) ", "'P('x) |- 'S('x); 'Q('x) <=> 'S('x)", "'Q('x)", "'T('x)"),
      ("'P('x) |- 'R('x); 'Q('x) ==> 'S('x)", "'P('x) |- 'R('x); 'S('x) ==> 'Q('x) ", "'P('x) |- 'T('x); 'Q('x) <=> 'S('x)", "'Q('x)", "'S('x)"),
      ("'P('x) |- 'S('x); 'Q('x) ==> 'S('x)", "'P('x) |- 'S('x); 'S('x) ==> 'Q('x) ", "'T('x) |- 'S('x); 'Q('x) <=> 'S('x)", "'Q('x)", "'S('x)")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2, stmt3, form1, form2) =>
      val prem1 = introduceSequent(stmt1)
      val prem2 = introduceSequent(stmt2)
      RightIff.withParameters(FOLParser.parseFormula(form1), FOLParser.parseFormula(form2))(prem1, prem2)(stmt3)
    }
  }

  //     right not
  test("Tactic Tests: Right Not - Parameter Inference") {
    val correct = List(
      ("'Q('x); 'P('x) |- 'R('x)", "'P('x) |- 'R('x); !'Q('x)"),
      ("'Q('x); 'P('x) |- 'R('x); !'Q('x)", "'P('x)|- 'R('x); !'Q('x)"),
      ("'Q('x); 'P('x) |- 'Q('x); 'R('x)", "'P('x) |- 'R('x); 'Q('x); !'Q('x)")
    )

    val incorrect = List(
      ("'Q('x); 'P('x) |- 'Q('x); 'R('x)", "'P('x); 'Q('x) |- 'R('x); !'Q('x)"),
      ("'P('x) |- 'R('x); 'Q('x) ==> 'S('x)", "'P('x) |- 'R('x); 'P('x); 'Q('x) <=> 'S('x)"),
      ("'P('x) |- 'R('x); 'Q('x) ==> 'S('x)", "'P('x) |- 'R('x); 'Q('x) <=> 'T('x)"),
      ("'P('x); 'Q('x) |- 'R('x)", "'P('x) |- 'Q('x); 'R('x)"),
      ("'P('x) |- 'R('x); !'Q('x)", "'P('x) |- 'Q('x); 'R('x)"),
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2) =>
      val prem = introduceSequent(stmt1)
      RightNot(prem)(stmt2)
    }
  }

  test("Tactic Tests: Right Not - Explicit Parameters") {
    val correct = List(
      ("'Q('x); 'P('x) |- 'R('x)", "'P('x) |- 'R('x); !'Q('x)", "'Q('x)"),
      ("'Q('x); 'P('x) |- 'R('x)", "'P('x) |- 'R('x); ! ! !'Q('x)", "'Q('x)"),
      ("'Q('x); 'P('x) |- 'R('x); !'Q('x)", "'P('x)|- 'R('x); !'Q('x)", "'Q('x)"),
      ("'Q('x); 'P('x) |- 'Q('x); 'R('x)", "'P('x) |- 'R('x); 'Q('x); !'Q('x)", "'Q('x)")
    )

    val incorrect = List(
      ("'P('x) |- 'Q('x); 'R('x)", "'P('x); 'Q('x) |- 'R('x)", "'Q('x)"),
      ("'P('x) |- 'Q('x); 'R('x)", "'P('x) |- 'R('x); !'Q('x)", "'Q('x)"),
      ("'P('x) |- 'Q('x); 'R('x)", "'P('x) |- 'R('x)", "'Q('x)"),
      ("'P('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'R('x)", "'P('x)"),
      ("'P('x); !'Q('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'R('x)", "'R('x)"),
      ("'P('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'Q('x); 'R('x)", "'P('x)"),
      ("'P('x); !'Q('x) |- 'Q('x); 'R('x)", "'P('x); !'Q('x) |- 'R('x)", "'R('x)")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2, form) =>
      val prem = introduceSequent(stmt1)
      RightNot.withParameters(FOLParser.parseFormula(form))(prem)(stmt2)
    }
  }

  //     right forall
  test("Tactic Tests: Right Forall - Parameter Inference") {
    val correct = List(
      ("'P('x) |- 'R('y)", "'P('x) |- ∀y. 'R('y)"),
      ("'A('y, 'x) |- 'R('z)", "'A('y, 'x) |- ∀z. 'R('z)"),
      ("'P('z); 'Q('x) |- 'R('y)", "'P('z); 'Q('x) |- ∀y. 'R('y)"),
      ("'P('x) /\\ 'Q('x) |- 'R('y) /\\ 'S('x)", "('P('x) /\\ 'Q('x))|- ∀y. ('R('y) /\\ 'S('x))"),
      ("'P('f('g('x, 'y), 'z, 'h, 'j)) |- 'R('f('g('x, 'x), 'e, 'z, 'h))", "'P('f('g('x, 'y), 'z, 'h, 'j))|- ∀e. 'R('f('g('x, 'x), 'e, 'z, 'h))")
    )

    val incorrect = List(
      ("'P('x); 'Q('z) |- 'R('y)", "'P('x) |- 'R('y)"),
      ("∃y. 'P('x) |- 'R('y)", "'P('x) |- 'R('y)"),
      ("'P('y) |- 'R('y)", "'P('y) |- ∀y. 'R('y)"),
      ("'P('x) |- 'R('y)", "'T('x) |- ∀y. 'R('y)"),
      ("'P('x) |- 'R('y)", "'P('x) |- "),
      ("'P('x) |- 'R('y)", "'P('x) |- ∀y. 'Q('y)"),
      ("'P('x) /\\ 'Q('x) |- 'R('y) /\\ 'S('x)", "('P('x) /\\ 'Q('x))|- ∀y. ('R('y) \\/ 'S('x))")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2) =>
      val prem = introduceSequent(stmt1)
      RightForall(prem)(stmt2)
    }
  }

  test("Tactic Tests: Right Forall - Explicit Parameters") {
    val correct = List(
      ("'P('x) |- 'R('y)", "'P('x) |- ∀y. 'R('y)", "'R('y)", "y"),
      ("'A('y, 'x) |- 'R('z)", "'A('y, 'x) |- ∀z. 'R('z)", "'R('z)", "z"),
      ("'P('z); 'Q('x) |- 'R('y)", "'P('z); 'Q('x) |- ∀y. 'R('y)", "'R('y)", "y"),
      ("'P('x) /\\ 'Q('x) |- 'R('y) /\\ 'S('x)", "('P('x) /\\ 'Q('x))|- ∀y. ('R('y) /\\ 'S('x))", "'R('y) /\\ 'S('x)", "y"),
      ("'P('f('g('x, 'y), 'z, 'h, 'j)) |- 'R('f('g('x, 'x), 'e, 'z, 'h))", "'P('f('g('x, 'y), 'z, 'h, 'j))|- ∀e. 'R('f('g('x, 'x), 'e, 'z, 'h))", "'R('f('g('x, 'x), 'e, 'z, 'h))", "e")
    )

    val incorrect = List(
      ("'P('y) |- 'R('y)", "'P('y) |- ∀y. 'R('y)", "'R('y)", "y"),
      ("'P('x) |- 'R('y)", "'T('x) |- ∀y. 'R('y)", "'R('y)", "y"),
      ("'P('x) |- 'R('y)", "'P('x) |- ", "'R('y)", "y"),
      ("'P('x) |- 'R('y)", "'P('x) |- ∀y. 'Q('y)", "'R('y)", "y"),
      ("'P('x) /\\ 'Q('x) |- 'R('y) /\\ 'S('x)", "('P('x) /\\ 'Q('x))|- ∀y. ('R('y) \\/ 'S('x))", "'R('y) /\\ 'S('x)", "y"),
      ("'P('x) |- 'R('y)", "'P('x) |- ∀y. 'R('y)", "'R('y)", "x"),
      ("'A('y, 'x) |- 'R('z)", "'A('y, 'x) |- ∀z. 'R('z)", "'Q('z)", "z"),
      ("'P('z); 'Q('x) |- 'R('y)", "'P('z); 'Q('x) |- ∀y. 'R('y)", "'R('z)", "y"),
      ("'P('x) /\\ 'Q('x) |- 'R('y) /\\ 'S('x)", "('P('x) /\\ 'Q('x))|- ∀y. ('R('y) /\\ 'S('x))", "'R('y) \\/ 'S('x)", "y"),
      ("'P('f('g('x, 'y), 'z, 'h, 'j)) |- 'R('f('g('x, 'x), 'e, 'z, 'h))", "'P('f('g('x, 'y), 'z, 'h, 'j))|- ∀e. 'R('f('g('x, 'x), 'e, 'z, 'h))", "'R('f('g('y, 'y), 'e, 'z, 'h))", "e")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2, form, variable) =>
      val prem = introduceSequent(stmt1)
      RightForall.withParameters(FOLParser.parseFormula(form), variable)(prem)(stmt2)
    }
  }

  //     right exists
  test("Tactic Tests: Right Exists - Parameter Inference") {
    val correct = List(
      ("'P('x) |- 'R('x)", "'P('x) |- ∃x. 'R('x)", "'x"),
      ("'P('x) |- 'R('x)", "'P('x) |- ∃y. 'R('y)", "'x"),
      ("'P('x) |- 'R('x)", "'P('x) |- ∃y. 'R('x)", "'x"),
      (" |- 'R('x); 'A('x, 'x)", " |- 'R('x); ∃y. 'A('y, 'x)", "'x"),
      ("'P('x); 'Q('x) |- 'R('x)", "'P('x); 'Q('x) |- ∃y. 'R('y)", "'x"),
      ("'P('x) /\\ 'Q('x) |- 'R('x) /\\ 'Q('x)", "('P('x) /\\ 'Q('x)) |- ∃x. ('R('x) /\\ 'Q('x))", "'x"),
      ("'P('f('g('x, 'y), 'z, 'h, 'j)) |- 'R('f('g('x, 'x), 'j, 'z, 'h))", "'P('f('g('x, 'y), 'z, 'h, 'j))|- ∃x. 'R('f('x, 'j, 'z, 'h))", "'g('x, 'x)")
    )

    val incorrect = List(
      ("'P('x) |- 'R('x)", "∀x. 'P('x) |- 'R('x)", "'x"),
      ("'P('x) |- 'R('x)", "∀x. 'Q('x) |- 'R('x)", "'x"),
      ("'P('x) |- 'R('x)", "∀y. 'P('y) |- 'R('y)", "'x"),
      ("'P('x) |- 'R('x)", "∀x. 'Q('x) |- 'R('x)", "'y"),
      ("'P('x) |- 'R('x)", "'P('x) |- ∃x. 'R('x)", "'y"),
      ("'P('x) |- 'R('x)", "'P('x) |- ∃x. 'R('y)", "'x"),
      ("'P('x) |- 'R('x)", "'P('x) |- ∃y. 'R('z)", "'z"),
      (" |- 'R('x); 'A('x, 'x)", " |- 'R('x); ∃y. 'A('z, 'y)", "'x"),
      ("'P('x); 'Q('x) |- 'R('x)", "'P('x); 'T('x) |- ∃y. 'R('y)", "'x"),
      ("'P('x) /\\ 'Q('x) |- 'R('x) /\\ 'Q('x)", "('P('x) \\/ 'Q('x)) |- ∃x. ('R('x) /\\ 'Q('x))", "'x"),
      ("'P('f('g('x, 'y), 'z, 'h, 'j)) |- 'R('f('g('x, 'x), 'j, 'z, 'h))", "'P('f('g('x, 'y), 'z, 'h, 'j))|- ∃x. 'R('f('x, 'x, 'z, 'h))", "'g('x, 'x)")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2, term) =>
      val prem = introduceSequent(stmt1)
      RightExists(FOLParser.parseTerm(term))(prem)(stmt2)
    }
  }

  test("Tactic Tests: Right Exists - Explicit Parameters") {
    val correct = List(
      ("'P('x) |- 'R('x)", "'P('x) |- ∃x. 'R('x)", "'R('x)", "x", "'x"),
      ("'P('x) |- 'R('x)", "'P('x) |- ∃y. 'R('y)", "'R('y)", "y", "'x"),
      ("'P('x) |- 'R('x)", "'P('x) |- ∃y. 'R('x)", "'R('x)", "y", "'x"),
      (" |- 'R('x); 'A('x, 'x)", " |- 'R('x); ∃y. 'A('y, 'x)", "'A('y, 'x)", "y", "'x"),
      ("'P('x); 'Q('x) |- 'R('x)", "'P('x); 'Q('x) |- ∃y. 'R('y)", "'R('y)", "y", "'x"),
      ("'P('x) /\\ 'Q('x) |- 'R('x) /\\ 'Q('x)", "('P('x) /\\ 'Q('x)) |- ∃x. ('R('x) /\\ 'Q('x))", "'R('x) /\\ 'Q('x)", "x", "'x"),
      ("'P('f('g('x, 'y), 'z, 'h, 'j)) |- 'R('f('g('x, 'x), 'j, 'z, 'h))", "'P('f('g('x, 'y), 'z, 'h, 'j))|- ∃x. 'R('f('x, 'j, 'z, 'h))", "'R('f('x, 'j, 'z, 'h))", "x", "'g('x, 'x)")
    )

    val incorrect = List(
      ("'P('x) |- 'R('x)", "'P('x) |- ∃x. 'R('x)", "'R('x)", "x", "'y"),
      ("'P('x) |- 'R('x)", "'P('x) |- ∃x. 'R('y)", "'R('y)", "x", "'x"),
      ("'P('x) |- 'R('x)", "'P('x) |- ∃y. 'R('z)", "'R('z)", "y", "'z"),
      (" |- 'R('x); 'A('x, 'x)", " |- 'R('x); ∃y. 'A('z, 'y)", "'A('z, 'y)", "y", "'x"),
      ("'P('x); 'Q('x) |- 'R('x)", "'P('x); 'T('x) |- ∃y. 'R('y)", "'R('y)", "y", "'x"),
      ("'P('x) /\\ 'Q('x) |- 'R('x) /\\ 'Q('x)", "('P('x) \\/ 'Q('x)) |- ∃x. ('R('x) /\\ 'Q('x))", "'R('x)", "x", "'x"),
      ("'P('f('g('x, 'y), 'z, 'h, 'j)) |- 'R('f('g('x, 'x), 'j, 'z, 'h))", "'P('f('g('x, 'y), 'z, 'h, 'j))|- ∃x. 'R('f('x, 'x, 'z, 'h))", "'R('x)", "x", "'g('x, 'x)")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2, form, variable, term) =>
      val prem = introduceSequent(stmt1)
      RightExists.withParameters(FOLParser.parseFormula(form), variable, FOLParser.parseTerm(term))(prem)(stmt2)
    }
  }

  //     right existsone
  test("Tactic Tests: Right ExistsOne - Parameter Inference") {
    val correct = List(
      ("'R('z) |- ∃x.∀y. ('y = 'x <=> 'P('y))", "'R('z) |- ∃!y. 'P('y)"),
      ("'R('z) |- ∃x.∀y. ('y = 'x <=> 'P('w))", "'R('z) |- ∃!y. 'P('w)"),
      ("'R('z) |- ∃x.∀y. ('y = 'x <=> 'P('w))", "'R('z) |- ∃!y. 'P('w)")
    )

    val incorrect = List(
      ("'P('x); 'Q('z) |- 'R('y)", "'P('x) |- 'R('y)"),
      ("'R('y) |- ∃x.∀y. ('y = 'x <=> 'P('w))", "'R('z) |- ∃!y. 'P('w)"),
      ("'R('y) |- ∃x.∀y. ('y = 'x <=> 'P('w))", "'R('y) |- ∃!y. 'P('y)"),
      ("'R('y) |- ∃x.∀y. ('y = 'x <=> 'P('x))", "'R('y) |- ∃!x. 'P('x)")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2) =>
      val prem = introduceSequent(stmt1)
      RightExistsOne(prem)(stmt2)
    }
  }

  test("Tactic Tests: Right ExistsOne - Explicit Parameters") {
    val correct = List(
      ("'R('y) |- ∃y.∀x.( ('x = 'y) <=> 'P('z))", "'R('y) |- ∃!x. 'P('z)", "'P('z)", "x"),
      ("'R('y) |- ∃y.∀x.( ('x = 'y) <=> 'P('x))", "'R('y) |- ∃!x. 'P('x)", "'P('x)", "x"),
      ("'R('y) |- ∃y.∀x.( ('x = 'y) <=> 'P('x))", "'R('y) |- ∃!x. 'P('x)", "'P('x)", "x")
    )

    val incorrect = List(
      ("'R('y) |- ∃y.∀x.( ('x = 'y) <=> 'P('z))", "'R('w) |- ∃!x. 'P('z)", "'P('z)", "x"),
      // TODO: this looks v broken::
      ("'R('y) |- ∃y.∀x.( ('x = 'y) <=> 'P('x))", "'T('y) |- ∃!x. 'P('x)", "'P('x)", "z"),
      ("'R('y) |- ∃y.∀x.( ('x = 'y) <=> 'P('x))", "'R('z) |- ∃!x. 'P('z)", "'P('z)", "x"),
      ("'R('y) |- ∃x.∀y. ('y = 'x <=> 'P('w))", "'R('z) |- ∃!y. 'P('w)", "'P('w)", "w"),
      ("'R('y) |- ∃x.∀y. ('y = 'x <=> 'P('w))", "'R('y) |- ∃!y. 'P('y)", "'P('y)", "y"),
      ("'R('y) |- ∃x.∀y. ('y = 'x <=> 'P('x))", "'R('w) |- ∃!x. 'P('x)", "'P('x)", "x")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2, form, variable) =>
      val prem = introduceSequent(stmt1)
      RightExistsOne.withParameters(FOLParser.parseFormula(form), variable)(prem)(stmt2)
    }
  }

  // weakening
  test("Tactic Tests: Weakening") {
    val correct = List(
      ("'P('x) |- ", "'P('x) |- 'R('x)"),
      ("'P('x) |- 'R('x)", "'P('x) |- 'R('x)"),
      ("'P('x) |- 'R('x)", "'P('x) |- 'R('x); 'S('y)"),
      ("'P('x) |- 'R('x)", "'P('x); 'S('y) |- 'R('x)"),
      ("'P('x) |- 'R('x)", "'P('x); 'S('y) |- 'R('x); 'Q('z)"),
      ("'P('x) |- 'R('x)", "'P('x); 'S('y); 'Q('z) |- 'R('x); 'Q('z); 'S('k)"),
    )

    val incorrect = List(
      ("'P('x) |- 'R('x)", "'P('x) |- 'Q('x)"),
      ("'P('x) |- 'R('x)", "'P('x) |- "),
      ("'P('x); 'S('y) |- 'R('x)", "'P('x) |- 'R('x); 'S('y)"),
      ("'P('x); 'Q('y) |- 'R('x)", "'P('x); 'S('y) |- 'R('x)"),
      ("'P('x); 'Q('y) |- 'R('x)", "'P('x); 'Q('x) |- 'R('x)"),
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2) =>
      val prem = introduceSequent(stmt1)
      Weakening(prem)(stmt2)
    }
  }

  // left refl
  test("Tactic Tests: Left Refl - Parameter Inference") {
    val correct = List(
      ("'R('z); 'x = 'x |- 'P('x)", "'R('z) |- 'P('x)"),
      ("'R('z); 'x = 'x; 'y = 'y |- 'P('x)", "'R('z); 'y = 'y |- 'P('x)"),
    )

    val incorrect = List(
      ("'R('z); 'x = 'y |- 'P('x)", "'R('z) |- 'P('x)"),
      ("'R('z); 'x = 'x; 'y = 'y |- 'P('x)", "'R('z) |- 'P('x)"),
      ("'R('z); 'x = 'x |- 'P('x)", "'R('z); 'x = 'x |- 'P('x)"),
      ("'R('z); 'x = 'x |- 'P('x)", "'R('z); 'x = 'y |- 'P('x)"),
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2) =>
      val prem = introduceSequent(stmt1)
      LeftRefl(prem)(stmt2)
    }
  }

  test("Tactic Tests: Left Refl - Explicit Parameters") {
    val correct = List(
      ("'R('z); 'x = 'x |- 'P('x)", "'R('z) |- 'P('x)", "'x = 'x"),
      ("'R('z); 'x = 'x; 'y = 'y |- 'P('x)", "'R('z); 'y = 'y |- 'P('x)", "'x = 'x"),
    )

    val incorrect = List(
      ("'R('z); 'x = 'y |- 'P('x)", "'R('z) |- 'P('x)", "'x = 'y"),
      ("'R('z); 'x = 'x; 'y = 'y |- 'P('x)", "'R('z); 'y = 'y |- 'P('x)", "'y = 'y"),
      ("'R('z); 'x = 'y |- 'P('x)", "'R('z) |- 'P('x)", "'x = 'x"),
      ("'R('z); 'x = 'x; 'y = 'y |- 'P('x)", "'R('z) |- 'P('x)", "'x = 'x"),
      ("'R('z); 'x = 'x |- 'P('x)", "'R('z); 'x = 'y |- 'P('x)", "'x = 'x"),
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2, form) =>
      val prem = introduceSequent(stmt1)
      LeftRefl.withParameters(FOLParser.parseFormula(form))(prem)(stmt2)
    }
  }

  // right refl
  test("Tactic Tests: Right Refl - Parameter Inference") {
    val correct = List(
      (" |- 'x = 'x"),
      (" |- 'x = 'x; 'P('x)"),
      ("'P('x) |- 'x = 'x"),
      ("'P('x) |- 'x = 'x; 'R('x)"),
      ("'P('x) |- 'x = 'y; 'R('x); 'x = 'x"),
    )

    val incorrect = List(
      (" |- "),
      (" |- 'P('x)"),
      (" |- 'x = 'y"),
      ("'P('x) |- 'x = 'y"),
      ("'P('x) |- 'x = 'y; 'R('x)"),
    )

    testTacticCases(correct, incorrect) { (stmt) =>
      RightRefl(stmt)
    }
  }

  test("Tactic Tests: Right Refl - Explicit Parameters") {
    val correct = List(
      (" |- 'x = 'x", "'x = 'x"),
      (" |- 'x = 'x; 'P('x)", "'x = 'x"),
      ("'P('x) |- 'x = 'x", "'x = 'x"),
      ("'P('x) |- 'x = 'x; 'R('x)", "'x = 'x"),
      ("'P('x) |- 'x = 'y; 'R('x); 'x = 'x", "'x = 'x"),
    )

    val incorrect = List(
      (" |- ", "'x = 'x"),
      (" |- 'x = 'x", "'x = 'y"),
      (" |- 'x = 'x; 'P('x)", "'y = 'x"),
      ("'P('x) |- 'x = 'x", "'y = 'y"),
      (" |- 'P('x)", "'x = 'x"),
      (" |- 'x = 'y", "'x = 'x"),
      (" |- 'x = 'y", "'x = 'y"),
      ("'P('x) |- 'x = 'y", "'x = 'x"),
      ("'P('x) |- 'x = 'y", "'x = 'y"),
      ("'P('x) |- 'x = 'y; 'R('x)", "'x = 'x"),
      ("'P('x) |- 'x = 'y; 'R('x)", "'x = 'y"),
    )

    testTacticCases(correct, incorrect) { (stmt, form) =>
      RightRefl.withParameters(FOLParser.parseFormula(form))(stmt)
    }
  }

  // left substeq
  // right substeq

  // left substiff
  // right substiff

  // instfunschema
  // instpredschema

  // subproof
}
