package lisa.test.utils

//import lisa.kernel.proof.SequentCalculus as SC
//import lisa.prooflib.BasicStepTactic.*
//import lisa.prooflib.Library
//import lisa.prooflib.ProofTacticLib
//import lisa.utils.Printer
import lisa.test.utils.ProofTacticTestLib
//import org.scalatest.funsuite.AnyFunSuite

class BasicTacticTest extends ProofTacticTestLib {
  /*
  given Conversion[String, Sequent] = FOLParser.parseSequent(_)
  given Conversion[String, Formula] = FOLParser.parseFormula(_)
  given Conversion[String, Term] = FOLParser.parseTerm(_)
  given Conversion[String, VariableLabel] = s => VariableLabel(if (s.head == '?') s.tail else s)
   */
  /*
  val x: lisa.fol.FOL.Variable = variable
  val y = variable
  val z = variable

  val P = predicate[1]
  val Q = predicate[1]
  val R = predicate[1]
  val S = predicate[2]
  // hypothesis
  test("Tactic Tests: Hypothesis") {
    val correct = List[lisa.fol.FOL.Sequent](
      (P(x) |- P(x)),
      (P(x) |- (P(x),  Q(x))),
      ((P(x), Q(x)) |- (P(x), Q(x))),
      ((P(x), Q(x)) |- P(x))
    )

    val incorrect = List[lisa.fol.FOL.Sequent](
      (P(x) |- ()),
      (() |- ()),
      (() |- P(x)),
      (() |- (P(x), Q(x))),
      (Q(x) |- ())
    )

    /*testTacticCases(correct, incorrect) {
      Hypothesis(_)
    }*/
  }*/
  /*
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

  // rewrite true
  test("Tactic Tests: Rewrite True") {
    val correct = List(
      ("'P('x); 'Q('x) |- 'P('x); 'Q('x)"),
      ("'P('x) |- 'P('x); 'Q('x)"),
      ("'P('x); 'Q('x) |- 'Q('x)"),
      ("'P('x) |- 'P('x)"),
      ("'P('x); 'Q('x) |- 'P('x); 'R('x)")
    )

    val incorrect = List(
      ("'R('x) |- 'P('x); 'Q('x)"),
      ("'P('x); 'S('x) |- 'Q('x)"),
      ("'Q('x) |- 'P('x)"),
      (" |- ")
    )

    testTacticCases(correct, incorrect) {
      RewriteTrue(_)
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
  test("Tactic Tests: Left Forall - Partial Parameter Inference") {
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
      LeftForall.withParameters(FOLParser.parseTerm(term))(prem)(stmt2)
    }
  }

  test("Tactic Tests: Left Forall - Parameter Inference (FO Matching)") {
    val correct = List(
      ("'P('x) |- 'R('x)", "∀x. 'P('x) |- 'R('x)"),
      ("'P('x) |- 'R('x)", "∀y. 'P('y) |- 'R('x)"),
      ("'P('x) |- 'R('x)", "∀y. 'P('x) |- 'R('x)"),
      ("'A('x, 'x) |- 'R('x)", "∀y. 'A('y, 'x) |- 'R('x)"),
      ("'P('x); 'Q('x) |- 'R('x)", "∀x. 'P('x); 'Q('x) |- 'R('x)"),
      ("'P('x) /\\ 'Q('x) |- 'R('x)", "∀x. ('P('x) /\\ 'Q('x))|- 'R('x)"),
      ("'P('f('g('x, 'y), 'z, 'h, 'j)) |- 'R('f('g('x, 'x), 'j, 'z, 'h))", "∀x. 'P('x)|- 'R('f('g('x, 'x), 'j, 'z, 'h))")
    )

    val incorrect = List(
      ("'P('x) |- 'R('x)", "∀x. 'Q('x) |- 'R('x)"),
      ("'P('x) |- 'R('x)", "∀y. 'P('y) |- 'R('y)"),
      ("'P('x); 'Q('x) |- 'R('x)", "∀y. 'P('x); 'Q('y) |- 'R('x)")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2) =>
      val prem = introduceSequent(stmt1)
      LeftForall(prem)(stmt2)
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
      ("'P('x) |- 'R('x); !'Q('x)", "'P('x) |- 'Q('x); 'R('x)")
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
  test("Tactic Tests: Right Exists - Partial Parameter Inference") {
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
      RightExists.withParameters(FOLParser.parseTerm(term))(prem)(stmt2)
    }
  }

  test("Tactic Tests: Right Exists - Parameter Inference (FO Matching)") {
    val correct = List(
      ("'P('x) |- 'R('x)", "'P('x) |- ∃x. 'R('x)"),
      ("'P('x) |- 'R('x)", "'P('x) |- ∃y. 'R('y)"),
      ("'P('x) |- 'R('x)", "'P('x) |- ∃y. 'R('x)"),
      (" |- 'R('x); 'A('x, 'x)", " |- 'R('x); ∃y. 'A('y, 'x)"),
      ("'P('x); 'Q('x) |- 'R('x)", "'P('x); 'Q('x) |- ∃y. 'R('y)"),
      ("'P('x) /\\ 'Q('x) |- 'R('x) /\\ 'Q('x)", "('P('x) /\\ 'Q('x)) |- ∃x. ('R('x) /\\ 'Q('x))"),
      ("'P('f('g('x, 'y), 'z, 'h, 'j)) |- 'R('f('g('x, 'x), 'j, 'z, 'h))", "'P('f('g('x, 'y), 'z, 'h, 'j))|- ∃x. 'R('f('x, 'j, 'z, 'h))")
    )

    val incorrect = List(
      ("'P('x) |- 'R('x)", "∀x. 'P('x) |- 'R('x)"),
      ("'P('x) |- 'R('x)", "∀x. 'Q('x) |- 'R('x)"),
      ("'P('x) |- 'R('x)", "∀y. 'P('y) |- 'R('y)"),
      ("'P('x) |- 'R('x)", "∀x. 'Q('x) |- 'R('x)"),
      ("'P('x) |- 'R('x)", "'P('x) |- ∃y. 'R('z)"),
      (" |- 'R('x); 'A('x, 'x)", " |- 'R('x); ∃y. 'A('z, 'y)"),
      ("'P('x); 'Q('x) |- 'R('x)", "'P('x); 'T('x) |- ∃y. 'R('y)"),
      ("'P('f('g('x, 'y), 'z, 'h, 'j)) |- 'R('f('g('x, 'x), 'j, 'z, 'h))", "'P('f('g('x, 'y), 'z, 'h, 'j))|- ∃x. 'R('f('x, 'x, 'z, 'h))")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2) =>
      val prem = introduceSequent(stmt1)
      RightExists(prem)(stmt2)
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
      ("'P('x); 'Q('x) |- 'R('x)", "'P('x) /\\ 'Q('x) |- 'R('x)"),
      ("'P('x) |- 'R('x); 'Q('x)", "'P('x) |- 'R('x) \\/ 'Q('x)")
    )

    val incorrect = List(
      ("'P('x) |- 'R('x)", "'P('x) |- 'Q('x)"),
      ("'P('x) |- 'R('x)", "'P('x) |- "),
      ("'P('x); 'S('y) |- 'R('x)", "'P('x) |- 'R('x); 'S('y)"),
      ("'P('x); 'Q('y) |- 'R('x)", "'P('x); 'S('y) |- 'R('x)"),
      ("'P('x); 'Q('y) |- 'R('x)", "'P('x); 'Q('x) |- 'R('x)"),
      ("'P('x); 'Q('x) |- 'R('x)", "'P('x) |- 'R('x)"),
      ("'P('x); 'Q('x) |- 'R('x)", "'P('x) \\/ 'Q('x) |- 'R('x)"),
      ("'P('x) |- 'R('x); 'Q('x)", "'P('x) |- 'R('x) /\\'Q('x) ")
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
      ("'R('z); 'x = 'x; 'y = 'y |- 'P('x)", "'R('z); 'y = 'y |- 'P('x)")
    )

    val incorrect = List(
      ("'R('z); 'x = 'y |- 'P('x)", "'R('z) |- 'P('x)"),
      ("'R('z); 'x = 'x; 'y = 'y |- 'P('x)", "'R('z) |- 'P('x)"),
      ("'R('z); 'x = 'x |- 'P('x)", "'R('z); 'x = 'x |- 'P('x)"),
      ("'R('z); 'x = 'x |- 'P('x)", "'R('z); 'x = 'y |- 'P('x)")
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2) =>
      val prem = introduceSequent(stmt1)
      LeftRefl(prem)(stmt2)
    }
  }

  test("Tactic Tests: Left Refl - Explicit Parameters") {
    val correct = List(
      ("'R('z); 'x = 'x |- 'P('x)", "'R('z) |- 'P('x)", "'x = 'x"),
      ("'R('z); 'x = 'x; 'y = 'y |- 'P('x)", "'R('z); 'y = 'y |- 'P('x)", "'x = 'x")
    )

    val incorrect = List(
      ("'R('z); 'x = 'y |- 'P('x)", "'R('z) |- 'P('x)", "'x = 'y"),
      ("'R('z); 'x = 'x; 'y = 'y |- 'P('x)", "'R('z); 'y = 'y |- 'P('x)", "'y = 'y"),
      ("'R('z); 'x = 'y |- 'P('x)", "'R('z) |- 'P('x)", "'x = 'x"),
      ("'R('z); 'x = 'x |- 'P('x)", "'R('z); 'x = 'y |- 'P('x)", "'x = 'x")
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
      ("'P('x) |- 'x = 'y; 'R('x); 'x = 'x")
    )

    val incorrect = List(
      (" |- "),
      (" |- 'P('x)"),
      (" |- 'x = 'y"),
      ("'P('x) |- 'x = 'y"),
      ("'P('x) |- 'x = 'y; 'R('x)")
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
      ("'P('x) |- 'x = 'y; 'R('x); 'x = 'x", "'x = 'x")
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
      ("'P('x) |- 'x = 'y; 'R('x)", "'x = 'y")
    )

    testTacticCases(correct, incorrect) { (stmt, form) =>
      RightRefl.withParameters(FOLParser.parseFormula(form))(stmt)
    }
  }

  // left substeq
  test("Tactic Tests: Left SubstEq") {
    val q = variable
    val w = variable
    val e = variable
    val r = variable
    val t = variable
    val y = variable
    val Y = predicate(6)
    val Y1 = LambdaTermFormula(Seq(q), Y(q, w, e, r, t, y))
    val Y2 = LambdaTermFormula(Seq(q, w), Y(q, w, e, r, t, y))
    val Y5 = LambdaTermFormula(Seq(q, w, e, r, t, y), Y(q, w, e, r, t, y))

    val correct = List(
      ("'P('x); 'Y('q, 'w, 'e, 'r, 't, 'y) |- 'R('x)", "'P('x); 'a = 'q; 'Y('a, 'w, 'e, 'r, 't, 'y) |- 'R('x)", List(("'a", "'q")), Y1),
      ("'P('x); 'Y('q, 'w, 'e, 'r, 't, 'y) |- 'R('x)", "'P('x); 'a = 'q; 'Y('a, 'w, 'e, 'r, 't, 'y) |- 'R('x)", List(("'a", "'q")), Y1),
      ("'P('x); 'Y('q, 'w, 'e, 'r, 't, 'y) |- 'R('x)", "'P('x); 'a = 'q; 's = 'w; 'Y('a, 's, 'e, 'r, 't, 'y) |- 'R('x)", List(("'a", "'q"), ("'s", "'w")), Y2),
      (
        "'P('q); 'Y('q, 'w, 'e, 'r, 't, 'y) |- 'R('x)",
        "'P('q); 'a = 'q; 's = 'w; 'd = 'e; 'f = 'r; 'g = 't; 'h = 'y; 'Y('a, 's, 'd, 'f, 'g, 'h) |- 'R('x)",
        List(("'a", "'q"), ("'s", "'w"), ("'d", "'e"), ("'f", "'r"), ("'g", "'t"), ("'h", "'y")),
        Y5
      )
    )

    val incorrect = List(
      ("'P('x); 'Y('q, 'w, 'e, 'r, 't, 'y) |- 'R('x)", "'P('x); 'Y('q, 'w, 'e, 'r, 't, 'y) |- 'R('x)", List(("'a", "'q")), Y1),
      ("'P('x); 'Y('q, 'w, 'e, 'r, 't, 'y) |- 'R('x)", "'P('x); 'Y('a, 'w, 'e, 'r, 't, 'y) |- 'R('x)", List(("'a", "'q")), Y1),
      ("'P('x); 'Y('q, 'w, 'e, 'r, 't, 'y) |- 'R('x)", "'P('x); 'a = 'w; 'Y('a, 'w, 'e, 'r, 't, 'y) |- 'R('x)", List(("'a", "'q")), Y1),
      ("'P('x); 'Y('q, 'w, 'e, 'r, 't, 'y) |- 'R('x)", "'P('x); 'a = 'q; 'S('x); 'Y('a, 'w, 'e, 'r, 't, 'y) |- 'R('x)", List(("'a", "'q")), Y1),
      ("'P('x); 'Y('q, 'w, 'e, 'r, 't, 'y) |- 'R('x)", "'P('x); 'a = 'q; 'S('x); 'Y('a, 'w, 'e, 'r, 't, 'y) |- 'R('x)", List(("'a", "'q")), Y1),
      ("'P('x); 'Y('q, 'w, 'e, 'r, 't, 'y) |- 'R('x)", "'P('x); 'a = 'q; 'Y('a, 'w, 'e, 'r, 't, 'y) |- 'S('x); 'R('x)", List(("'a", "'q")), Y1),
      (
        "'P('q); 'Y('q, 'w, 'e, 'r, 't, 'y) |- 'R('x)",
        "'P('q); 'a = 'q; 's = 'w; 'd = 'e; 'f = 'r; 'g = 't; 'h = 't; 'Y('a, 's, 'd, 'f, 'g, 'h) |- 'R('x)",
        List(("'a", "'q"), ("'s", "'w"), ("'d", "'e"), ("'f", "'r"), ("'g", "'t"), ("'h", "'t")),
        Y5
      ),
      (
        "'P('q); 'Y('q, 'w, 'e, 'r, 't, 'y) |- 'R('x)",
        "'P('q); 'a = 'q; 's = 'w; 'd = 'e; 'f = 'r; 'g = 't; 'h = 'y; 'Y('a, 's, 'd, 'f, 'g, 'h) |- 'R('x)",
        List(("'a", "'q"), ("'s", "'w"), ("'d", "'e"), ("'f", "'r"), ("'g", "'t"), ("'h", "'t")),
        Y5
      ),
      (
        "'P('q); 'Y('q, 'w, 'e, 'r, 't, 'y) |- 'R('x)",
        "'P('q); 'a = 'q; 's = 'w; 'd = 'e; 'f = 'r; 'g = 't; 'h = 't; 'Y('a, 's, 'd, 'f, 'g, 'h) |- 'R('x)",
        List(("'a", "'q"), ("'s", "'w"), ("'d", "'e"), ("'f", "'r"), ("'g", "'t"), ("'h", "'y")),
        Y5
      )
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2, forms, ltf) =>
      val prem = introduceSequent(stmt1)
      LeftSubstEq(forms.map((a, b) => (FOLParser.parseTerm(a), FOLParser.parseTerm(b))), ltf)(prem)(stmt2)
    }
  }

  // right substeq
  test("Tactic Tests: Right SubstEq") {
    val q = variable
    val w = variable
    val e = variable
    val r = variable
    val t = variable
    val y = variable
    val Y = predicate(6)
    val Y1 = LambdaTermFormula(Seq(q), Y(q, w, e, r, t, y))
    val Y2 = LambdaTermFormula(Seq(q, w), Y(q, w, e, r, t, y))
    val Y5 = LambdaTermFormula(Seq(q, w, e, r, t, y), Y(q, w, e, r, t, y))

    val correct = List(
      ("'P('x) |- 'R('x); 'Y('q, 'w, 'e, 'r, 't, 'y)", "'P('x); 'a = 'q |- 'R('x); 'Y('a, 'w, 'e, 'r, 't, 'y)", List(("'a", "'q")), Y1),
      ("'P('x) |- 'R('x); 'Y('q, 'w, 'e, 'r, 't, 'y)", "'P('x); 'a = 'q |- 'R('x); 'Y('a, 'w, 'e, 'r, 't, 'y)", List(("'a", "'q")), Y1),
      ("'P('x) |- 'R('x); 'Y('q, 'w, 'e, 'r, 't, 'y)", "'P('x); 'a = 'q; 's = 'w |- 'R('x); 'Y('a, 's, 'e, 'r, 't, 'y)", List(("'a", "'q"), ("'s", "'w")), Y2),
      (
        "'P('x) |- 'R('x); 'Y('q, 'w, 'e, 'r, 't, 'y)",
        "'P('x); 'a = 'q; 's = 'w; 'd = 'e; 'f = 'r; 'g = 't; 'h = 'y |- 'R('x); 'Y('a, 's, 'd, 'f, 'g, 'h)",
        List(("'a", "'q"), ("'s", "'w"), ("'d", "'e"), ("'f", "'r"), ("'g", "'t"), ("'h", "'y")),
        Y5
      )
    )

    val incorrect = List(
      ("'P('x) |- 'R('x); 'Y('q, 'w, 'e, 'r, 't, 'y)", "'P('x) |- 'R('x); 'Y('q, 'w, 'e, 'r, 't, 'y)", List(("'a", "'q")), Y1),
      ("'P('x) |- 'R('x); 'Y('q, 'w, 'e, 'r, 't, 'y)", "'P('x) |- 'R('x); 'Y('a, 'w, 'e, 'r, 't, 'y)", List(("'a", "'q")), Y1),
      ("'P('x) |- 'R('x); 'Y('q, 'w, 'e, 'r, 't, 'y)", "'P('x); 'a = 'w |- 'R('x); 'Y('a, 'w, 'e, 'r, 't, 'y)", List(("'a", "'q")), Y1),
      ("'P('x) |- 'R('x); 'Y('q, 'w, 'e, 'r, 't, 'y)", "'P('x); 'a = 'q; 'S('x) |- 'R('x); 'Y('a, 'w, 'e, 'r, 't, 'y)", List(("'a", "'q")), Y1),
      ("'P('x) |- 'R('x); 'Y('q, 'w, 'e, 'r, 't, 'y)", "'P('x); 'a = 'q; 'S('x) |- 'R('x); 'Y('a, 'w, 'e, 'r, 't, 'y)", List(("'a", "'q")), Y1),
      ("'P('x) |- 'R('x); 'Y('q, 'w, 'e, 'r, 't, 'y)", "'P('x); 'a = 'q |- 'S('x); 'R('x); 'Y('a, 'w, 'e, 'r, 't, 'y)", List(("'a", "'q")), Y1),
      (
        "'P('x) |- 'R('x); 'Y('q, 'w, 'e, 'r, 't, 'y)",
        "'P('q); 'a = 'q; 's = 'w; 'd = 'e; 'f = 'r; 'g = 't; 'h = 't |- 'R('x); 'Y('a, 's, 'd, 'f, 'g, 'h)",
        List(("'a", "'q"), ("'s", "'w"), ("'d", "'e"), ("'f", "'r"), ("'g", "'t"), ("'h", "'t")),
        Y5
      ),
      (
        "'P('x) |- 'R('x); 'Y('q, 'w, 'e, 'r, 't, 'y)",
        "'P('q); 'a = 'q; 's = 'w; 'd = 'e; 'f = 'r; 'g = 't; 'h = 'y |- 'R('x); 'Y('a, 's, 'd, 'f, 'g, 'h)",
        List(("'a", "'q"), ("'s", "'w"), ("'d", "'e"), ("'f", "'r"), ("'g", "'t"), ("'h", "'t")),
        Y5
      ),
      (
        "'P('x) |- 'R('x); 'Y('q, 'w, 'e, 'r, 't, 'y)",
        "'P('q); 'a = 'q; 's = 'w; 'd = 'e; 'f = 'r; 'g = 't; 'h = 't |- 'R('x); 'Y('a, 's, 'd, 'f, 'g, 'h)",
        List(("'a", "'q"), ("'s", "'w"), ("'d", "'e"), ("'f", "'r"), ("'g", "'t"), ("'h", "'y")),
        Y5
      )
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2, forms, ltf) =>
      val prem = introduceSequent(stmt1)
      RightSubstEq(forms.map((a, b) => (FOLParser.parseTerm(a), FOLParser.parseTerm(b))), ltf)(prem)(stmt2)
    }
  }

  // left substiff
  test("Tactic Tests: Left SubstIff") {
    val q = FOLParser.parseFormula("'Q('q)")
    val w = FOLParser.parseFormula("'W('w)")
    val e = FOLParser.parseFormula("'E('e)")
    val r = FOLParser.parseFormula("'R('r)")
    val t = FOLParser.parseFormula("'T('t)")
    val y = FOLParser.parseFormula("'Y('y)")
    val a = FOLParser.parseFormula("'A('a)")
    val s = FOLParser.parseFormula("'S('s)")
    val d = FOLParser.parseFormula("'D('d)")
    val f = FOLParser.parseFormula("'F('f)")
    val g = FOLParser.parseFormula("'G('g)")
    val h = FOLParser.parseFormula("'H('h)")
    val z = VariableFormulaLabel("z")
    val x = VariableFormulaLabel("x")
    val c = VariableFormulaLabel("c")
    val v = VariableFormulaLabel("v")
    val b = VariableFormulaLabel("b")
    val n = VariableFormulaLabel("n")
    val Y1 = LambdaFormulaFormula(Seq(z), z /\ w /\ e /\ r /\ t /\ y)
    val Y2 = LambdaFormulaFormula(Seq(z, x), z /\ x /\ e /\ r /\ t /\ y)
    val Y5 = LambdaFormulaFormula(Seq(z, x, c, v, b, n), z /\ x /\ c /\ v /\ b /\ n)

    val correct = List(
      (
        "'P('x); ('Q('q) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y)) |- 'R('x)",
        "'P('x); ('A('a) <=> 'Q('q)); ('A('a) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y)) |- 'R('x)",
        List((a, q)),
        Y1
      ),
      (
        "'P('x); ('Q('q) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y)) |- 'R('x)",
        "'P('x); ('A('a) <=> 'Q('q)); ('A('a) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y)) |- 'R('x)",
        List((a, q)),
        Y1
      ),
      (
        "'P('x); ('Q('q) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y)) |- 'R('x)",
        "'P('x); ('A('a) <=> 'Q('q)); ('S('s) <=> 'W('w)); ('A('a) /\\ 'S('s) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y)) |- 'R('x)",
        List((a, q), (s, w)),
        Y2
      ),
      (
        "'P('q); ('Q('q) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y)) |- 'R('x)",
        "'P('q); ('A('a) <=> 'Q('q)); ('S('s) <=> 'W('w)); ('D('d) <=> 'E('e)); ('F('f) <=> 'R('r)); ('G('g) <=> 'T('t)); ('H('h) <=> 'Y('y)); ('A('a) /\\ 'S('s) /\\ 'D('d) /\\ 'F('f) /\\ 'G('g) /\\ 'H('h)) |- 'R('x)",
        List((a, q), (s, w), (d, e), (f, r), (g, t), (h, y)),
        Y5
      )
    )

    val incorrect = List(
      ("'P('x); ('Q('q) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y)) |- 'R('x)", "'P('x); ('Q('q) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y)) |- 'R('x)", List((a, q)), Y1),
      ("'P('x); ('Q('q) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y)) |- 'R('x)", "'P('x); ('A('a) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y)) |- 'R('x)", List((a, q)), Y1),
      (
        "'P('x); ('Q('q) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y)) |- 'R('x)",
        "'P('x); ('A('a) <=> 'W('w)); ('A('a) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y)) |- 'R('x)",
        List((a, q)),
        Y1
      ),
      (
        "'P('x); ('Q('q) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y)) |- 'R('x)",
        "'P('x); ('A('a) <=> 'Q('q)); 'S('x); ('A('a) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y)) |- 'R('x)",
        List((a, q)),
        Y1
      ),
      (
        "'P('x); ('Q('q) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y)) |- 'R('x)",
        "'P('x); ('A('a) <=> 'Q('q)); 'S('x); ('A('a) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y)) |- 'R('x)",
        List((a, q)),
        Y1
      ),
      (
        "'P('x); ('Q('q) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y)) |- 'R('x)",
        "'P('x); ('A('a) <=> 'Q('q)); ('A('a) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y)) |- 'S('x); 'R('x)",
        List((a, q)),
        Y1
      ),
      (
        "'P('q); ('Q('q) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y)) |- 'R('x)",
        "'P('q); ('A('a) <=> 'Q('q)); ('S('s) <=> 'W('w)); ('D('d) <=> 'E('e)); ('F('f) <=> 'R('r)); ('G('g) <=> 'T('t)); ('H('h) <=> 'T('t)); ('A('a) /\\ 'S('s) /\\ 'D('d) /\\ 'F('f) /\\ 'G('g) /\\ 'H('h)) |- 'R('x)",
        List((a, q), (s, w), (d, e), (f, r), (g, t), (h, t)),
        Y5
      ),
      (
        "'P('q); ('Q('q) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y)) |- 'R('x)",
        "'P('q); ('A('a) <=> 'Q('q)); ('S('s) <=> 'W('w)); ('D('d) <=> 'E('e)); ('F('f) <=> 'R('r)); ('G('g) <=> 'T('t)); ('H('h) <=> 'T('t)); ('A('a) /\\ 'S('s) /\\ 'D('d) /\\ 'F('f) /\\ 'G('g) /\\ 'H('h)) |- 'R('x)",
        List((a, q), (s, w), (d, e), (f, r), (g, t), (h, t)),
        Y5
      ),
      (
        "'P('q); ('Q('q) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y)) |- 'R('x)",
        "'P('q); ('A('a) <=> 'Q('q)); ('S('s) <=> 'W('w)); ('D('d) <=> 'E('e)); ('F('f) <=> 'R('r)); ('G('g) <=> 'T('t)); ('H('h) <=> 'T('t)); ('A('a) /\\ 'S('s) /\\ 'D('d) /\\ 'F('f) /\\ 'G('g) /\\ 'H('h)) |- 'R('x)",
        List((a, q), (s, w), (d, e), (f, r), (g, t), (h, y)),
        Y5
      )
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2, forms, ltf) =>
      val prem = introduceSequent(stmt1)
      LeftSubstIff(forms, ltf)(prem)(stmt2)
    }
  }

  // right substiff
  test("Tactic Tests: Right SubstIff") {
    val q = FOLParser.parseFormula("'Q('q)")
    val w = FOLParser.parseFormula("'W('w)")
    val e = FOLParser.parseFormula("'E('e)")
    val r = FOLParser.parseFormula("'R('r)")
    val t = FOLParser.parseFormula("'T('t)")
    val y = FOLParser.parseFormula("'Y('y)")
    val a = FOLParser.parseFormula("'A('a)")
    val s = FOLParser.parseFormula("'S('s)")
    val d = FOLParser.parseFormula("'D('d)")
    val f = FOLParser.parseFormula("'F('f)")
    val g = FOLParser.parseFormula("'G('g)")
    val h = FOLParser.parseFormula("'H('h)")
    val z = VariableFormulaLabel("z")
    val x = VariableFormulaLabel("x")
    val c = VariableFormulaLabel("c")
    val v = VariableFormulaLabel("v")
    val b = VariableFormulaLabel("b")
    val n = VariableFormulaLabel("n")
    val Y1 = LambdaFormulaFormula(Seq(z), z /\ w /\ e /\ r /\ t /\ y)
    val Y2 = LambdaFormulaFormula(Seq(z, x), z /\ x /\ e /\ r /\ t /\ y)
    val Y5 = LambdaFormulaFormula(Seq(z, x, c, v, b, n), z /\ x /\ c /\ v /\ b /\ n)

    val correct = List(
      (
        "'P('x) |- 'R('x); ('Q('q) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y))",
        "'P('x); ('A('a) <=> 'Q('q)) |- 'R('x); ('A('a) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y))",
        List((a, q)),
        Y1
      ),
      (
        "'P('x) |- 'R('x); ('Q('q) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y))",
        "'P('x); ('A('a) <=> 'Q('q)) |- 'R('x); ('A('a) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y))",
        List((a, q)),
        Y1
      ),
      (
        "'P('x) |- 'R('x); ('Q('q) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y))",
        "'P('x); ('A('a) <=> 'Q('q)); ('S('s) <=> 'W('w)) |- 'R('x); ('A('a) /\\ 'S('s) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y))",
        List((a, q), (s, w)),
        Y2
      ),
      (
        "'P('q) |- 'R('x); ('Q('q) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y))",
        "'P('q); ('A('a) <=> 'Q('q)); ('S('s) <=> 'W('w)); ('D('d) <=> 'E('e)); ('F('f) <=> 'R('r)); ('G('g) <=> 'T('t)); ('H('h) <=> 'Y('y)) |- 'R('x); ('A('a) /\\ 'S('s) /\\ 'D('d) /\\ 'F('f) /\\ 'G('g) /\\ 'H('h))",
        List((a, q), (s, w), (d, e), (f, r), (g, t), (h, y)),
        Y5
      ),
      ( // check for appropriate renaming during substitution inside quantifiers
        "|- ¬¬∧(∀'y_1. ¬(∀'y. ¬('y = 'y_1)))",
        "('z = 'y) |- ¬¬∧(∀'y_1. ¬(∀'y. ¬('y = 'y_1)))",
        List((FOLParser.parseFormula("'z = 'y"), top())),
        lambda(x, FOLParser.parseFormula("¬¬∧(∀'y_1. ¬(∀'y_2. ¬('y_2 = 'y_1)))"))
      )
    )

    val incorrect = List(
      ("'P('x) |- 'R('x); ('Q('q) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y))", "'P('x) |- 'R('x); ('Q('q) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y))", List((a, q)), Y1),
      ("'P('x) |- 'R('x); ('Q('q) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y))", "'P('x) |- 'R('x); ('A('a) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y))", List((a, q)), Y1),
      (
        "'P('x) |- 'R('x); ('Q('q) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y))",
        "'P('x); ('A('a) <=> 'W('w)) |- 'R('x); ('A('a) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y))",
        List((a, q)),
        Y1
      ),
      (
        "'P('x) |- 'R('x); ('Q('q) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y))",
        "'P('x); ('A('a) <=> 'Q('q)); 'S('x) |- 'R('x); ('A('a) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y))",
        List((a, q)),
        Y1
      ),
      (
        "'P('x) |- 'R('x); ('Q('q) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y))",
        "'P('x); ('A('a) <=> 'Q('q)); 'S('x) |- 'R('x); ('A('a) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y))",
        List((a, q)),
        Y1
      ),
      (
        "'P('x) |- 'R('x); ('Q('q) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y))",
        "'P('x); ('A('a) <=> 'Q('q)) |- 'S('x); 'R('x); ('A('a) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y))",
        List((a, q)),
        Y1
      ),
      (
        "'P('q) |- 'R('x); ('Q('q) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y))",
        "'P('q); ('A('a) <=> 'Q('q)); ('S('s) <=> 'W('w)); ('D('d) <=> 'E('e)); ('F('f) <=> 'R('r)); ('G('g) <=> 'T('t)); ('H('h) <=> 'T('t)) |- 'R('x); ('A('a) /\\ 'S('s) /\\ 'D('d) /\\ 'F('f) /\\ 'G('g) /\\ 'H('h))",
        List((a, q), (s, w), (d, e), (f, r), (g, t), (h, t)),
        Y5
      ),
      (
        "'P('q) |- 'R('x); ('Q('q) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y))",
        "'P('q); ('A('a) <=> 'Q('q)); ('S('s) <=> 'W('w)); ('D('d) <=> 'E('e)); ('F('f) <=> 'R('r)); ('G('g) <=> 'T('t)); ('H('h) <=> 'T('t)) |- 'R('x); ('A('a) /\\ 'S('s) /\\ 'D('d) /\\ 'F('f) /\\ 'G('g) /\\ 'H('h))",
        List((a, q), (s, w), (d, e), (f, r), (g, t), (h, t)),
        Y5
      ),
      (
        "'P('q) |- 'R('x); ('Q('q) /\\ 'W('w) /\\ 'E('e) /\\ 'R('r) /\\ 'T('t) /\\ 'Y('y))",
        "'P('q); ('A('a) <=> 'Q('q)); ('S('s) <=> 'W('w)); ('D('d) <=> 'E('e)); ('F('f) <=> 'R('r)); ('G('g) <=> 'T('t)); ('H('h) <=> 'T('t)) |- 'R('x); ('A('a) /\\ 'S('s) /\\ 'D('d) /\\ 'F('f) /\\ 'G('g) /\\ 'H('h))",
        List((a, q), (s, w), (d, e), (f, r), (g, t), (h, y)),
        Y5
      )
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2, forms, ltf) =>
      val prem = introduceSequent(stmt1)
      RightSubstIff(forms, ltf)(prem)(stmt2)
    }
  }

  // instfunschema
  test("Tactic Tests: InstFunSchema") {
    val x = variable
    val y = variable
    val f = SchematicFunctionLabel("f", 1)
    val h = SchematicFunctionLabel("h", 2)
    val g = function(2)
    val Y = LambdaTermTerm(Seq(x), x)
    val Z = LambdaTermTerm(Seq(x, y), g(x, y))

    val correct = List(
      ("'P('x); 'f('x) = 'y |- 'R('y)", "'P('x); ('x = 'y) |- 'R('y)", Map[SchematicTermLabel, LambdaTermTerm](f -> Y)),
      ("'P('x); 'Q('f('x)) |- 'R('y)", "'P('x); 'Q('x) |- 'R('y)", Map[SchematicTermLabel, LambdaTermTerm](f -> Y)),
      ("'P('x); 'Q('h('x, 'y)) |- 'R('y)", "'P('x); 'Q('g('x, 'y)) |- 'R('y)", Map[SchematicTermLabel, LambdaTermTerm](h -> Z)),
      ("'P('h('y, 'y)); 'Q('h('x, 'y)) |- 'R('y)", "'P('g('y, 'y)); 'Q('g('x, 'y)) |- 'R('y)", Map[SchematicTermLabel, LambdaTermTerm](h -> Z)),
      ("'P('x); 'Q('g('x, 'y)) |- 'R('y)", "'P('x); 'Q('g('x, 'y)) |- 'R('y)", Map[SchematicTermLabel, LambdaTermTerm](h -> Z)),
      ("'P('x); 'Q('g('x, 'y)) |- 'R('y); 'f('x) = 'y", "'P('x); 'Q('g('x, 'y)) |- 'R('y); 'x = 'y", Map[SchematicTermLabel, LambdaTermTerm](h -> Z, f -> Y))
    )

    val incorrect = List(
      ("'P('x); 'f('x) = 'y |- 'R('y)", "'P('x); !('x = 'y) |- 'R('y)", Map[SchematicTermLabel, LambdaTermTerm](f -> Y)),
      ("'P('x); 'Q('f('x)) |- 'R('y)", "'P('x); 'Q('y) |- 'R('y)", Map[SchematicTermLabel, LambdaTermTerm](f -> Y)),
      ("'P('x); 'Q('h('x, 'y)) |- 'R('y)", "'P('x); 'Q('h('x, 'y)) |- 'R('y)", Map[SchematicTermLabel, LambdaTermTerm](h -> Z)),
      ("'P('h('y, 'y)); 'Q('h('x, 'y)) |- 'R('y)", "'P('g('y, 'y)); 'Q('g('y, 'y)) |- 'R('y)", Map[SchematicTermLabel, LambdaTermTerm](h -> Z)),
      ("'P('x); 'Q('g('x, 'y)) |- 'R('y)", "'P('x); 'Q('h('x, 'y)) |- 'R('y)", Map[SchematicTermLabel, LambdaTermTerm](h -> Z)),
      ("'P('x); 'Q('g('x, 'y)) |- 'R('y); 'f('x) = 'y", "'P('x); 'Q('g('x, 'y)) |- 'R('y); 'x = 'z", Map[SchematicTermLabel, LambdaTermTerm](h -> Z, f -> Y)),
      ("'P('x); 'Q('g('x, 'y)) |- 'R('y); 'f('x) = 'y", "'P('x); 'Q('g('x, 'y)) |- 'R('y); 'x = 'y", Map[SchematicTermLabel, LambdaTermTerm](h -> Z))
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2, termMap) =>
      val prem = introduceSequent(stmt1)
      InstFunSchema(termMap)(prem)(stmt2)
    }
  }

  // instpredschema
  test("Tactic Tests: InstPredSchema") {
    val x = variable
    val y = variable
    val f = SchematicPredicateLabel("f", 1)
    val h = SchematicPredicateLabel("h", 2)
    val g = predicate(2)
    val Y = LambdaTermFormula(Seq(x), x === x)
    val Z = LambdaTermFormula(Seq(x, y), g(x, y))

    val correct = List(
      ("'P('x); 'f('x) |- 'R('y)", "'P('x); ('x = 'x) |- 'R('y)", Map[SchematicVarOrPredLabel, LambdaTermFormula](f -> Y)),
      ("'P('x); 'Q('x) /\\ 'f('x) |- 'R('y)", "'P('x); 'Q('x) /\\ 'x = 'x |- 'R('y)", Map[SchematicVarOrPredLabel, LambdaTermFormula](f -> Y)),
      ("'P('x); 'h('x, 'y) |- 'R('y)", "'P('x); 'g('x, 'y) |- 'R('y)", Map[SchematicVarOrPredLabel, LambdaTermFormula](h -> Z)),
      ("'h('y, 'y); 'h('x, 'y) |- 'R('y)", "'g('y, 'y); 'g('x, 'y) |- 'R('y)", Map[SchematicVarOrPredLabel, LambdaTermFormula](h -> Z)),
      ("'P('x); 'g('x, 'y) |- 'R('y)", "'P('x); 'g('x, 'y) |- 'R('y)", Map[SchematicVarOrPredLabel, LambdaTermFormula](h -> Z)),
      ("'P('x); 'g('x, 'y) |- 'R('y); 'f('x)", "'P('x); 'g('x, 'y) |- 'R('y); 'x = 'x", Map[SchematicVarOrPredLabel, LambdaTermFormula](h -> Z, f -> Y))
    )

    val incorrect = List(
      ("'P('x); 'f('x) = 'y |- 'R('y)", "'P('x); !('x = 'y) |- 'R('y)", Map[SchematicVarOrPredLabel, LambdaTermFormula](f -> Y)),
      ("'P('x); 'f('x) |- 'R('y)", "'P('x); 'Q('y) |- 'R('y)", Map[SchematicVarOrPredLabel, LambdaTermFormula](f -> Y)),
      ("'P('x); 'h('x, 'y) |- 'R('y)", "'P('x); 'h('x, 'y) |- 'R('y)", Map[SchematicVarOrPredLabel, LambdaTermFormula](h -> Z)),
      ("'h('y, 'y); 'h('x, 'y) |- 'R('y)", "'g('y, 'y); 'g('y, 'y) |- 'R('y)", Map[SchematicVarOrPredLabel, LambdaTermFormula](h -> Z)),
      ("'P('x); 'g('x, 'y) |- 'R('y)", "'P('x); 'h('x, 'y) |- 'R('y)", Map[SchematicVarOrPredLabel, LambdaTermFormula](h -> Z)),
      ("'P('x); 'g('x, 'y) |- 'R('y); 'f('x)", "'P('x); 'g('x, 'y) |- 'R('y); 'x = 't", Map[SchematicVarOrPredLabel, LambdaTermFormula](h -> Z, f -> Y)),
      ("'P('x); 'g('x, 'y) |- 'R('y); 'f('x)", "'P('x); 'g('x, 'y) |- 'R('y); 'x = 'x", Map[SchematicVarOrPredLabel, LambdaTermFormula](h -> Z)),
      ("'P('x); 'g('x, 'y) |- 'R('y); 'f('x)", "'P('x); 'g('x, 'y) |- 'R('y)", Map[SchematicVarOrPredLabel, LambdaTermFormula](h -> Z, f -> Y))
    )

    testTacticCases(correct, incorrect) { (stmt1, stmt2, termMap) =>
      val prem = introduceSequent(stmt1)
      InstPredSchema(termMap)(prem)(stmt2)
    }
  }
   */
}
