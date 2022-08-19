package lisa.front

import org.scalatest.funsuite.AnyFunSuite

import scala.language.adhocExtensions

import lisa.front.parser.FrontReader
import lisa.front.printer.{FrontPositionedPrinter, FrontPrintStyle}

class ParserPrinterTests extends AnyFunSuite {
  test("formula parsing and printing (ASCII)") {
    Seq[String](
      "a",
      raw"a /\ b",
      raw"a /\ b \/ c => d <=> e",
      "a => b => c => d",
      "((a => b) => c) => d",
      "forall x. ?x = ?z",
      "f(a, b)",
      raw"(a \/ b) /\ c",
      raw"forall x, y. (?x = ?z) /\ (?x = ?y)",
      raw"??f(g({?x, {{}, ?y}}, {}), a, a /\ b)",
      "?s",
      "?f(?s, ?g(?x), t) = ?u",
      "exists x. forall y. ?x = ?y"
    ).foreach { s =>
      val formula = FrontReader.readFormula(s)
      val printed = FrontPositionedPrinter.prettyFormula(formula, symbols = FrontPrintStyle.Ascii)
      println(printed)
      assert(printed == s) // actual == expected
    }
  }


  test("sequent parsing and printing (ASCII)") {
    Seq[String](
      "|-",
      "|- a",
      "a |- b",
      "a; b |- c; d",
      raw"a /\ b; c \/ d |- e; f => g; h",
    ).foreach { s =>
      val sequent = FrontReader.readSequent(s)
      val printed = FrontPositionedPrinter.prettySequent(sequent, symbols = FrontPrintStyle.Ascii)
      //println(printed)
      assert(printed == s)
    }
  }

  test("partial sequent parsing and printing (ASCII)") {
    Seq[String](
      "|-",
      "|- a",
      "a |- b",
      "a; b |- c; d",
      "... |- a; b",
      "... |- ...",
      "a |- b; ...",
      "...; a |- b",
      "...; a |- b; ...",
      "...; a; b |- b; c; ...",
    ).foreach { s =>
      val sequent = FrontReader.readPartialSequent(s)
      val printed = FrontPositionedPrinter.prettyPartialSequent(sequent, symbols = FrontPrintStyle.Ascii)
      //println(printed)
      assert(printed == s)
    }
  }
}
