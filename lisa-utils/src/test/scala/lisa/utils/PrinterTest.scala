package lisa.utils

import lisa.kernel.fol.FOL.*
import lisa.utils.Printer.*
import lisa.utils.Parser
import org.scalatest.funsuite.AnyFunSuite

import scala.language.adhocExtensions

class PrinterTest extends AnyFunSuite {

  val (a, b, c) = (ConstantPredicateLabel("a", 0), ConstantPredicateLabel("b", 0), ConstantPredicateLabel("c", 0))
  val (x, y, z) = (VariableLabel("x"), VariableLabel("y"), VariableLabel("z"))

  given Conversion[PredicateLabel, PredicateFormula] = PredicateFormula(_, Seq.empty)
  given Conversion[VariableLabel, VariableTerm] = VariableTerm.apply

  test("Minimal parenthesization") {
    assert(Parser.printFormula(ConnectorFormula(And, Seq(a, b))) == "a ∧ b")
    assert(Parser.printFormula(ConnectorFormula(And, Seq(ConnectorFormula(And, Seq(a, b)), c))) == "a ∧ b ∧ c")
    assert(Parser.printFormula(ConnectorFormula(And, Seq(a, ConnectorFormula(And, Seq(b, c))))) == "a ∧ (b ∧ c)")
    assert(Parser.printFormula(ConnectorFormula(Or, Seq(a, ConnectorFormula(And, Seq(b, c))))) == "a ∨ (b ∧ c)")
    assert(Parser.printFormula(ConnectorFormula(Or, Seq(ConnectorFormula(And, Seq(a, b)), c))) == "a ∧ b ∨ c")
    assert(Parser.printFormula(ConnectorFormula(And, Seq(ConnectorFormula(Or, Seq(a, b)), c))) == "(a ∨ b) ∧ c")
    assert(Parser.printFormula(ConnectorFormula(And, Seq(a, ConnectorFormula(Or, Seq(b, c))))) == "a ∧ (b ∨ c)")

    assert(Parser.printFormula(ConnectorFormula(Neg, Seq(a))) == "¬a")
    assert(Parser.printFormula(ConnectorFormula(Neg, Seq(ConnectorFormula(Neg, Seq(a))))) == "¬¬a")
    assert(Parser.printFormula(ConnectorFormula(Neg, Seq(ConnectorFormula(Neg, Seq(ConnectorFormula(And, Seq(a, b))))))) == "¬¬(a ∧ b)")
    assert(Parser.printFormula(ConnectorFormula(And, Seq(ConnectorFormula(Neg, Seq(a)), ConnectorFormula(And, Seq(ConnectorFormula(Neg, Seq(b)), ConnectorFormula(Neg, Seq(c))))))) == "¬a ∧ (¬b ∧ ¬c)")
    assert(Parser.printFormula(ConnectorFormula(And, Seq(ConnectorFormula(And, Seq(ConnectorFormula(Neg, Seq(a)), ConnectorFormula(Neg, Seq(b)))), ConnectorFormula(Neg, Seq(c))))) == "¬a ∧ ¬b ∧ ¬c")

    assert(Parser.printFormula(ConnectorFormula(And, Seq(a, PredicateFormula(equality, Seq(x, x))))) == "a ∧ (?x = ?x)")

    assert(Parser.printFormula(BinderFormula(Forall, x, PredicateFormula(equality, Seq(x, x)))) == "∀x. ?x = ?x")
    assert(Parser.printFormula(ConnectorFormula(And, Seq(a, BinderFormula(Forall, x, PredicateFormula(equality, Seq(x, x)))))) == "a ∧ ∀x. ?x = ?x")
    assert(Parser.printFormula(ConnectorFormula(And, Seq(BinderFormula(Forall, x, b), a))) == "(∀x. b) ∧ a")
    assert(Parser.printFormula(ConnectorFormula(And, Seq(ConnectorFormula(And, Seq(a, BinderFormula(Forall, x, b))), a))) == "a ∧ (∀x. b) ∧ a")
    assert(Parser.printFormula(ConnectorFormula(Or, Seq(ConnectorFormula(And, Seq(a, BinderFormula(Forall, x, b))), a))) == "a ∧ (∀x. b) ∨ a")

    assert(Parser.printFormula(BinderFormula(Forall, x, BinderFormula(Exists, y, BinderFormula(ExistsOne, z, a)))) == "∀x. ∃y. ∃!z. a")

    assert(Parser.printFormula(PredicateFormula(ConstantPredicateLabel("f", 3), Seq(x, y, z))) == "f(?x, ?y, ?z)")
  }

}
