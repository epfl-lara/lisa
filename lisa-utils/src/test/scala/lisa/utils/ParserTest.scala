package lisa.utils

import lisa.kernel.fol.FOL.*
import org.scalatest.funsuite.AnyFunSuite

class ParserTest extends AnyFunSuite {

  val (a, b, c) = (ConstantPredicateLabel("a", 0), ConstantPredicateLabel("b", 0), ConstantPredicateLabel("c", 0))
  val (x, y, z) = (VariableLabel("x"), VariableLabel("y"), VariableLabel("z"))
  val (cx, cy, cz) = (ConstantFunctionLabel("x", 0), ConstantFunctionLabel("y", 0), ConstantFunctionLabel("z", 0))
  val (f0, f1, f2, f3) = (ConstantFunctionLabel("f", 0), ConstantFunctionLabel("f", 1), ConstantFunctionLabel("f", 2), ConstantFunctionLabel("f", 3))
  val (sf1, sf2, sf3) = (SchematicFunctionLabel("f", 1), SchematicFunctionLabel("f", 2), SchematicFunctionLabel("f", 3))

  given Conversion[PredicateLabel, PredicateFormula] = PredicateFormula(_, Seq.empty)

  given Conversion[ConstantFunctionLabel, FunctionTerm] = FunctionTerm(_, Seq())

  given Conversion[VariableLabel, VariableTerm] = VariableTerm.apply

  test("constant") {
    assert(Parser.parseTerm("x") == FunctionTerm(cx, Seq()))
  }

  test("variable") {
    assert(Parser.parseTerm("?x") == VariableTerm(x))
  }

  test("constant function application") {
    assert(Parser.parseTerm("f()") == FunctionTerm(f0, Seq()))
    assert(Parser.parseTerm("f(x)") == FunctionTerm(f1, Seq(cx)))
    assert(Parser.parseTerm("f(x, y)") == FunctionTerm(f2, Seq(cx, cy)))
    assert(Parser.parseTerm("f(x, y, z)") == FunctionTerm(f3, Seq(cx, cy, cz)))

    assert(Parser.parseTerm("f(?x)") == FunctionTerm(f1, Seq(x)))
    assert(Parser.parseTerm("f(?x, ?y)") == FunctionTerm(f2, Seq(x, y)))
    assert(Parser.parseTerm("f(?x, ?y, ?z)") == FunctionTerm(f3, Seq(x, y, z)))
  }

  test("schematic function application") {
    // Parser.parseTerm("?f()") -- schematic functions of 0 arguments do not exist, those are variables
    assert(Parser.parseTerm("?f(x)") == FunctionTerm(sf1, Seq(cx)))
    assert(Parser.parseTerm("?f(x, y)") == FunctionTerm(sf2, Seq(cx, cy)))
    assert(Parser.parseTerm("?f(x, y, z)") == FunctionTerm(sf3, Seq(cx, cy, cz)))

    assert(Parser.parseTerm("?f(?x)") == FunctionTerm(sf1, Seq(x)))
    assert(Parser.parseTerm("?f(?x, ?y)") == FunctionTerm(sf2, Seq(x, y)))
    assert(Parser.parseTerm("?f(?x, ?y, ?z)") == FunctionTerm(sf3, Seq(x, y, z)))
  }

  test("nested function application") {
    assert(Parser.parseTerm("?f(?f(?x), ?y)") == FunctionTerm(sf2, Seq(FunctionTerm(sf1, Seq(x)), y)))
  }

  test("0-ary predicate") {
    assert(Parser.parseFormula("a") == PredicateFormula(ConstantPredicateLabel("a", 0), Seq()))
    assert(Parser.parseFormula("a()") == PredicateFormula(ConstantPredicateLabel("a", 0), Seq()))
  }

  test("predicate application") {
    assert(Parser.parseFormula("p(x, y, z)") == PredicateFormula(ConstantPredicateLabel("p", 3), Seq(cx, cy, cz)))
    assert(Parser.parseFormula("p(?x, ?y, ?z)") == PredicateFormula(ConstantPredicateLabel("p", 3), Seq(x, y, z)))
  }

  test("equality") {
    assert(Parser.parseFormula("(x = x)") == PredicateFormula(equality, Seq(cx, cx)))
    assert(Parser.parseFormula("x = x") == PredicateFormula(equality, Seq(cx, cx)))
    assert(Parser.parseFormula("a ∧ (?x = ?x)") == ConnectorFormula(And, Seq(a, PredicateFormula(equality, Seq(x, x)))))
  }

  test("unicode connectors") {
    assert(Parser.parseFormula("¬a") == ConnectorFormula(Neg, Seq(a)))
    assert(Parser.parseFormula("a ∧ b") == ConnectorFormula(And, Seq(a, b)))
    assert(Parser.parseFormula("a ∨ b") == ConnectorFormula(Or, Seq(a, b)))
    assert(Parser.parseFormula("a ⇒ b") == ConnectorFormula(Implies, Seq(a, b)))
    assert(Parser.parseFormula("a ↔ b") == ConnectorFormula(Iff, Seq(a, b)))
  }

  test("ascii connectors") {
    assert(Parser.parseFormula("!a") == ConnectorFormula(Neg, Seq(a)))
    assert(Parser.parseFormula("a /\\ b") == ConnectorFormula(And, Seq(a, b)))
    assert(Parser.parseFormula("a \\/ b") == ConnectorFormula(Or, Seq(a, b)))
    assert(Parser.parseFormula("a => b") == ConnectorFormula(Implies, Seq(a, b)))
    assert(Parser.parseFormula("a ==> b") == ConnectorFormula(Implies, Seq(a, b)))
    assert(Parser.parseFormula("a <=> b") == ConnectorFormula(Iff, Seq(a, b)))
  }

  test("connector associativity") {
    assert(Parser.parseFormula("a ∧ b ∧ c") == ConnectorFormula(And, Seq(ConnectorFormula(And, Seq(a, b)), c)))
    assert(Parser.parseFormula("a ∨ b ∨ c") == ConnectorFormula(Or, Seq(ConnectorFormula(Or, Seq(a, b)), c)))
  }

  test("connector priority") {
    // a ∨ (b ∧ c)
    assert(Parser.parseFormula("a ∨ b ∧ c") == ConnectorFormula(Or, Seq(a, ConnectorFormula(And, Seq(b, c)))))
    // (a ∧ b) ∨ c
    assert(Parser.parseFormula("a ∧ b ∨ c") == ConnectorFormula(Or, Seq(ConnectorFormula(And, Seq(a, b)), c)))

    // (a ∧ b) => c
    assert(Parser.parseFormula("a ∧ b => c") == ConnectorFormula(Implies, Seq(ConnectorFormula(And, Seq(a, b)), c)))
    // a => (b ∧ c)
    assert(Parser.parseFormula("a => b ∧ c") == ConnectorFormula(Implies, Seq(a, ConnectorFormula(And, Seq(b, c)))))
    // (a ∨ b) => c
    assert(Parser.parseFormula("a ∨ b => c") == ConnectorFormula(Implies, Seq(ConnectorFormula(Or, Seq(a, b)), c)))
    // a => (b ∨ c)
    assert(Parser.parseFormula("a => b ∨ c") == ConnectorFormula(Implies, Seq(a, ConnectorFormula(Or, Seq(b, c)))))

    // (a ∧ b) <=> c
    assert(Parser.parseFormula("a ∧ b <=> c") == ConnectorFormula(Iff, Seq(ConnectorFormula(And, Seq(a, b)), c)))
    // a <=> (b ∧ c)
    assert(Parser.parseFormula("a <=> b ∧ c") == ConnectorFormula(Iff, Seq(a, ConnectorFormula(And, Seq(b, c)))))
    // (a ∨ b) <=> c
    assert(Parser.parseFormula("a ∨ b <=> c") == ConnectorFormula(Iff, Seq(ConnectorFormula(Or, Seq(a, b)), c)))
    // a <=> (b ∨ c)
    assert(Parser.parseFormula("a <=> b ∨ c") == ConnectorFormula(Iff, Seq(a, ConnectorFormula(Or, Seq(b, c)))))
  }

  test("connector parentheses") {
    assert(Parser.parseFormula("(a ∨ b) ∧ c") == ConnectorFormula(And, Seq(ConnectorFormula(Or, Seq(a, b)), c)))
    assert(Parser.parseFormula("a ∧ (b ∨ c)") == ConnectorFormula(And, Seq(a, ConnectorFormula(Or, Seq(b, c)))))
  }

  test("quantifiers") {
    assert(Parser.parseFormula("∀ ?x. (p)") == BinderFormula(Forall, VariableLabel("x"), PredicateFormula(ConstantPredicateLabel("p", 0), Seq())))
    assert(Parser.parseFormula("∃ ?x. (p)") == BinderFormula(Exists, VariableLabel("x"), PredicateFormula(ConstantPredicateLabel("p", 0), Seq())))
    assert(Parser.parseFormula("∃! ?x. (p)") == BinderFormula(ExistsOne, VariableLabel("x"), PredicateFormula(ConstantPredicateLabel("p", 0), Seq())))

    assert(Parser.parseFormula("∀ ?x. p") == BinderFormula(Forall, VariableLabel("x"), PredicateFormula(ConstantPredicateLabel("p", 0), Seq())))
    assert(Parser.parseFormula("∃ ?x. p") == BinderFormula(Exists, VariableLabel("x"), PredicateFormula(ConstantPredicateLabel("p", 0), Seq())))
    assert(Parser.parseFormula("∃! ?x. p") == BinderFormula(ExistsOne, VariableLabel("x"), PredicateFormula(ConstantPredicateLabel("p", 0), Seq())))
  }

  test("nested quantifiers") {
    assert(Parser.parseFormula("∀x. ∃y. ∃!z. a") == BinderFormula(Forall, x, BinderFormula(Exists, y, BinderFormula(ExistsOne, z, a))))
  }

  test("quantifier parentheses") {
    assert(Parser.parseFormula("∀x. b ∧ a") == BinderFormula(Forall, x, ConnectorFormula(And, Seq(b, a))))
    assert(
      Parser.parseFormula("∀ ?x. p(?x) ∧ q(?x)") == BinderFormula(
        Forall,
        x,
        ConnectorFormula(And, Seq(PredicateFormula(ConstantPredicateLabel("p", 1), Seq(x)), PredicateFormula(ConstantPredicateLabel("q", 1), Seq(x))))
      )
    )

    assert(Parser.parseFormula("(∀x. b) ∧ a") == ConnectorFormula(And, Seq(BinderFormula(Forall, x, b), a)))

    assert(
      Parser.parseFormula("(∀ ?x. p(?x)) ∧ q(?x)") == ConnectorFormula(
        And,
        Seq(
          BinderFormula(Forall, VariableLabel("x"), PredicateFormula(ConstantPredicateLabel("p", 1), Seq(x))),
          PredicateFormula(ConstantPredicateLabel("q", 1), Seq(x))
        )
      )
    )

    assert(Parser.parseFormula("a ∧ (∀x. b) ∨ a") == ConnectorFormula(Or, Seq(ConnectorFormula(And, Seq(a, BinderFormula(Forall, x, b))), a)))
    assert(Parser.parseFormula("(a ∧ (∀x. b)) ∧ a") == ConnectorFormula(And, Seq(ConnectorFormula(And, Seq(a, BinderFormula(Forall, x, b))), a)))
  }

  test("complex formulas with connectors") {
    assert(Parser.parseFormula("¬(a ∨ b)") == ConnectorFormula(Neg, Seq(ConnectorFormula(Or, Seq(a, b)))))
    assert(Parser.parseFormula("¬(¬a)") == ConnectorFormula(Neg, Seq(ConnectorFormula(Neg, Seq(a)))))
    assert(Parser.parseFormula("¬¬a") == ConnectorFormula(Neg, Seq(ConnectorFormula(Neg, Seq(a)))))
    assert(Parser.parseFormula("¬¬(a ∧ b)") == ConnectorFormula(Neg, Seq(ConnectorFormula(Neg, Seq(ConnectorFormula(And, Seq(a, b)))))))
    assert(Parser.parseFormula("¬a ∧ ¬b ∧ ¬c") == ConnectorFormula(And, Seq(ConnectorFormula(And, Seq(ConnectorFormula(Neg, Seq(a)), ConnectorFormula(Neg, Seq(b)))), ConnectorFormula(Neg, Seq(c)))))
  }

  test("complex formulas") {
    assert(Parser.parseFormula("∀x. ?x = ?x") == BinderFormula(Forall, x, PredicateFormula(equality, Seq(x, x))))
  }

  test("parser limitations") {
    // TODO: more specific error reporting check
    assertThrows[Parser.ParserException](Parser.parseFormula("(a ∧ ∀x. b) ∧ a"))

  }

  test("sequent") {
    fail("not implemented")
  }

  test("sequents from Mapping proof") {
    fail("not implemented")
  }

  test("sequents from Peano proof") {
    fail("not implemented")
  }

}
