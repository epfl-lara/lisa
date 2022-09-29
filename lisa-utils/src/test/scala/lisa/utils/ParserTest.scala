package lisa.utils

import lisa.kernel.fol.FOL._
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.utils.Helpers.*
import org.scalatest.funsuite.AnyFunSuite

class ParserTest extends AnyFunSuite with TestUtils {
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
    val forallEq = BinderFormula(Forall, x, PredicateFormula(equality, Seq(x, x)))
    assert(Parser.parseSequent("∀x. ?x = ?x") == Sequent(Set(), Set(forallEq)))
    assert(Parser.parseSequent("⊢ ∀x. ?x = ?x") == Sequent(Set(), Set(forallEq)))
    assert(Parser.parseSequent("∀x. ?x = ?x ⊢ ∀x. ?x = ?x") == Sequent(Set(forallEq), Set(forallEq)))
    val existsXEq = BinderFormula(Exists, x, PredicateFormula(equality, Seq(x, x)))
    assert(Parser.parseSequent("∀x. ?x = ?x ⊢ ∃x. ?x = ?x") == Sequent(Set(forallEq), Set(existsXEq)))
    val existsYEq = BinderFormula(Exists, y, PredicateFormula(equality, Seq(y, y)))
    assert(Parser.parseSequent("∀x. ?x = ?x ⊢ ∃x. ?x = ?x; ∃y. ?y = ?y") == Sequent(Set(forallEq), Set(existsYEq, existsXEq)))
    assert(
      Parser.parseSequent("p ; ∀x. ?x = ?x ⊢ ∃x. ?x = ?x; ∃y. ?y = ?y") ==
        Sequent(Set(forallEq, PredicateFormula(ConstantPredicateLabel("p", 0), Seq())), Set(existsYEq, existsXEq))
    )
  }

  test("sequents from Mapping and SetTheory") {
    val va = VariableLabel("a")
    val leftAndRight = BinderFormula(ExistsOne, x, PredicateFormula(sPhi2, Seq(x, va)))
    assert(Parser.parseSequent("∃!x. ?phi(?x, ?a) ⊢ ∃!x. ?phi(?x, ?a)") == Sequent(Set(leftAndRight), Set(leftAndRight)))

    assert(
      Parser.parseSequent("∀x. (?x = ?x1) ↔ ?phi(?x) ⊢ (?z = ?f(?x1)) ⇒ (∃x. (?z = ?f(?x)) ∧ ?phi(?x))") == Sequent(
        Set(BinderFormula(Forall, x, ConnectorFormula(Iff, Seq(x === x1, sPhi1(x))))),
        Set((z === sf1(x1)) ==> exists(x, (z === sf1(x)) /\ sPhi1(x)))
      )
    )
    assert(
      Parser.parseSequent("∃x1. ∀x. (?x = ?x1) ↔ ?phi(?x) ⊢ ∃z1. ∀z. (?z = ?z1) ↔ (∃x. (?z = ?f(?x)) ∧ ?phi(?x))") == (exists(x1, forall(x, (x === x1) <=> (sPhi1(x)))) |- exists(
        z1,
        forall(z, (z === z1) <=> exists(x, (z === sf1(x)) /\ sPhi1(x)))
      ))
    )
    assert(Parser.parseSequent("⊢ (?x = ?x) ∨ (?x = ?y)") == (() |- (x === x) \/ (x === y)))
    assert(
      Parser.parseSequent("(?x = ?x) ∨ (?x = ?y); (?x = ?x) ∨ (?x = ?y) ↔ (?x = ?x') ∨ (?x = ?y') ⊢ (?x = ?x') ∨ (?x = ?y')") == (Set(
        (x === x) \/ (x === y),
        ((x === x) \/ (x === y)) <=> ((x === xPrime) \/ (x === yPrime))
      ) |- (x === xPrime) \/ (x === yPrime))
    )
  }
}
