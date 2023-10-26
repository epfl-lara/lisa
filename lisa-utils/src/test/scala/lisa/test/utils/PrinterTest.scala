package lisa.test.utils

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.utils.FOLParser
import lisa.utils.KernelHelpers.{_, given}
import lisa.utils.parsing.*
import lisa.utils.{_, given}
import org.scalatest.funsuite.AnyFunSuite

import scala.language.adhocExtensions

class PrinterTest extends AnyFunSuite with TestUtils {

  test("Minimal parenthesization") {
    assert(FOLParser.printFormula(ConnectorFormula(And, Seq(a, b))) == "a ∧ b")
    assert(FOLParser.printFormula(ConnectorFormula(And, Seq(ConnectorFormula(And, Seq(a, b)), c))) == "a ∧ b ∧ c")
    assert(FOLParser.printFormula(ConnectorFormula(And, Seq(a, ConnectorFormula(And, Seq(b, c))))) == "a ∧ (b ∧ c)")
    assert(FOLParser.printFormula(ConnectorFormula(Or, Seq(a, ConnectorFormula(And, Seq(b, c))))) == "a ∨ b ∧ c")
    assert(FOLParser.printFormula(ConnectorFormula(Or, Seq(ConnectorFormula(And, Seq(a, b)), c))) == "a ∧ b ∨ c")
    assert(FOLParser.printFormula(ConnectorFormula(And, Seq(ConnectorFormula(Or, Seq(a, b)), c))) == "(a ∨ b) ∧ c")
    assert(FOLParser.printFormula(ConnectorFormula(And, Seq(a, ConnectorFormula(Or, Seq(b, c))))) == "a ∧ (b ∨ c)")

    assert(FOLParser.printFormula(ConnectorFormula(Neg, Seq(a))) == "¬a")
    assert(FOLParser.printFormula(ConnectorFormula(Neg, Seq(ConnectorFormula(Neg, Seq(a))))) == "¬¬a")
    assert(FOLParser.printFormula(ConnectorFormula(Neg, Seq(ConnectorFormula(Neg, Seq(ConnectorFormula(And, Seq(a, b))))))) == "¬¬(a ∧ b)")
    assert(
      FOLParser.printFormula(ConnectorFormula(And, Seq(ConnectorFormula(Neg, Seq(a)), ConnectorFormula(And, Seq(ConnectorFormula(Neg, Seq(b)), ConnectorFormula(Neg, Seq(c))))))) == "¬a ∧ (¬b ∧ ¬c)"
    )
    assert(
      FOLParser.printFormula(ConnectorFormula(And, Seq(ConnectorFormula(And, Seq(ConnectorFormula(Neg, Seq(a)), ConnectorFormula(Neg, Seq(b)))), ConnectorFormula(Neg, Seq(c))))) == "¬a ∧ ¬b ∧ ¬c"
    )

    assert(FOLParser.printFormula(ConnectorFormula(And, Seq(a, PredicateFormula(equality, Seq(x, x))))) == "a ∧ 'x = 'x")

    assert(FOLParser.printFormula(BinderFormula(Forall, x, PredicateFormula(equality, Seq(x, x)))) == "∀'x. 'x = 'x")
    assert(FOLParser.printFormula(ConnectorFormula(And, Seq(a, BinderFormula(Forall, x, PredicateFormula(equality, Seq(x, x)))))) == "a ∧ (∀'x. 'x = 'x)")
    assert(FOLParser.printFormula(ConnectorFormula(And, Seq(BinderFormula(Forall, x, b), a))) == "(∀'x. b) ∧ a")
    assert(FOLParser.printFormula(ConnectorFormula(And, Seq(ConnectorFormula(And, Seq(a, BinderFormula(Forall, x, b))), a))) == "a ∧ (∀'x. b) ∧ a")
    assert(FOLParser.printFormula(ConnectorFormula(Or, Seq(ConnectorFormula(And, Seq(a, BinderFormula(Forall, x, b))), a))) == "a ∧ (∀'x. b) ∨ a")

    assert(FOLParser.printFormula(BinderFormula(Forall, x, BinderFormula(Exists, y, BinderFormula(ExistsOne, z, a)))) == "∀'x. ∃'y. ∃!'z. a")

    assert(FOLParser.printFormula(PredicateFormula(ConstantPredicateLabel("f", 3), Seq(x, y, z))) == "f('x, 'y, 'z)")
  }

  test("constant") {
    assert(FOLParser.printTerm(Term(cx, Seq())) == "x")
  }

  test("variable") {
    assert(FOLParser.printTerm(VariableTerm(x)) == "'x")
  }

  test("constant function application") {
    assert(FOLParser.printTerm(Term(f1, Seq(cx))) == "f(x)")
    assert(FOLParser.printTerm(Term(f2, Seq(cx, cy))) == "f(x, y)")
    assert(FOLParser.printTerm(Term(f3, Seq(cx, cy, cz))) == "f(x, y, z)")

    assert(FOLParser.printTerm(Term(f1, Seq(x))) == "f('x)")
    assert(FOLParser.printTerm(Term(f2, Seq(x, y))) == "f('x, 'y)")
    assert(FOLParser.printTerm(Term(f3, Seq(x, y, z))) == "f('x, 'y, 'z)")
  }

  test("schematic function application") {
    assert(FOLParser.printTerm(Term(sf1, Seq(cx))) == "'f(x)")
    assert(FOLParser.printTerm(Term(sf2, Seq(cx, cy))) == "'f(x, y)")
    assert(FOLParser.printTerm(Term(sf3, Seq(cx, cy, cz))) == "'f(x, y, z)")

    assert(FOLParser.printTerm(Term(sf1, Seq(x))) == "'f('x)")
    assert(FOLParser.printTerm(Term(sf2, Seq(x, y))) == "'f('x, 'y)")
    assert(FOLParser.printTerm(Term(sf3, Seq(x, y, z))) == "'f('x, 'y, 'z)")
  }

  test("nested function application") {
    assert(FOLParser.printTerm(Term(sf2, Seq(Term(sf1, Seq(x)), y))) == "'f('f('x), 'y)")
  }

  test("0-ary predicate") {
    assert(FOLParser.printFormula(PredicateFormula(ConstantPredicateLabel("a", 0), Seq())) == "a")
  }

  test("predicate application") {
    assert(FOLParser.printFormula(PredicateFormula(ConstantPredicateLabel("p", 3), Seq(cx, cy, cz))) == "p(x, y, z)")
    assert(FOLParser.printFormula(PredicateFormula(ConstantPredicateLabel("p", 3), Seq(x, y, z))) == "p('x, 'y, 'z)")
  }

  test("equality") {
    assert(FOLParser.printFormula(PredicateFormula(equality, Seq(cx, cx))) == "x = x")
    assert(FOLParser.printFormula(ConnectorFormula(And, Seq(a, PredicateFormula(equality, Seq(x, x))))) == "a ∧ 'x = 'x")
  }

  test("toplevel connectors") {
    assert(FOLParser.printFormula(ConnectorFormula(Implies, Seq(a, b))) == "a ⇒ b")
    assert(FOLParser.printFormula(ConnectorFormula(Iff, Seq(a, b))) == "a ⇔ b")
  }

  test("unicode connectors") {
    assert(FOLParser.printFormula(ConnectorFormula(Neg, Seq(a))) == "¬a")
    assert(FOLParser.printFormula(ConnectorFormula(And, Seq(a, b))) == "a ∧ b")
    assert(FOLParser.printFormula(ConnectorFormula(Or, Seq(a, b))) == "a ∨ b")
  }

  test("connector associativity") {
    assert(FOLParser.printFormula(ConnectorFormula(And, Seq(ConnectorFormula(And, Seq(a, b)), c))) == "a ∧ b ∧ c")
    assert(FOLParser.printFormula(ConnectorFormula(Or, Seq(ConnectorFormula(Or, Seq(a, b)), c))) == "a ∨ b ∨ c")
  }

  test("and/or of 1 argument") {
    assert(FOLParser.printFormula(ConnectorFormula(And, Seq(a))) == "∧(a)")
    assert(FOLParser.printFormula(ConnectorFormula(Or, Seq(a))) == "∨(a)")

    assert(FOLParser.printFormula(ConnectorFormula(Implies, Seq(ConnectorFormula(Or, Seq(a)), ConnectorFormula(And, Seq(a))))) == "∨(a) ⇒ ∧(a)")
    assert(FOLParser.printFormula(ConnectorFormula(Implies, Seq(a, a))) == "a ⇒ a")
    assert(FOLParser.printFormula(BinderFormula(Forall, x, ConnectorFormula(Or, Seq(a)))) == "∀'x. ∨(a)")
  }

  test("connectors of >2 arguments") {
    assert(FOLParser.printFormula(ConnectorFormula(And, Seq(a, b, c))) == "a ∧ b ∧ c")
    assert(FOLParser.printFormula(ConnectorFormula(Or, Seq(a, b, c))) == "a ∨ b ∨ c")

    assert(FOLParser.printFormula(ConnectorFormula(And, Seq(a, b, c, a))) == "a ∧ b ∧ c ∧ a")
    assert(FOLParser.printFormula(ConnectorFormula(Or, Seq(a, b, c, b))) == "a ∨ b ∨ c ∨ b")

    assert(FOLParser.printFormula(ConnectorFormula(Or, Seq(ConnectorFormula(And, Seq(a, b, c)), ConnectorFormula(And, Seq(c, b, a))))) == "a ∧ b ∧ c ∨ c ∧ b ∧ a")
  }

  test("connectors with no arguments") {
    assert(FOLParser.printFormula(ConnectorFormula(And, Seq())) == "⊤")
    assert(FOLParser.printFormula(ConnectorFormula(Or, Seq())) == "⊥")
  }

  test("connector priority") {
    // a ∨ (b ∧ c)
    assert(FOLParser.printFormula(ConnectorFormula(Or, Seq(a, ConnectorFormula(And, Seq(b, c))))) == "a ∨ b ∧ c")
    // (a ∧ b) ∨ c
    assert(FOLParser.printFormula(ConnectorFormula(Or, Seq(ConnectorFormula(And, Seq(a, b)), c))) == "a ∧ b ∨ c")

    // (a ∧ b) => c
    assert(FOLParser.printFormula(ConnectorFormula(Implies, Seq(ConnectorFormula(And, Seq(a, b)), c))) == "a ∧ b ⇒ c")
    // a => (b ∧ c)
    assert(FOLParser.printFormula(ConnectorFormula(Implies, Seq(a, ConnectorFormula(And, Seq(b, c))))) == "a ⇒ b ∧ c")
    // (a ∨ b) => c
    assert(FOLParser.printFormula(ConnectorFormula(Implies, Seq(ConnectorFormula(Or, Seq(a, b)), c))) == "a ∨ b ⇒ c")
    // a => (b ∨ c)
    assert(FOLParser.printFormula(ConnectorFormula(Implies, Seq(a, ConnectorFormula(Or, Seq(b, c))))) == "a ⇒ b ∨ c")

    // (a ∧ b) <=> c
    assert(FOLParser.printFormula(ConnectorFormula(Iff, Seq(ConnectorFormula(And, Seq(a, b)), c))) == "a ∧ b ⇔ c")
    // a <=> (b ∧ c)
    assert(FOLParser.printFormula(ConnectorFormula(Iff, Seq(a, ConnectorFormula(And, Seq(b, c))))) == "a ⇔ b ∧ c")
    // (a ∨ b) <=> c
    assert(FOLParser.printFormula(ConnectorFormula(Iff, Seq(ConnectorFormula(Or, Seq(a, b)), c))) == "a ∨ b ⇔ c")
    // a <=> (b ∨ c)
    assert(FOLParser.printFormula(ConnectorFormula(Iff, Seq(a, ConnectorFormula(Or, Seq(b, c))))) == "a ⇔ b ∨ c")
  }

  test("connector parentheses") {
    assert(FOLParser.printFormula(ConnectorFormula(And, Seq(ConnectorFormula(Or, Seq(a, b)), c))) == "(a ∨ b) ∧ c")
    assert(FOLParser.printFormula(ConnectorFormula(And, Seq(a, ConnectorFormula(Or, Seq(b, c))))) == "a ∧ (b ∨ c)")
  }

  test("schematic connectors") {
    assert(FOLParser.printFormula(sc1(p(x))) == "?c(p('x))")
    assert(FOLParser.printFormula(iff(sc1(p(x)), sc2(p(y), p(y)))) == "?c(p('x)) ⇔ ?c(p('y), p('y))")
  }

  test("quantifiers") {
    assert(FOLParser.printFormula(BinderFormula(Forall, VariableLabel("x"), PredicateFormula(ConstantPredicateLabel("p", 0), Seq()))) == "∀'x. p")
    assert(FOLParser.printFormula(BinderFormula(Exists, VariableLabel("x"), PredicateFormula(ConstantPredicateLabel("p", 0), Seq()))) == "∃'x. p")
    assert(FOLParser.printFormula(BinderFormula(ExistsOne, VariableLabel("x"), PredicateFormula(ConstantPredicateLabel("p", 0), Seq()))) == "∃!'x. p")
  }

  test("nested quantifiers") {
    assert(FOLParser.printFormula(BinderFormula(Forall, x, BinderFormula(Exists, y, BinderFormula(ExistsOne, z, a)))) == "∀'x. ∃'y. ∃!'z. a")
  }

  test("quantifier parentheses") {
    assert(FOLParser.printFormula(BinderFormula(Forall, x, ConnectorFormula(And, Seq(b, a)))) == "∀'x. b ∧ a")
    assert(
      FOLParser.printFormula(
        BinderFormula(
          Forall,
          x,
          ConnectorFormula(And, Seq(PredicateFormula(ConstantPredicateLabel("p", 1), Seq(x)), PredicateFormula(ConstantPredicateLabel("q", 1), Seq(x))))
        )
      ) == "∀'x. p('x) ∧ q('x)"
    )

    assert(FOLParser.printFormula(ConnectorFormula(And, Seq(BinderFormula(Forall, x, b), a))) == "(∀'x. b) ∧ a")

    assert(
      FOLParser.printFormula(
        ConnectorFormula(
          And,
          Seq(
            BinderFormula(Forall, VariableLabel("x"), PredicateFormula(ConstantPredicateLabel("p", 1), Seq(x))),
            PredicateFormula(ConstantPredicateLabel("q", 1), Seq(x))
          )
        )
      ) == "(∀'x. p('x)) ∧ q('x)"
    )

    assert(FOLParser.printFormula(ConnectorFormula(Or, Seq(ConnectorFormula(And, Seq(a, BinderFormula(Forall, x, b))), a))) == "a ∧ (∀'x. b) ∨ a")
    assert(FOLParser.printFormula(ConnectorFormula(And, Seq(ConnectorFormula(And, Seq(a, BinderFormula(Forall, x, b))), a))) == "a ∧ (∀'x. b) ∧ a")
  }

  test("complex formulas with connectors") {
    assert(FOLParser.printFormula(ConnectorFormula(Neg, Seq(ConnectorFormula(Or, Seq(a, b))))) == "¬(a ∨ b)")
    assert(FOLParser.printFormula(ConnectorFormula(Neg, Seq(ConnectorFormula(Neg, Seq(a))))) == "¬¬a")
    assert(FOLParser.printFormula(ConnectorFormula(Neg, Seq(ConnectorFormula(Neg, Seq(ConnectorFormula(And, Seq(a, b))))))) == "¬¬(a ∧ b)")
    assert(
      FOLParser.printFormula(ConnectorFormula(And, Seq(ConnectorFormula(And, Seq(ConnectorFormula(Neg, Seq(a)), ConnectorFormula(Neg, Seq(b)))), ConnectorFormula(Neg, Seq(c))))) == "¬a ∧ ¬b ∧ ¬c"
    )
  }

  test("complex formulas") {
    assert(FOLParser.printFormula(BinderFormula(Forall, x, PredicateFormula(equality, Seq(x, x)))) == "∀'x. 'x = 'x")
  }

  test("sequent") {
    val forallEq = BinderFormula(Forall, x, PredicateFormula(equality, Seq(x, x)))
    assert(FOLParser.printSequent(Sequent(Set(), Set(forallEq))) == "⊢ ∀'x. 'x = 'x")
    assert(FOLParser.printSequent(Sequent(Set(forallEq), Set(forallEq))) == "∀'x. 'x = 'x ⊢ ∀'x. 'x = 'x")
    val existsXEq = BinderFormula(Exists, x, PredicateFormula(equality, Seq(x, x)))
    assert(FOLParser.printSequent(Sequent(Set(forallEq), Set(existsXEq))) == "∀'x. 'x = 'x ⊢ ∃'x. 'x = 'x")
  }

  // warning: this test might be flaky because formula order is not fixed in sequents but fixed in the string representation
  test("sequent with multiple formulas") {
    val forallEq = BinderFormula(Forall, x, PredicateFormula(equality, Seq(x, x)))
    val existsXEq = BinderFormula(Exists, x, PredicateFormula(equality, Seq(x, x)))
    val existsYEq = BinderFormula(Exists, y, PredicateFormula(equality, Seq(y, y)))
    assert(
      FOLParser.printSequent(Sequent(Set(forallEq), Set(existsYEq, existsXEq))) == "∀'x. 'x = 'x ⊢ ∃'y. 'y = 'y; " +
        "∃'x. 'x = 'x"
    )
    assert(
      FOLParser.printSequent(Sequent(Set(forallEq, PredicateFormula(ConstantPredicateLabel("p", 0), Seq())), Set(existsYEq, existsXEq))) == "∀'x. 'x = 'x; p ⊢ ∃'y. 'y = 'y; ∃'x. 'x = 'x"
    )
  }

  // warning: this test might be flaky because formula order is not fixed in sequents but fixed in the string representation
  test("sequents from Mapping and SetTheory") {
    val va = VariableLabel("a")
    val leftAndRight = BinderFormula(ExistsOne, x, PredicateFormula(sPhi2, Seq(x, va)))
    assert(FOLParser.printSequent(Sequent(Set(leftAndRight), Set(leftAndRight))) == "∃!'x. 'phi('x, 'a) ⊢ ∃!'x. 'phi('x, 'a)")

    assert(
      FOLParser.printSequent(
        Sequent(
          Set(BinderFormula(Forall, x, ConnectorFormula(Iff, Seq(x === x1, sPhi1(x))))),
          Set((z === sf1(x1)) ==> exists(x, (z === sf1(x)) /\ sPhi1(x)))
        )
      ) == "∀'x. 'x = 'x1 ⇔ 'phi('x) ⊢ 'z = 'f('x1) ⇒ (∃'x. 'z = 'f('x) ∧ 'phi('x))"
    )
    assert(
      FOLParser.printSequent(
        exists(x1, forall(x, (x === x1) <=> (sPhi1(x)))) |- exists(
          z1,
          forall(z, (z === z1) <=> exists(x, (z === sf1(x)) /\ sPhi1(x)))
        )
      ) == "∃'x1. ∀'x. 'x = 'x1 ⇔ 'phi('x) ⊢ ∃'z1. ∀'z. 'z = 'z1 ⇔ (∃'x. 'z = 'f('x) ∧ 'phi('x))"
    )
    assert(FOLParser.printSequent((() |- (x === x) \/ (x === y))) == "⊢ 'x = 'x ∨ 'x = 'y")
    assert(
      FOLParser.printSequent(
        Set(
          (x === x) \/ (x === y),
          ((x === x) \/ (x === y)) <=> ((x === xPrime) \/ (x === yPrime))
        ) |- (x === xPrime) \/ (x === yPrime)
      ) == "'x = 'x ∨ 'x = 'y; 'x = 'x ∨ 'x = 'y ⇔ 'x = 'x' ∨ 'x = 'y' ⊢ 'x = 'x' ∨ 'x = 'y'"
    )
  }

  test("infix predicates") {
    val in = ConstantPredicateLabel("∊", 2)
    val prefixIn = ConstantPredicateLabel("elem", 2)
    val parser = Parser(SynonymInfoBuilder().addSynonyms(prefixIn.id, in.id).build, in.id :: Nil, Nil)
    assert(parser.printFormula(PredicateFormula(in, Seq(cx, cy))) == "x ∊ y")
    assert(parser.printFormula(PredicateFormula(in, Seq(x, y))) == "'x ∊ 'y")
    assert(parser.printFormula(ConnectorFormula(And, Seq(PredicateFormula(in, Seq(x, y)), a))) == "'x ∊ 'y ∧ a")
    assert(parser.printFormula(ConnectorFormula(Or, Seq(a, PredicateFormula(in, Seq(x, y))))) == "a ∨ 'x ∊ 'y")

    assert(parser.printFormula(PredicateFormula(prefixIn, Seq(cx, cy))) == "x ∊ y")
    assert(parser.printFormula(PredicateFormula(prefixIn, Seq(x, y))) == "'x ∊ 'y")
    assert(parser.printFormula(ConnectorFormula(And, Seq(PredicateFormula(prefixIn, Seq(x, y)), a))) == "'x ∊ 'y ∧ a")
    assert(parser.printFormula(ConnectorFormula(Or, Seq(a, PredicateFormula(prefixIn, Seq(x, y))))) == "a ∨ 'x ∊ 'y")
  }

  test("infix functions") {
    val parser = Parser(SynonymInfoBuilder().addSynonyms(plus.id, "+").build, Nil, ("+", Associativity.Left) :: Nil)
    assert(parser.printTerm(Term(plus, Seq(cx, cy))) == "x + y")
    assert(parser.printTerm(Term(plus, Seq(Term(plus, Seq(cx, cy)), cz))) == "x + y + z")
  }
  /*
  test("mix of infix functions and infix predicates") {
    val parser = Parser(SynonymInfoBuilder().addSynonyms(in.id, "∊").addSynonyms(plus.id, "+").build, "∊" :: Nil, ("+", Associativity.Left) :: Nil)
    assert(parser.printFormula(PredicateFormula(in, Seq(Term(plus, Seq(cx, cy)), cz))) == "x + y ∊ z")
    assert(
      parser.printFormula(
        ConnectorFormula(
          And,
          Seq(ConnectorFormula(And, Seq(PredicateFormula(in, Seq(cx, cy)), PredicateFormula(in, Seq(cx, cz)))), PredicateFormula(in, Seq(Term(plus, Seq(cx, cy)), cz)))
        )
      ) == "x ∊ y ∧ x ∊ z ∧ x + y ∊ z"
    )

  }*/
}
