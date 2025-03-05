package lisa.utils

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.utils.KernelHelpers.{_, given}
import lisa.utils.{_, given}
import org.scalatest.funsuite.AnyFunSuite

import scala.language.adhocExtensions

/**
 * TODO: Port to TPTP-based printing
 */
class PrinterTest extends AnyFunSuite with TestUtils {
/*
  test("Minimal parenthesization") {
    assert((multiand(Seq(a, b))).repr == "a ∧ b")
    assert((multiand(Seq(multiand(Seq(a, b)), c))).repr == "a ∧ b ∧ c")
    assert((multiand(Seq(a, multiand(Seq(b, c))))).repr == "a ∧ (b ∧ c)")
    assert((multior(Seq(a, multiand(Seq(b, c))))).repr == "a ∨ b ∧ c")
    assert((multior(Seq(multiand(Seq(a, b)), c))).repr == "a ∧ b ∨ c")
    assert((multiand(Seq(multior(Seq(a, b)), c))).repr == "(a ∨ b) ∧ c")
    assert((multiand(Seq(a, multior(Seq(b, c))))).repr == "a ∧ (b ∨ c)")

    assert((!a).repr == "¬a")
    assert((!!a).repr == "¬¬a")
    assert((!!Seq(multiand(Seq(a, b))))).repr == "¬¬(a ∧ b)")
    assert(
      (multiand(Seq(!a, multiand(Seq(!b, !c))))).repr == "¬a ∧ (¬b ∧ ¬c)"
    )
    assert(
      (multiand(Seq(multiand(Seq(ConnectorFormula(Neg, Seq(a)), ConnectorFormula(Neg, Seq(b)))), ConnectorFormula(Neg, Seq(c))))).repr == "¬a ∧ ¬b ∧ ¬c"
    )

    assert((multiand(Seq(a, AtomicFormula(equality, Seq(x, x))))).repr == "a ∧ 'x = 'x")

    assert((BinderFormula(Forall, x, AtomicFormula(equality, Seq(x, x)))).repr == "∀'x. 'x = 'x")
    assert((multiand(Seq(a, BinderFormula(Forall, x, AtomicFormula(equality, Seq(x, x)))))).repr == "a ∧ (∀'x. 'x = 'x)")
    assert((multiand(Seq(BinderFormula(Forall, x, b), a))).repr == "(∀'x. b) ∧ a")
    assert((multiand(Seq(multiand(Seq(a, BinderFormula(Forall, x, b))), a))).repr == "a ∧ (∀'x. b) ∧ a")
    assert((multior(Seq(multiand(Seq(a, BinderFormula(Forall, x, b))), a))).repr == "a ∧ (∀'x. b) ∨ a")

    assert((BinderFormula(Forall, x, BinderFormula(Exists, y, BinderFormula(ExistsOne, z, a)))).repr == "∀'x. ∃'y. ∃!'z. a")

    assert((AtomicFormula(ConstantAtomicLabel("f", 3), Seq(x, y, z))).repr == "f('x, 'y, 'z)")
  }

  test("constant") {
    assert(FOLParser.printTerm(Ind(cx, Seq())) == "x")
  }

  test("variable") {
    assert(FOLParser.printTerm(VariableTerm(x)) == "'x")
  }

  test("constant function application") {
    assert(FOLParser.printTerm(Ind(f1, Seq(cx))) == "f(x)")
    assert(FOLParser.printTerm(Ind(f2, Seq(cx, cy))) == "f(x, y)")
    assert(FOLParser.printTerm(Ind(f3, Seq(cx, cy, cz))) == "f(x, y, z)")

    assert(FOLParser.printTerm(Ind(f1, Seq(x))) == "f('x)")
    assert(FOLParser.printTerm(Ind(f2, Seq(x, y))) == "f('x, 'y)")
    assert(FOLParser.printTerm(Ind(f3, Seq(x, y, z))) == "f('x, 'y, 'z)")
  }

  test("schematic function application") {
    assert(FOLParser.printTerm(Ind(sf1, Seq(cx))) == "'f(x)")
    assert(FOLParser.printTerm(Ind(sf2, Seq(cx, cy))) == "'f(x, y)")
    assert(FOLParser.printTerm(Ind(sf3, Seq(cx, cy, cz))) == "'f(x, y, z)")

    assert(FOLParser.printTerm(Ind(sf1, Seq(x))) == "'f('x)")
    assert(FOLParser.printTerm(Ind(sf2, Seq(x, y))) == "'f('x, 'y)")
    assert(FOLParser.printTerm(Ind(sf3, Seq(x, y, z))) == "'f('x, 'y, 'z)")
  }

  test("nested function application") {
    assert(FOLParser.printTerm(Ind(sf2, Seq(Ind(sf1, Seq(x)), y))) == "'f('f('x), 'y)")
  }

  test("0-ary predicate") {
    assert((AtomicFormula(ConstantAtomicLabel("a", 0), Seq())).repr == "a")
  }

  test("predicate application") {
    assert((AtomicFormula(ConstantAtomicLabel("p", 3), Seq(cx, cy, cz))).repr == "p(x, y, z)")
    assert((AtomicFormula(ConstantAtomicLabel("p", 3), Seq(x, y, z))).repr == "p('x, 'y, 'z)")
  }

  test("equality") {
    assert((AtomicFormula(equality, Seq(cx, cx))).repr == "x = x")
    assert((multiand(Seq(a, AtomicFormula(equality, Seq(x, x))))).repr == "a ∧ 'x = 'x")
  }

  test("toplevel connectors") {
    assert((ConnectorFormula(Implies, Seq(a, b))).repr == "a ⇒ b")
    assert((ConnectorFormula(Iff, Seq(a, b))).repr == "a ⇔ b")
  }

  test("unicode connectors") {
    assert((ConnectorFormula(Neg, Seq(a))).repr == "¬a")
    assert((multiand(Seq(a, b))).repr == "a ∧ b")
    assert((multior(Seq(a, b))).repr == "a ∨ b")
  }

  test("connector associativity") {
    assert((multiand(Seq(multiand(Seq(a, b)), c))).repr == "a ∧ b ∧ c")
    assert((multior(Seq(multior(Seq(a, b)), c))).repr == "a ∨ b ∨ c")
  }

  test("and/or of 1 argument") {
    assert((multiand(Seq(a))).repr == "∧(a)")
    assert((multior(Seq(a))).repr == "∨(a)")

    assert((ConnectorFormula(Implies, Seq(multior(Seq(a)), multiand(Seq(a))))).repr == "∨(a) ⇒ ∧(a)")
    assert((ConnectorFormula(Implies, Seq(a, a))).repr == "a ⇒ a")
    assert((BinderFormula(Forall, x, multior(Seq(a)))).repr == "∀'x. ∨(a)")
  }

  test("connectors of >2 arguments") {
    assert((multiand(Seq(a, b, c))).repr == "a ∧ b ∧ c")
    assert((multior(Seq(a, b, c))).repr == "a ∨ b ∨ c")

    assert((multiand(Seq(a, b, c, a))).repr == "a ∧ b ∧ c ∧ a")
    assert((multior(Seq(a, b, c, b))).repr == "a ∨ b ∨ c ∨ b")

    assert((multior(Seq(multiand(Seq(a, b, c)), multiand(Seq(c, b, a))))).repr == "a ∧ b ∧ c ∨ c ∧ b ∧ a")
  }

  test("connectors with no arguments") {
    assert((multiand(Seq())).repr == "⊤")
    assert((multior(Seq())).repr == "⊥")
  }

  test("connector priority") {
    // a ∨ (b ∧ c)
    assert((multior(Seq(a, multiand(Seq(b, c))))).repr == "a ∨ b ∧ c")
    // (a ∧ b) ∨ c
    assert((multior(Seq(multiand(Seq(a, b)), c))).repr == "a ∧ b ∨ c")

    // (a ∧ b) => c
    assert((ConnectorFormula(Implies, Seq(multiand(Seq(a, b)), c))).repr == "a ∧ b ⇒ c")
    // a => (b ∧ c)
    assert((ConnectorFormula(Implies, Seq(a, multiand(Seq(b, c))))).repr == "a ⇒ b ∧ c")
    // (a ∨ b) => c
    assert((ConnectorFormula(Implies, Seq(multior(Seq(a, b)), c))).repr == "a ∨ b ⇒ c")
    // a => (b ∨ c)
    assert((ConnectorFormula(Implies, Seq(a, multior(Seq(b, c))))).repr == "a ⇒ b ∨ c")

    // (a ∧ b) <=> c
    assert((ConnectorFormula(Iff, Seq(multiand(Seq(a, b)), c))).repr == "a ∧ b ⇔ c")
    // a <=> (b ∧ c)
    assert((ConnectorFormula(Iff, Seq(a, multiand(Seq(b, c))))).repr == "a ⇔ b ∧ c")
    // (a ∨ b) <=> c
    assert((ConnectorFormula(Iff, Seq(multior(Seq(a, b)), c))).repr == "a ∨ b ⇔ c")
    // a <=> (b ∨ c)
    assert((ConnectorFormula(Iff, Seq(a, multior(Seq(b, c))))).repr == "a ⇔ b ∨ c")
  }

  test("connector parentheses") {
    assert((multiand(Seq(multior(Seq(a, b)), c))).repr == "(a ∨ b) ∧ c")
    assert((multiand(Seq(a, multior(Seq(b, c))))).repr == "a ∧ (b ∨ c)")
  }

  test("schematic connectors") {
    assert((sc1(p(x))).repr == "?c(p('x))")
    assert((iff(sc1(p(x)), sc2(p(y), p(y)))).repr == "?c(p('x)) ⇔ ?c(p('y), p('y))")
  }

  test("quantifiers") {
    assert((BinderFormula(Forall, VariableLabel("x"), AtomicFormula(ConstantAtomicLabel("p", 0), Seq()))).repr == "∀'x. p")
    assert((BinderFormula(Exists, VariableLabel("x"), AtomicFormula(ConstantAtomicLabel("p", 0), Seq()))).repr == "∃'x. p")
    assert((BinderFormula(ExistsOne, VariableLabel("x"), AtomicFormula(ConstantAtomicLabel("p", 0), Seq()))).repr == "∃!'x. p")
  }

  test("nested quantifiers") {
    assert((BinderFormula(Forall, x, BinderFormula(Exists, y, BinderFormula(ExistsOne, z, a)))).repr == "∀'x. ∃'y. ∃!'z. a")
  }

  test("quantifier parentheses") {
    assert((BinderFormula(Forall, x, multiand(Seq(b, a)))).repr == "∀'x. b ∧ a")
    assert(
      FOLParser.printFormula(
        BinderFormula(
          Forall,
          x,
          multiand(Seq(AtomicFormula(ConstantAtomicLabel("p", 1), Seq(x)), AtomicFormula(ConstantAtomicLabel("q", 1), Seq(x))))
        )
      ) == "∀'x. p('x) ∧ q('x)"
    )

    assert((multiand(Seq(BinderFormula(Forall, x, b), a))).repr == "(∀'x. b) ∧ a")

    assert(
      FOLParser.printFormula(
        ConnectorFormula(
          And,
          Seq(
            BinderFormula(Forall, VariableLabel("x"), AtomicFormula(ConstantAtomicLabel("p", 1), Seq(x))),
            AtomicFormula(ConstantAtomicLabel("q", 1), Seq(x))
          )
        )
      ) == "(∀'x. p('x)) ∧ q('x)"
    )

    assert((multior(Seq(multiand(Seq(a, BinderFormula(Forall, x, b))), a))).repr == "a ∧ (∀'x. b) ∨ a")
    assert((multiand(Seq(multiand(Seq(a, BinderFormula(Forall, x, b))), a))).repr == "a ∧ (∀'x. b) ∧ a")
  }

  test("complex formulas with connectors") {
    assert((ConnectorFormula(Neg, Seq(multior(Seq(a, b))))).repr == "¬(a ∨ b)")
    assert((ConnectorFormula(Neg, Seq(ConnectorFormula(Neg, Seq(a))))).repr == "¬¬a")
    assert((ConnectorFormula(Neg, Seq(ConnectorFormula(Neg, Seq(multiand(Seq(a, b))))))).repr == "¬¬(a ∧ b)")
    assert(
      (multiand(Seq(multiand(Seq(ConnectorFormula(Neg, Seq(a)), ConnectorFormula(Neg, Seq(b)))), ConnectorFormula(Neg, Seq(c))))).repr == "¬a ∧ ¬b ∧ ¬c"
    )
  }

  test("complex formulas") {
    assert((BinderFormula(Forall, x, AtomicFormula(equality, Seq(x, x)))).repr == "∀'x. 'x = 'x")
  }

  test("sequent") {
    val forallEq = BinderFormula(Forall, x, AtomicFormula(equality, Seq(x, x)))
    assert(FOLParser.printSequent(Sequent(Set(), Set(forallEq))) == "⊢ ∀'x. 'x = 'x")
    assert(FOLParser.printSequent(Sequent(Set(forallEq), Set(forallEq))) == "∀'x. 'x = 'x ⊢ ∀'x. 'x = 'x")
    val existsXEq = BinderFormula(Exists, x, AtomicFormula(equality, Seq(x, x)))
    assert(FOLParser.printSequent(Sequent(Set(forallEq), Set(existsXEq))) == "∀'x. 'x = 'x ⊢ ∃'x. 'x = 'x")
  }

  // warning: this test might be flaky because formula order is not fixed in sequents but fixed in the string representation
  test("sequent with multiple formulas") {
    val forallEq = BinderFormula(Forall, x, AtomicFormula(equality, Seq(x, x)))
    val existsXEq = BinderFormula(Exists, x, AtomicFormula(equality, Seq(x, x)))
    val existsYEq = BinderFormula(Exists, y, AtomicFormula(equality, Seq(y, y)))
    assert(
      FOLParser.printSequent(Sequent(Set(forallEq), Set(existsYEq, existsXEq))) == "∀'x. 'x = 'x ⊢ ∃'y. 'y = 'y; " +
        "∃'x. 'x = 'x"
    )
    assert(
      FOLParser.printSequent(Sequent(Set(forallEq, AtomicFormula(ConstantAtomicLabel("p", 0), Seq())), Set(existsYEq, existsXEq))) == "∀'x. 'x = 'x; p ⊢ ∃'y. 'y = 'y; ∃'x. 'x = 'x"
    )
  }

  // warning: this test might be flaky because formula order is not fixed in sequents but fixed in the string representation
  test("sequents from Mapping and SetTheory") {
    val va = VariableLabel("a")
    val leftAndRight = BinderFormula(ExistsOne, x, AtomicFormula(sPhi2, Seq(x, va)))
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
    val in = ConstantAtomicLabel("∊", 2)
    val prefixIn = ConstantAtomicLabel("elem", 2)
    val parser = Parser(SynonymInfoBuilder().addSynonyms(prefixIn.id, in.id).build, in.id :: Nil, Nil)
    assert(parser.printFormula(AtomicFormula(in, Seq(cx, cy))) == "x ∊ y")
    assert(parser.printFormula(AtomicFormula(in, Seq(x, y))) == "'x ∊ 'y")
    assert(parser.printFormula(multiand(Seq(AtomicFormula(in, Seq(x, y)), a))) == "'x ∊ 'y ∧ a")
    assert(parser.printFormula(multior(Seq(a, AtomicFormula(in, Seq(x, y))))) == "a ∨ 'x ∊ 'y")

    assert(parser.printFormula(AtomicFormula(prefixIn, Seq(cx, cy))) == "x ∊ y")
    assert(parser.printFormula(AtomicFormula(prefixIn, Seq(x, y))) == "'x ∊ 'y")
    assert(parser.printFormula(multiand(Seq(AtomicFormula(prefixIn, Seq(x, y)), a))) == "'x ∊ 'y ∧ a")
    assert(parser.printFormula(multior(Seq(a, AtomicFormula(prefixIn, Seq(x, y))))) == "a ∨ 'x ∊ 'y")
  }

  test("infix functions") {
    val parser = Parser(SynonymInfoBuilder().addSynonyms(plus.id, "+").build, Nil, ("+", Associativity.Left) :: Nil)
    assert(parser.printTerm(Ind(plus, Seq(cx, cy))) == "x + y")
    assert(parser.printTerm(Ind(plus, Seq(Ind(plus, Seq(cx, cy)), cz))) == "x + y + z")
  }
  /*
  test("mix of infix functions and infix predicates") {
    val parser = Parser(SynonymInfoBuilder().addSynonyms(in.id, "∊").addSynonyms(plus.id, "+").build, "∊" :: Nil, ("+", Associativity.Left) :: Nil)
    assert(parser.printFormula(AtomicFormula(in, Seq(Ind(plus, Seq(cx, cy)), cz))) == "x + y ∊ z")
    assert(
      parser.printFormula(
        ConnectorFormula(
          And,
          Seq(multiand(Seq(AtomicFormula(in, Seq(cx, cy)), AtomicFormula(in, Seq(cx, cz)))), AtomicFormula(in, Seq(Ind(plus, Seq(cx, cy)), cz)))
        )
      ) == "x ∊ y ∧ x ∊ z ∧ x + y ∊ z"
    )

  }*/

  */
}
