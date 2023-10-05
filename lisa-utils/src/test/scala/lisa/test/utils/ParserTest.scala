package lisa.test.utils

import lisa.kernel.fol.FOL._
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.utils.FOLParser
import lisa.utils.KernelHelpers.{_, given}
import lisa.utils.parsing.*
import lisa.utils.{_, given}
import org.scalatest.funsuite.AnyFunSuite

class ParserTest extends AnyFunSuite with TestUtils {
  test("constant") {
    assert(FOLParser.parseTerm("x") == Term(cx, Seq()))
  }

  test("variable") {
    assert(FOLParser.parseTerm("'x") == VariableTerm(x))
  }

  test("constant function application") {
    assert(FOLParser.parseTerm("f()") == Term(f0, Seq()))
    assert(FOLParser.parseTerm("f(x)") == Term(f1, Seq(cx)))
    assert(FOLParser.parseTerm("f(x, y)") == Term(f2, Seq(cx, cy)))
    assert(FOLParser.parseTerm("f(x, y, z)") == Term(f3, Seq(cx, cy, cz)))

    assert(FOLParser.parseTerm("f('x)") == Term(f1, Seq(x)))
    assert(FOLParser.parseTerm("f('x, 'y)") == Term(f2, Seq(x, y)))
    assert(FOLParser.parseTerm("f('x, 'y, 'z)") == Term(f3, Seq(x, y, z)))
  }

  test("schematic function application") {
    // FOLParser.parseTerm("?f()") -- schematic functions of 0 arguments do not exist, those are variables
    assert(FOLParser.parseTerm("'f(x)") == Term(sf1, Seq(cx)))
    assert(FOLParser.parseTerm("'f(x, y)") == Term(sf2, Seq(cx, cy)))
    assert(FOLParser.parseTerm("'f(x, y, z)") == Term(sf3, Seq(cx, cy, cz)))

    assert(FOLParser.parseTerm("'f('x)") == Term(sf1, Seq(x)))
    assert(FOLParser.parseTerm("'f('x, 'y)") == Term(sf2, Seq(x, y)))
    assert(FOLParser.parseTerm("'f('x, 'y, 'z)") == Term(sf3, Seq(x, y, z)))
  }

  test("nested function application") {
    assert(FOLParser.parseTerm("'f('f('x), 'y)") == Term(sf2, Seq(Term(sf1, Seq(x)), y)))
  }

  test("0-ary predicate") {
    assert(FOLParser.parseFormula("a") == PredicateFormula(ConstantPredicateLabel("a", 0), Seq()))
    assert(FOLParser.parseFormula("a()") == PredicateFormula(ConstantPredicateLabel("a", 0), Seq()))
  }

  test("boolean constants") {
    assert(FOLParser.parseFormula("true") == True)
    assert(FOLParser.parseFormula("True") == True)
    assert(FOLParser.parseFormula("T") == True)
    assert(FOLParser.parseFormula("⊤") == True)

    assert(FOLParser.parseFormula("false") == False)
    assert(FOLParser.parseFormula("False") == False)
    assert(FOLParser.parseFormula("F") == False)
    assert(FOLParser.parseFormula("⊥") == False)
  }

  test("predicate application") {
    assert(FOLParser.parseFormula("p(x, y, z)") == PredicateFormula(ConstantPredicateLabel("p", 3), Seq(cx, cy, cz)))
    assert(FOLParser.parseFormula("p('x, 'y, 'z)") == PredicateFormula(ConstantPredicateLabel("p", 3), Seq(x, y, z)))
  }

  test("equality") {
    assert(FOLParser.parseFormula("(x = x)") == PredicateFormula(equality, Seq(cx, cx)))
    assert(FOLParser.parseFormula("x = x") == PredicateFormula(equality, Seq(cx, cx)))
    assert(FOLParser.parseFormula("a ∧ ('x = 'x)") == ConnectorFormula(And, Seq(a, PredicateFormula(equality, Seq(x, x)))))
  }

  test("unicode connectors") {
    assert(FOLParser.parseFormula("¬a") == ConnectorFormula(Neg, Seq(a)))
    assert(FOLParser.parseFormula("a ∧ b") == ConnectorFormula(And, Seq(a, b)))
    assert(FOLParser.parseFormula("a ∨ b") == ConnectorFormula(Or, Seq(a, b)))
    assert(FOLParser.parseFormula("a ⇒ b") == ConnectorFormula(Implies, Seq(a, b)))
    assert(FOLParser.parseFormula("a ⇔ b") == ConnectorFormula(Iff, Seq(a, b)))
    assert(FOLParser.parseFormula("a ⇔ b") == ConnectorFormula(Iff, Seq(a, b)))
  }

  test("ascii connectors") {
    assert(FOLParser.parseFormula("!a") == ConnectorFormula(Neg, Seq(a)))
    assert(FOLParser.parseFormula("a /\\ b") == ConnectorFormula(And, Seq(a, b)))
    assert(FOLParser.parseFormula("a \\/ b") == ConnectorFormula(Or, Seq(a, b)))
    assert(FOLParser.parseFormula("a => b") == ConnectorFormula(Implies, Seq(a, b)))
    assert(FOLParser.parseFormula("a ==> b") == ConnectorFormula(Implies, Seq(a, b)))
    assert(FOLParser.parseFormula("a <=> b") == ConnectorFormula(Iff, Seq(a, b)))
  }

  test("connector associativity") {
    assert(FOLParser.parseFormula("a ∧ b ∧ c") == ConnectorFormula(And, Seq(ConnectorFormula(And, Seq(a, b)), c)))
    assert(FOLParser.parseFormula("a ∨ b ∨ c") == ConnectorFormula(Or, Seq(ConnectorFormula(Or, Seq(a, b)), c)))
  }

  test("connector priority") {
    // a ∨ (b ∧ c)
    assert(FOLParser.parseFormula("a ∨ b ∧ c") == ConnectorFormula(Or, Seq(a, ConnectorFormula(And, Seq(b, c)))))
    // (a ∧ b) ∨ c
    assert(FOLParser.parseFormula("a ∧ b ∨ c") == ConnectorFormula(Or, Seq(ConnectorFormula(And, Seq(a, b)), c)))

    // (a ∧ b) => c
    assert(FOLParser.parseFormula("a ∧ b => c") == ConnectorFormula(Implies, Seq(ConnectorFormula(And, Seq(a, b)), c)))
    // a => (b ∧ c)
    assert(FOLParser.parseFormula("a => b ∧ c") == ConnectorFormula(Implies, Seq(a, ConnectorFormula(And, Seq(b, c)))))
    // (a ∨ b) => c
    assert(FOLParser.parseFormula("a ∨ b => c") == ConnectorFormula(Implies, Seq(ConnectorFormula(Or, Seq(a, b)), c)))
    // a => (b ∨ c)
    assert(FOLParser.parseFormula("a => b ∨ c") == ConnectorFormula(Implies, Seq(a, ConnectorFormula(Or, Seq(b, c)))))

    // (a ∧ b) <=> c
    assert(FOLParser.parseFormula("a ∧ b <=> c") == ConnectorFormula(Iff, Seq(ConnectorFormula(And, Seq(a, b)), c)))
    // a <=> (b ∧ c)
    assert(FOLParser.parseFormula("a <=> b ∧ c") == ConnectorFormula(Iff, Seq(a, ConnectorFormula(And, Seq(b, c)))))
    // (a ∨ b) <=> c
    assert(FOLParser.parseFormula("a ∨ b <=> c") == ConnectorFormula(Iff, Seq(ConnectorFormula(Or, Seq(a, b)), c)))
    // a <=> (b ∨ c)
    assert(FOLParser.parseFormula("a <=> b ∨ c") == ConnectorFormula(Iff, Seq(a, ConnectorFormula(Or, Seq(b, c)))))
  }

  test("connector parentheses") {
    assert(FOLParser.parseFormula("(a ∨ b) ∧ c") == ConnectorFormula(And, Seq(ConnectorFormula(Or, Seq(a, b)), c)))
    assert(FOLParser.parseFormula("a ∧ (b ∨ c)") == ConnectorFormula(And, Seq(a, ConnectorFormula(Or, Seq(b, c)))))
  }

  test("schematic connectors") {
    assert(FOLParser.parseFormula("?c(p(x), p(y))") == ConnectorFormula(sc2, Seq(p(cx), p(cy))))
    assert(FOLParser.parseFormula("?c('phi('x)) <=> ?c('phi('y))") == iff(sc1(sPhi1(x)), sc1(sPhi1(y))))
    assert(FOLParser.parseFormula("?c(p(x), p(x)) /\\ ?c(p(y), p(y))") == and(sc2(p(cx), p(cx)), sc2(p(cy), p(cy))))
  }

  test("quantifiers") {
    assert(FOLParser.parseFormula("∀ 'x. (p)") == BinderFormula(Forall, VariableLabel("x"), PredicateFormula(ConstantPredicateLabel("p", 0), Seq())))
    assert(FOLParser.parseFormula("∃ 'x. (p)") == BinderFormula(Exists, VariableLabel("x"), PredicateFormula(ConstantPredicateLabel("p", 0), Seq())))
    assert(FOLParser.parseFormula("∃! 'x. (p)") == BinderFormula(ExistsOne, VariableLabel("x"), PredicateFormula(ConstantPredicateLabel("p", 0), Seq())))

    assert(FOLParser.parseFormula("∀ 'x. p") == BinderFormula(Forall, VariableLabel("x"), PredicateFormula(ConstantPredicateLabel("p", 0), Seq())))
    assert(FOLParser.parseFormula("∃ 'x. p") == BinderFormula(Exists, VariableLabel("x"), PredicateFormula(ConstantPredicateLabel("p", 0), Seq())))
    assert(FOLParser.parseFormula("∃! 'x. p") == BinderFormula(ExistsOne, VariableLabel("x"), PredicateFormula(ConstantPredicateLabel("p", 0), Seq())))
  }

  test("nested quantifiers") {
    assert(FOLParser.parseFormula("∀x. ∃y. ∃!z. a") == BinderFormula(Forall, x, BinderFormula(Exists, y, BinderFormula(ExistsOne, z, a))))
  }

  test("quantifier parentheses") {
    assert(FOLParser.parseFormula("∀x. b ∧ a") == BinderFormula(Forall, x, ConnectorFormula(And, Seq(b, a))))
    assert(
      FOLParser.parseFormula("∀ 'x. p('x) ∧ q('x)") == BinderFormula(
        Forall,
        x,
        ConnectorFormula(And, Seq(PredicateFormula(ConstantPredicateLabel("p", 1), Seq(x)), PredicateFormula(ConstantPredicateLabel("q", 1), Seq(x))))
      )
    )

    assert(FOLParser.parseFormula("(∀x. b) ∧ a") == ConnectorFormula(And, Seq(BinderFormula(Forall, x, b), a)))

    assert(
      FOLParser.parseFormula("(∀ 'x. p('x)) ∧ q('x)") == ConnectorFormula(
        And,
        Seq(
          BinderFormula(Forall, VariableLabel("x"), PredicateFormula(ConstantPredicateLabel("p", 1), Seq(x))),
          PredicateFormula(ConstantPredicateLabel("q", 1), Seq(x))
        )
      )
    )

    assert(FOLParser.parseFormula("a ∧ (∀x. b) ∨ a") == ConnectorFormula(Or, Seq(ConnectorFormula(And, Seq(a, BinderFormula(Forall, x, b))), a)))
    assert(FOLParser.parseFormula("(a ∧ (∀x. b)) ∧ a") == ConnectorFormula(And, Seq(ConnectorFormula(And, Seq(a, BinderFormula(Forall, x, b))), a)))
  }

  test("complex formulas with connectors") {
    assert(FOLParser.parseFormula("¬(a ∨ b)") == ConnectorFormula(Neg, Seq(ConnectorFormula(Or, Seq(a, b)))))
    assert(FOLParser.parseFormula("¬(¬a)") == ConnectorFormula(Neg, Seq(ConnectorFormula(Neg, Seq(a)))))
    assert(FOLParser.parseFormula("¬¬a") == ConnectorFormula(Neg, Seq(ConnectorFormula(Neg, Seq(a)))))
    assert(FOLParser.parseFormula("¬¬(a ∧ b)") == ConnectorFormula(Neg, Seq(ConnectorFormula(Neg, Seq(ConnectorFormula(And, Seq(a, b)))))))
    assert(
      FOLParser.parseFormula("¬a ∧ ¬b ∧ ¬c") == ConnectorFormula(And, Seq(ConnectorFormula(And, Seq(ConnectorFormula(Neg, Seq(a)), ConnectorFormula(Neg, Seq(b)))), ConnectorFormula(Neg, Seq(c))))
    )
  }

  test("complex formulas") {
    assert(FOLParser.parseFormula("∀x. 'x = 'x") == BinderFormula(Forall, x, PredicateFormula(equality, Seq(x, x))))
  }

  test("parser limitations") {
    // TODO: more specific error reporting check
    assertThrows[ParserException](FOLParser.parseFormula("(a ∧ ∀x. b) ∧ a"))

  }

  test("sequent") {
    val forallEq = BinderFormula(Forall, x, PredicateFormula(equality, Seq(x, x)))
    assert(FOLParser.parseSequent("∀x. 'x = 'x") == Sequent(Set(), Set(forallEq)))
    assert(FOLParser.parseSequent("⊢ ∀x. 'x = 'x") == Sequent(Set(), Set(forallEq)))
    assert(FOLParser.parseSequent("∀x. 'x = 'x ⊢ ∀x. 'x = 'x") == Sequent(Set(forallEq), Set(forallEq)))
    val existsXEq = BinderFormula(Exists, x, PredicateFormula(equality, Seq(x, x)))
    assert(FOLParser.parseSequent("∀x. 'x = 'x ⊢ ∃x. 'x = 'x") == Sequent(Set(forallEq), Set(existsXEq)))
    val existsYEq = BinderFormula(Exists, y, PredicateFormula(equality, Seq(y, y)))
    assert(FOLParser.parseSequent("∀x. 'x = 'x ⊢ ∃x. 'x = 'x; ∃y. 'y = 'y") == Sequent(Set(forallEq), Set(existsYEq, existsXEq)))
    assert(
      FOLParser.parseSequent("p ; ∀x. 'x = 'x ⊢ ∃x. 'x = 'x; ∃y. 'y = 'y") ==
        Sequent(Set(forallEq, PredicateFormula(ConstantPredicateLabel("p", 0), Seq())), Set(existsYEq, existsXEq))
    )
  }

  test("sequents from Mapping and SetTheory") {
    val va = VariableLabel("a")
    val leftAndRight = BinderFormula(ExistsOne, x, PredicateFormula(sPhi2, Seq(x, va)))
    assert(FOLParser.parseSequent("∃!x. 'phi('x, 'a) ⊢ ∃!x. 'phi('x, 'a)") == Sequent(Set(leftAndRight), Set(leftAndRight)))

    assert(
      FOLParser.parseSequent("∀x. ('x = 'x1) ⇔ 'phi('x) ⊢ ('z = 'f('x1)) ⇒ (∃x. ('z = 'f('x)) ∧ 'phi('x))") == Sequent(
        Set(BinderFormula(Forall, x, ConnectorFormula(Iff, Seq(x === x1, sPhi1(x))))),
        Set((z === sf1(x1)) ==> exists(x, (z === sf1(x)) /\ sPhi1(x)))
      )
    )
    assert(
      FOLParser.parseSequent("∃x1. ∀x. ('x = 'x1) ⇔ 'phi('x) ⊢ ∃z1. ∀z. ('z = 'z1) ⇔ (∃x. ('z = 'f('x)) ∧ 'phi('x))") == (exists(x1, forall(x, (x === x1) <=> (sPhi1(x)))) |- exists(
        z1,
        forall(z, (z === z1) <=> exists(x, (z === sf1(x)) /\ sPhi1(x)))
      ))
    )
    assert(FOLParser.parseSequent("⊢ ('x = 'x) ∨ ('x = 'y)") == (() |- (x === x) \/ (x === y)))
    assert(
      FOLParser.parseSequent("('x = 'x) ∨ ('x = 'y); ('x = 'x) ∨ ('x = 'y) ⇔ ('x = 'x1) ∨ ('x = 'y1) ⊢ ('x = 'x1) ∨ ('x = 'y1)") == (Set(
        (x === x) \/ (x === y),
        ((x === x) \/ (x === y)) <=> ((x === x1) \/ (x === y1))
      ) |- (x === x1) \/ (x === y1))
    )
  }

  test("equivalent names") {
    val parser = Parser(SynonymInfoBuilder().addSynonyms(in.id, "∊").build, "∊" :: Nil, Nil)
    assert(parser.parseFormula("x∊y") == PredicateFormula(in, Seq(cx, cy)))
    assert(parser.parseFormula("x ∊ y") == PredicateFormula(in, Seq(cx, cy)))
    assert(parser.parseFormula("'x ∊ 'y") == PredicateFormula(in, Seq(x, y)))
    assert(parser.parseFormula("('x ∊ 'y) /\\ a") == ConnectorFormula(And, Seq(PredicateFormula(in, Seq(x, y)), a)))
    assert(parser.parseFormula("a \\/ ('x ∊ 'y)") == ConnectorFormula(Or, Seq(a, PredicateFormula(in, Seq(x, y)))))
  }

  test("infix functions") {
    val parser = Parser(SynonymInfoBuilder().addSynonyms(plus.id, "+").build, Nil, ("+", Associativity.Left) :: Nil)
    assert(parser.parseTerm("x + y") == Term(plus, Seq(cx, cy)))
    assert(parser.parseTerm("(x + y) + z") == Term(plus, Seq(Term(plus, Seq(cx, cy)), cz)))
  }

  test("mix of infix functions and infix predicates") {
    val parser = Parser(SynonymInfoBuilder().addSynonyms(in.id, "∊").addSynonyms(plus.id, "+").build, "∊" :: Nil, ("+", Associativity.Left) :: Nil)
    assert(parser.parseFormula("(x + y) ∊ z") == PredicateFormula(in, Seq(Term(plus, Seq(cx, cy)), cz)))
    assert(
      parser.parseFormula("x ∊ y /\\ x ∊ z /\\ (x + y) ∊ z") == ConnectorFormula(
        And,
        Seq(ConnectorFormula(And, Seq(PredicateFormula(in, Seq(cx, cy)), PredicateFormula(in, Seq(cx, cz)))), PredicateFormula(in, Seq(Term(plus, Seq(cx, cy)), cz)))
      )
    )
  }

  test("infix function and predicate priority") {
    val parser = Parser(SynonymInfoBuilder().addSynonyms(plus.id, "+").build, equality.id :: Nil, ("+", Associativity.Left) :: Nil)
    assert(parser.parseFormula("(x + y) = (y + x)") == PredicateFormula(equality, Seq(plus(cx, cy), plus(cy, cx))))
    assert(parser.parseFormula("x + y = y + x") == PredicateFormula(equality, Seq(plus(cx, cy), plus(cy, cx))))
  }

  test("parser exception: unexpected input") {
    try {
      FOLParser.parseFormula("f(x y)")
    } catch {
      case e: UnexpectedInputException => assert(e.getMessage.startsWith("""
          |f(x y)
          |    ^
          |Unexpected input""".stripMargin))
    }
  }

  test("parser exception: formula instead of term") {
    try {
      FOLParser.parseFormula("x = (a /\\ b)")
    } catch {
      case e: UnexpectedInputException =>
        assert(e.getMessage.startsWith("""
            |x = (a /\ b)
            |     ^^^^^^
            |Unexpected input: expected term""".stripMargin))
    }
  }
}
