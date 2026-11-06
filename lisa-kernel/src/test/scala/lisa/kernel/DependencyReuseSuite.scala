package lisa.kernel

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.*
import org.scalatest.funsuite.AnyFunSuite

class DependencyReuseSuite extends AnyFunSuite:
  private given Theory = Theory.empty
  private def atom(i: Int): Expression = Variable(Identifier("dependency", i), Prop)
  private def statement(p: Expression): Sequent = Sequent(Set.empty, Set(p))
  private def conjunction(premises: Seq[Thm]): Thm =
    val terms = premises.map(_.right.head)
    RightAnd(statement(terms.reduce(and(_)(_))), premises, terms).toOption.get

  test("preserve a large axiom set by reference through unary rules"):
    val axioms = (0 until 32).map(i => Axiom(statement(atom(i))).toOption.get)
    val premise = conjunction(axioms)
    val result = Weakening(premise.statement, premise).toOption.get
    assert(result.axioms == axioms.map(_.statement).toSet)
    assert(result.axioms eq premise.axioms)
    assert(result.assumptions.isEmpty && !result.usesSorry)

  test("union overlapping dependency sets without dropping distinct axioms"):
    val axioms = (0 until 48).map(i => Axiom(statement(atom(i))).toOption.get)
    val result = conjunction(Seq(conjunction(axioms.take(32)), conjunction(axioms.drop(16))))
    assert(result.axioms == axioms.map(_.statement).toSet)

  test("retain proof holes and sorry separately from axioms, then discharge only the hole"):
    val hole = Assume(statement(atom(100))).toOption.get
    val sorry = Sorry(statement(atom(101))).toOption.get
    val axiom = Axiom(statement(atom(102))).toOption.get
    val premise = conjunction(Seq(hole, sorry, axiom))
    val result = Weakening(premise.statement, premise).toOption.get
    assert(result.axioms == Set(axiom.statement))
    assert(result.assumptions == Set(hole.statement))
    assert(result.assumptions eq premise.assumptions)
    assert(result.usesSorry)
    val discharged = Discharge(result, Axiom(hole.statement).toOption.get).toOption.get
    assert(discharged.assumptions.isEmpty)
    assert(discharged.axioms == Set(axiom.statement, hole.statement))
    assert(discharged.usesSorry)

  test("do not bypass theory checks when sharing dependencies"):
    val premise = Axiom(statement(atom(200))).toOption.get
    val result = Weakening(using Theory.empty)(premise.statement, premise)
    assert(result.left.exists(_.isInstanceOf[TheoryMismatch]))
