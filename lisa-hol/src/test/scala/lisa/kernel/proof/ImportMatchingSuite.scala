package lisa.kernel.proof

import lisa.kernel.fol.FOL._
import lisa.kernel.proof.SequentCalculus._
import org.scalatest.funsuite.AnyFunSuite

class ImportMatchingSuite extends AnyFunSuite:
  private val p = Variable(Identifier("matching-p"), Prop)
  private val q = Variable(Identifier("matching-q"), Prop)

  test("justify ordered, reordered, repeated and OL-equivalent imports without requiring a bijection"):
    val theory = new RunningTheory
    val axioms = Seq(theory.addAxiom("p", p).get, theory.addAxiom("q", q).get)
    val imports = axioms.map(theory.sequentFromJustification).toIndexedSeq
    val goal = imports.head
    val proof = SCProof(IndexedSeq(Restate(goal, -1)), imports)
    assert(theory.makeTheorem("ordered", goal, proof, axioms).isValid)
    assert(theory.makeTheorem("reordered", goal, proof, axioms.reverse).isValid)
    assert(!theory.makeTheorem("missing", goal, proof, axioms.take(1)).isValid)
    assert(!theory.makeTheorem("wrong", goal, proof, Seq(axioms.head, axioms.head)).isValid)
    assert(theory.makeTheorem("extra", goal, proof.copy(imports = imports.take(1)), axioms).isValid)
    assert(theory.makeTheorem("repeated", goal, proof.copy(imports = IndexedSeq(goal, goal)), axioms.take(1)).isValid)
    val equivalent = Sequent(Set.empty, Set(and(p)(top)))
    assert(theory.makeTheorem("equivalent", goal, proof.copy(imports = IndexedSeq(equivalent)), axioms.take(1)).isValid)

  test("still check the certificate, declared goal, language and sorry provenance after exact matching"):
    val theory = new RunningTheory
    val axiom = theory.addAxiom("p", p).get
    val imports = IndexedSeq(theory.sequentFromJustification(axiom))
    val goal = Sequent(Set.empty, Set(bot))
    val invalid = SCProof(IndexedSeq(Hypothesis(goal, p)), imports)
    assert(!theory.makeTheorem("invalid", goal, invalid, Seq(axiom)).isValid)
    val valid = SCProof(IndexedSeq(Restate(imports.head, -1)), imports)
    assert(!theory.makeTheorem("wrong-goal", goal, valid, Seq(axiom)).isValid)
    val foreign = Constant(Identifier("unregistered"), Prop)
    val foreignGoal = Sequent(Set(foreign), Set(foreign))
    assert(!theory.makeTheorem("foreign", foreignGoal, SCProof(IndexedSeq(Hypothesis(foreignGoal, foreign)), imports), Seq(axiom)).isValid)
    val admitted = SCProof(IndexedSeq(Sorry(goal)), imports)
    assert(theory.makeTheorem("admitted", goal, admitted, Seq(axiom)).isValid)
    assert(theory.getTheorem("admitted").get.withSorry)
    val inherited = SCProof(IndexedSeq(Restate(goal, -1)), IndexedSeq(goal))
    assert(theory.makeTheorem("inherited", goal, inherited, Seq(theory.getTheorem("admitted").get)).isValid)
    assert(theory.getTheorem("inherited").get.withSorry)
