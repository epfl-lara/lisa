package lisa.kernel

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.RunningTheory.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SCProofChecker
import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.Helpers.{*, given}
import lisa.utils.Printer
import org.scalatest.funsuite.AnyFunSuite

import scala.language.adhocExtensions
import scala.util.Random

class ProofTests extends AnyFunSuite {
  val predicateVerifier = SCProofChecker.checkSCProof

  private val x = VariableLabel("x")
  private val y = VariableLabel("y")
  private val z = VariableLabel("z")
  private val a = PredicateFormula(ConstantPredicateLabel("A", 0), Seq())
  private val b = PredicateFormula(ConstantPredicateLabel("B", 0), Seq())
  private val fp = ConstantPredicateLabel("F", 1)
  val sT = VariableLabel("t")

  test("Verification of Pierce law") {
    val s0 = Hypothesis(a |- a, a)
    val s1 = Weakening(a |- Set(a, b), 0)
    val s2 = RightImplies(() |- Set(a, a ==> b), 1, a, b)
    val s3 = LeftImplies((a ==> b) ==> a |- a, 2, 0, a ==> b, a)
    val s4 = RightImplies(() |- (a ==> b) ==> a ==> a, 3, (a ==> b) ==> a, a)
    val ppl: SCProof = SCProof(IndexedSeq(s0, s1, s2, s3, s4))
    assert(predicateVerifier(ppl).isValid)
  }

  test("Verification of substitution") {
    val t0 = Hypothesis(fp(x) |- fp(x), fp(x))
    val t1 = RightSubstEq(Set(fp(x), x === y) |- fp(y), 0, List((x, y)), LambdaTermFormula(Seq(sT), fp(sT)))
    val pr = new SCProof(IndexedSeq(t0, t1))
    assert(predicateVerifier(pr).isValid)
  }

  test("Commutativity on a random large formula") {
    val k = 9
    val r = new Random()
    val vars = (0 until 1 << k).map(i => PredicateFormula(ConstantPredicateLabel(s"P$i", 0), Seq()))

    val pairs = vars.grouped(2)
    val sPairs = vars.grouped(2)
    var subformulas = pairs.map(p => or(p.head, p.last)).grouped(2)
    var subformulasSwapped = sPairs.map(p => if (r.nextBoolean()) or(p.head, p.last) else or(p.last, p.head)).grouped(2)
    for (i <- 1 until k) {
      val op = if (i % 2 == 0) or else and
      subformulas = subformulas.map(sf => op(sf.head, sf.last)).grouped(2)
      subformulasSwapped = subformulasSwapped.map(sf => if (r.nextBoolean()) op(sf.head, sf.last) else op(sf.last, sf.head)).grouped(2)
    }
    val orig = subformulas.next().head
    val swapped = subformulasSwapped.next().head
    val prf = SCProof(Vector(Hypothesis(Sequent(Set(orig), Set(orig)), orig), Rewrite(Sequent(Set(orig), Set(swapped)), 0)))
    assert(predicateVerifier(prf).isValid)
  }
}
