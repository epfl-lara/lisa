package lisa.kernel

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.RunningTheory.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SCProofChecker
import lisa.kernel.proof.SCProofChecker.checkSCProof
import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.KernelHelpers.{_, given}
import lisa.utils.Printer
import org.scalatest.funsuite.AnyFunSuite

import scala.language.adhocExtensions
import scala.util.Random

class ProofTests extends AnyFunSuite {

  private val x = VariableLabel("x")
  private val y = VariableLabel("y")
  private val z = VariableLabel("z")
  val f = SchematicFunctionLabel("f", 1)
  val f2 = SchematicFunctionLabel("f2", 1)
  val g = ConstantFunctionLabel("g", 2)
  val g2 = SchematicFunctionLabel("g2", 2)
  private val a = AtomicFormula(ConstantAtomicLabel("A", 0), Seq())
  private val b = AtomicFormula(ConstantAtomicLabel("B", 0), Seq())
  private val fp = ConstantAtomicLabel("F", 1)
  val sT = VariableLabel("t")

  val X = VariableFormulaLabel("X")
  val P = SchematicPredicateLabel("f", 1)
  val P2 = SchematicPredicateLabel("f2", 1)
  val Q = ConstantAtomicLabel("g", 2)
  val Q2 = SchematicPredicateLabel("g2", 2)

  test("Verification of Pierce law") {
    val s0 = Hypothesis(a |- a, a)
    val s1 = Weakening(a |- Set(a, b), 0)
    val s2 = RightImplies(() |- Set(a, a ==> b), 1, a, b)
    val s3 = LeftImplies((a ==> b) ==> a |- a, 2, 0, a ==> b, a)
    val s4 = RightImplies(() |- (a ==> b) ==> a ==> a, 3, (a ==> b) ==> a, a)
    val ppl: SCProof = SCProof(IndexedSeq(s0, s1, s2, s3, s4))
    assert(checkSCProof(ppl).isValid)
  }

  test("Verification of LeftSubstEq") {
    {
      val t0 = Hypothesis(fp(x) |- fp(x), fp(x))
      val t1 = LeftSubstEq(Set(fp(y), x === y) |- fp(x), 0, List(((LambdaTermTerm(Seq(), x), LambdaTermTerm(Seq(), y)))), (Seq(sT), fp(sT)))
      assert(checkSCProof(SCProof(IndexedSeq(t0, t1))).isValid)
    }
    {
      val t0 = Hypothesis(exists(x, fp(f(x))) |- exists(x, fp(f(x))), exists(x, fp(f(x))))
      val t1 = LeftSubstEq(
        Set(exists(x, fp(g(x, x))), forall(y, f(y) === g(y, y))) |- exists(x, fp(f(x))),
        0,
        List((LambdaTermTerm(Seq(x), f(x)), LambdaTermTerm(Seq(x), g(x, x)))),
        (Seq(f2), exists(x, fp(f2(x))))
      )
      assert(checkSCProof(SCProof(IndexedSeq(t0, t1))).isValid)
    }
    {
      val t0 = Hypothesis(exists(x, fp(f(x))) |- exists(x, fp(f(x))), exists(x, fp(f(x))))
      val t1 = LeftSubstEq(
        Set(exists(x, fp(g(x, x))), forall(y, f(y) === g(y, y))) |- exists(x, fp(f(x))),
        0,
        List((LambdaTermTerm(Seq(y), f(y)), LambdaTermTerm(Seq(z), g(z, z)))),
        (Seq(f2), exists(x, fp(f2(x))))
      )
      assert(checkSCProof(SCProof(IndexedSeq(t0, t1))).isValid)
    }
    {
      val t0 = Hypothesis(exists(x, forall(y, fp(g(y, g(x, z))))) |- exists(x, forall(y, fp(g(y, g(x, z))))), exists(x, forall(y, fp(g(y, g(x, z))))))
      val t1 = LeftSubstEq(
        Set(exists(x, forall(y, fp(g(g(x, z), y)))), forall(y, forall(z, g(y, z) === g(z, y)))) |- exists(x, forall(y, fp(g(y, g(x, z))))),
        0,
        List((LambdaTermTerm(Seq(y, z), g(y, z)), LambdaTermTerm(Seq(y, z), g(z, y)))),
        (Seq(g2), exists(x, forall(y, fp(g2(y, g(x, z))))))
      )
      assert(checkSCProof(SCProof(IndexedSeq(t0, t1))).isValid)
    }
    {
      val t0 = Hypothesis(exists(x, forall(y, fp(g(y, g(x, z))))) |- exists(x, forall(y, fp(g(y, g(x, z))))), exists(x, forall(y, fp(g(y, g(x, z))))))
      val t1 = LeftSubstEq(
        Set(exists(x, forall(y, fp(g(g(z, x), y)))), forall(y, forall(z, g(y, z) === g(z, y)))) |- exists(x, forall(y, fp(g(y, g(x, z))))),
        0,
        List((LambdaTermTerm(Seq(y, z), g(y, z)), LambdaTermTerm(Seq(y, z), g(z, y)))),
        (Seq(g2), exists(x, forall(y, fp(g2(y, g2(x, z))))))
      )
      assert(checkSCProof(SCProof(IndexedSeq(t0, t1))).isValid)
    }
    {
      val t0 = Hypothesis(exists(x, forall(y, fp(g(y, g(x, f(z)))))) |- exists(x, forall(y, fp(g(y, g(x, f(z)))))), exists(x, forall(y, fp(g(y, g(x, f(z)))))))
      val t1 = LeftSubstEq(
        Set(exists(x, forall(y, fp(g(g(g(z, z), x), y)))), forall(y, f(y) === g(y, y)), forall(y, forall(z, g(y, z) === g(z, y)))) |- exists(x, forall(y, fp(g(y, g(x, f(z)))))),
        0,
        List((LambdaTermTerm(Seq(y, z), g(y, z)), LambdaTermTerm(Seq(y, z), g(z, y))), (LambdaTermTerm(Seq(y), f(y)), LambdaTermTerm(Seq(z), g(z, z)))),
        (Seq(g2, f2), exists(x, forall(y, fp(g2(y, g2(x, f2(z)))))))
      )
      assert(checkSCProof(SCProof(IndexedSeq(t0, t1))).isValid)
    }
  }

  test("Verification of RightSubstEq") {
    {
      val t0 = Hypothesis(fp(x) |- fp(x), fp(x))
      val t1 = RightSubstEq(Set(fp(x), x === y) |- fp(y), 0, List(((LambdaTermTerm(Seq(), x), LambdaTermTerm(Seq(), y)))), (Seq(sT), fp(sT)))
      assert(checkSCProof(SCProof(IndexedSeq(t0, t1))).isValid)
    }
    {
      val t0 = Hypothesis(exists(x, fp(f(x))) |- exists(x, fp(f(x))), exists(x, fp(f(x))))
      val t1 = RightSubstEq(
        Set(exists(x, fp(f(x))), forall(y, f(y) === g(y, y))) |- exists(x, fp(g(x, x))),
        0,
        List((LambdaTermTerm(Seq(x), f(x)), LambdaTermTerm(Seq(x), g(x, x)))),
        (Seq(f2), exists(x, fp(f2(x))))
      )
      assert(checkSCProof(SCProof(IndexedSeq(t0, t1))).isValid)
    }
    {
      val t0 = Hypothesis(exists(x, fp(f(x))) |- exists(x, fp(f(x))), exists(x, fp(f(x))))
      val t1 = RightSubstEq(
        Set(exists(x, fp(f(x))), forall(y, f(y) === g(y, y))) |- exists(x, fp(g(x, x))),
        0,
        List((LambdaTermTerm(Seq(y), f(y)), LambdaTermTerm(Seq(z), g(z, z)))),
        (Seq(f2), exists(x, fp(f2(x))))
      )
      assert(checkSCProof(SCProof(IndexedSeq(t0, t1))).isValid)
    }
    {
      val t0 = Hypothesis(exists(x, forall(y, fp(g(y, g(x, z))))) |- exists(x, forall(y, fp(g(y, g(x, z))))), exists(x, forall(y, fp(g(y, g(x, z))))))
      val t1 = RightSubstEq(
        Set(exists(x, forall(y, fp(g(y, g(x, z))))), forall(y, forall(z, g(y, z) === g(z, y)))) |- exists(x, forall(y, fp(g(g(x, z), y)))),
        0,
        List((LambdaTermTerm(Seq(y, z), g(y, z)), LambdaTermTerm(Seq(y, z), g(z, y)))),
        (Seq(g2), exists(x, forall(y, fp(g2(y, g(x, z))))))
      )
      assert(checkSCProof(SCProof(IndexedSeq(t0, t1))).isValid)
    }
    {
      val t0 = Hypothesis(exists(x, forall(y, fp(g(y, g(x, z))))) |- exists(x, forall(y, fp(g(y, g(x, z))))), exists(x, forall(y, fp(g(y, g(x, z))))))
      val t1 = RightSubstEq(
        Set(exists(x, forall(y, fp(g(y, g(x, z))))), forall(y, forall(z, g(y, z) === g(z, y)))) |- exists(x, forall(y, fp(g(g(z, x), y)))),
        0,
        List((LambdaTermTerm(Seq(y, z), g(y, z)), LambdaTermTerm(Seq(y, z), g(z, y)))),
        (Seq(g2), exists(x, forall(y, fp(g2(y, g2(x, z))))))
      )
      assert(checkSCProof(SCProof(IndexedSeq(t0, t1))).isValid)
    }
    {
      val t0 = Hypothesis(exists(x, forall(y, fp(g(y, g(x, f(z)))))) |- exists(x, forall(y, fp(g(y, g(x, f(z)))))), exists(x, forall(y, fp(g(y, g(x, f(z)))))))
      val t1 = RightSubstEq(
        Set(exists(x, forall(y, fp(g(y, g(x, f(z)))))), forall(y, f(y) === g(y, y)), forall(y, forall(z, g(y, z) === g(z, y)))) |- exists(x, forall(y, fp(g(g(g(z, z), x), y)))),
        0,
        List((LambdaTermTerm(Seq(y, z), g(y, z)), LambdaTermTerm(Seq(y, z), g(z, y))), (LambdaTermTerm(Seq(y), f(y)), LambdaTermTerm(Seq(z), g(z, z)))),
        (Seq(g2, f2), exists(x, forall(y, fp(g2(y, g2(x, f2(z)))))))
      )
      assert(checkSCProof(SCProof(IndexedSeq(t0, t1))).isValid)
    }

  }

  test("Verification of LeftSubstIff") {
    {
      val t0 = Hypothesis(P(x) |- P(x), P(x))
      val t1 = LeftSubstIff(Set(P(y), P(x) <=> P(y)) |- P(x), 0, List(((LambdaTermFormula(Seq(), P(x)), LambdaTermFormula(Seq(), P(y))))), (Seq(X), X))
      val pr = new SCProof(IndexedSeq(t0, t1))
      assert(checkSCProof(pr).isValid)
    }
    {
      val t0 = Hypothesis(exists(x, P(x)) |- exists(x, P(x)), exists(x, P(x)))
      val t1 = LeftSubstIff(
        Set(exists(x, Q(x, x)), forall(y, P(y) <=> Q(y, y))) |- exists(x, P(x)),
        0,
        List((LambdaTermFormula(Seq(x), P(x)), LambdaTermFormula(Seq(x), Q(x, x)))),
        (Seq(P2), exists(x, P2(x)))
      )
      assert(checkSCProof(SCProof(IndexedSeq(t0, t1))).isValid)
    }
    {
      val t0 = Hypothesis(exists(x, P(x)) |- exists(x, P(x)), exists(x, P(x)))
      val t1 = LeftSubstIff(
        Set(exists(x, Q(x, x)), forall(y, P(y) <=> Q(y, y))) |- exists(x, P(x)),
        0,
        List((LambdaTermFormula(Seq(y), P(y)), LambdaTermFormula(Seq(z), Q(z, z)))),
        (Seq(P2), exists(x, P2(x)))
      )
      assert(checkSCProof(SCProof(IndexedSeq(t0, t1))).isValid)
    }
    {
      val t0 = Hypothesis(exists(x, forall(y, Q(y, g(x, z)))) |- exists(x, forall(y, Q(y, g(x, z)))), exists(x, forall(y, Q(y, g(x, z)))))
      val t1 = LeftSubstIff(
        Set(exists(x, forall(y, Q(g(x, z), y))), forall(x, forall(y, Q(x, y) <=> Q(y, x)))) |- exists(x, forall(y, Q(y, g(x, z)))),
        0,
        List((LambdaTermFormula(Seq(y, z), Q(y, z)), LambdaTermFormula(Seq(y, z), Q(z, y)))),
        (Seq(Q2), exists(x, forall(y, Q2(y, g(x, z)))))
      )
      assert(checkSCProof(SCProof(IndexedSeq(t0, t1))).isValid)
    }

  }

  test("Verification of RightSubstIff") {
    {
      val t0 = Hypothesis(P(x) |- P(x), P(x))
      val t1 = RightSubstIff(Set(P(x), P(x) <=> P(y)) |- P(y), 0, List(((LambdaTermFormula(Seq(), P(x)), LambdaTermFormula(Seq(), P(y))))), (Seq(X), X))
      val pr = new SCProof(IndexedSeq(t0, t1))
      assert(checkSCProof(pr).isValid)
    }
    {
      val t0 = Hypothesis(exists(x, P(x)) |- exists(x, P(x)), exists(x, P(x)))
      val t1 = RightSubstIff(
        Set(exists(x, P(x)), forall(y, P(y) <=> Q(y, y))) |- exists(x, Q(x, x)),
        0,
        List((LambdaTermFormula(Seq(x), P(x)), LambdaTermFormula(Seq(x), Q(x, x)))),
        (Seq(P2), exists(x, P2(x)))
      )
      assert(checkSCProof(SCProof(IndexedSeq(t0, t1))).isValid)
    }
    {
      val t0 = Hypothesis(exists(x, P(x)) |- exists(x, P(x)), exists(x, P(x)))
      val t1 = RightSubstIff(
        Set(exists(x, P(x)), forall(y, P(y) <=> Q(y, y))) |- exists(x, Q(x, x)),
        0,
        List((LambdaTermFormula(Seq(y), P(y)), LambdaTermFormula(Seq(z), Q(z, z)))),
        (Seq(P2), exists(x, P2(x)))
      )
      assert(checkSCProof(SCProof(IndexedSeq(t0, t1))).isValid)
    }
    {
      val t0 = Hypothesis(exists(x, forall(y, Q(y, g(x, z)))) |- exists(x, forall(y, Q(y, g(x, z)))), exists(x, forall(y, Q(y, g(x, z)))))
      val t1 = RightSubstIff(
        Set(exists(x, forall(y, Q(y, g(x, z)))), forall(x, forall(y, Q(x, y) <=> Q(y, x)))) |- exists(x, forall(y, Q(g(x, z), y))),
        0,
        List((LambdaTermFormula(Seq(y, z), Q(y, z)), LambdaTermFormula(Seq(y, z), Q(z, y)))),
        (Seq(Q2), exists(x, forall(y, Q2(g(x, z), y))))
      )
      assert(checkSCProof(SCProof(IndexedSeq(t0, t1))).isValid)
    }
  }

  test("Commutativity on a random large formula") {
    val k = 9
    val r = new Random()
    val vars = (0 until 1 << k).map(i => AtomicFormula(ConstantAtomicLabel(s"P$i", 0), Seq()))

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
    val prf = SCProof(Vector(Hypothesis(Sequent(Set(orig), Set(orig)), orig), Restate(Sequent(Set(orig), Set(swapped)), 0)))
    assert(checkSCProof(prf).isValid)
  }
}
