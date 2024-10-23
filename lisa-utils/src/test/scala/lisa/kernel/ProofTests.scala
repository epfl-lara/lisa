package lisa.kernel

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.RunningTheory.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SCProofChecker
import lisa.kernel.proof.SCProofChecker.checkSCProof
import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.KernelHelpers.{_, given}
import org.scalatest.funsuite.AnyFunSuite

import scala.language.adhocExtensions
import scala.util.Random

class ProofTests extends AnyFunSuite {

  private val x = variable
  private val y = variable
  private val z = variable
  val f = function(1)
  val f2 = function(1)
  val g = cst("g", Term >>: Term >>: Term)
  val g2 = function(2)
  private val a = cst("A", Formula)
  private val b = cst("A", Formula)
  private val fp = cst("F", Term >>: Formula)
  val sT = variable("t")

  val X = formulaVariable("X")
  val P = predicate(1)
  val P2 = predicate(1)
  val Q = cst(Term >>: Term >>: Formula)
  val Q2 = predicate(2)

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
      val t1 = Hypothesis(x === y |- x === y, x === y)
      val t2 = LeftSubstEq(Set(fp(y), x === y) |- fp(x), 0, Seq((x, y)), (Seq(sT), fp(sT)))
      val judg = checkSCProof(SCProof(IndexedSeq(t0, t1, t2)))
      assert(judg.isValid, "\n" + judg.repr)
    }
    {
      val t0 = Hypothesis(exists(x, fp(f(x))) |- exists(x, fp(f(x))), exists(x, fp(f(x))))
      val t1 = LeftSubstEq(
        Set(exists(x, fp(lambda(x, g(x, x))(x))), forall(y, f(y) === lambda(x, g(x, x))(y))) |- exists(x, fp(f(x))),
        0,
        Seq((f, lambda(x, g(x, x)))),
        (Seq(f2), exists(x, fp(f2(x))))
      )
      val t2 = Beta(
        Set(exists(x, fp(g(x, x))), forall(y, f(y) === g(y, y))) |- exists(x, fp(f(x))),
        1
      )
      val judg = checkSCProof(SCProof(IndexedSeq(t0, t1, t2)))
      assert(judg.isValid, "\n" + judg.repr)
    }
    {
      val t0 = Hypothesis(exists(x, fp(f(x))) |- exists(x, fp(f(x))), exists(x, fp(f(x))))
      val t1 = LeftSubstEq(
        Set(exists(x, fp(lambda(x, g(x, x))(x))), forall(y, f(y) === lambda(x, g(x, x))(y))) |- exists(x, fp(f(x))),
        0,
        Seq((f, lambda(z, g(z, z)))),
        (Seq(f2), exists(x, fp(f2(x))))
      )
      val t2 = Beta(
        Set(exists(x, fp(g(x, x))), forall(y, f(y) === g(y, y))) |- exists(x, fp(f(x))),
        1
      )
      val judg = checkSCProof(SCProof(IndexedSeq(t0, t1, t2)))
      assert(judg.isValid, "\n" + judg.repr)
    }
    {
      val t0 = Hypothesis(exists(x, forall(y, fp(g(y, g(x, z))))) |- exists(x, forall(y, fp(g(y, g(x, z))))), exists(x, forall(y, fp(g(y, g(x, z))))))
      val t1 = LeftSubstEq(
        Set(exists(x, forall(y, fp(lambda(Seq(y, z), g(z, y))(y, g(x, z))))), forall(y, forall(z, g(y, z) === lambda(Seq(y, z), g(z, y))(y, z)))) |- exists(x, forall(y, fp(g(y, g(x, z))))),
        0,
        Seq((g, lambda(Seq(y, z), g(z, y)))),
        (Seq(g2), exists(x, forall(y, fp(g2(y, g(x, z))))))
      )
      val judg = checkSCProof(SCProof(IndexedSeq(t0, t1)))
      assert(judg.isValid, "\n" + judg.repr)
    }
    {
      val t0 = Hypothesis(exists(x, forall(y, fp(g(y, g(x, z))))) |- exists(x, forall(y, fp(g(y, g(x, z))))), exists(x, forall(y, fp(g(y, g(x, z))))))
      val t1 = LeftSubstEq(
        Set(
          exists(x, forall(y, fp(lambda(Seq(y, z), g(z, y))(y, lambda(Seq(y, z), g(z, y))(x, z))))),
          forall(y, forall(z, g(y, z) === lambda(Seq(y, z), g(z, y))(y, z)))
          ) |- exists(x, forall(y, fp(g(y, g(x, z))))),
        0,
        Seq((g, lambda(Seq(y, z), g(z, y)))),
        (Seq(g2), exists(x, forall(y, fp(g2(y, g2(x, z))))))
      )
      val judg = checkSCProof(SCProof(IndexedSeq(t0, t1)))
      assert(judg.isValid, "\n" + judg.repr)
    }
    //
    {
      val t0 = Hypothesis(P(x) |- P(x), P(x))
      val t1 = Hypothesis(P(x) <=> P(y) |- P(x) <=> P(y), P(x) <=> P(y))
      val t2 = LeftSubstIff(Set(P(y), P(x) <=> P(y)) |- P(x), 0, Seq((P(x), P(y))), (Seq(X), X))
      val judg = checkSCProof(SCProof(IndexedSeq(t0, t1, t2)))
      assert(judg.isValid, "\n" + judg.repr)
    }
    {
      val t0 = Hypothesis(exists(x, P(x)) |- exists(x, P(x)), exists(x, P(x)))
      val t1 = LeftSubstIff(
        Set(exists(x, lambda(x, Q(x, x))(x)), forall(y, P(y) <=> lambda(x, Q(x, x))(y))) |- exists(x, P(x)),
        0,
        Seq((P, lambda(x, Q(x, x)))),
        (Seq(P2), exists(x, P2(x)))
      )
      val t2 = Beta(
        Set(exists(x, Q(x, x)), forall(y, P(y) <=> Q(y, y))) |- exists(x, P(x)),
        1
      )
      val judg = checkSCProof(SCProof(IndexedSeq(t0, t1, t2)))
      assert(judg.isValid, "\n" + judg.repr)
    }
    {
      val t0 = Hypothesis(exists(x, P(x)) |- exists(x, P(x)), exists(x, P(x)))
      val t1 = LeftSubstIff(
        Set(exists(x, lambda(z, Q(z, z))(x)), forall(y, P(y) <=> lambda(x, Q(x, x))(y))) |- exists(x, P(x)),
        0,
        Seq((P, lambda(z, Q(z, z)))),
        (Seq(P2), exists(x, P2(x)))
      )
      val t2 = Beta(
        Set(exists(x, Q(x, x)), forall(y, P(y) <=> Q(y, y))) |- exists(x, P(x)),
        1
      )
      val judg = checkSCProof(SCProof(IndexedSeq(t0, t1, t2)))
      assert(judg.isValid, "\n" + judg.repr)
    }
    {
      val t0 = Hypothesis(exists(x, forall(y, Q(y, g(x, z)))) |- exists(x, forall(y, Q(y, g(x, z)))), exists(x, forall(y, Q(y, g(x, z)))))
      val t1 = LeftSubstIff(
        Set(exists(x, forall(y, lambda(Seq(y, z), Q(z, y))(y, g(x, z)))), forall(x, forall(y, Q(x, y) <=> lambda(Seq(y, z), Q(z, y))(x, y)))) |- exists(x, forall(y, Q(y, g(x, z)))),
        0,
        Seq((Q, lambda(Seq(y, z), Q(z, y)))),
        (Seq(Q2), exists(x, forall(y, Q2(y, g(x, z)))))
      )
      val judg = checkSCProof(SCProof(IndexedSeq(t0, t1)))
      assert(judg.isValid, "\n" + judg.repr)
    }
    {
      val t0 = Hypothesis(exists(x, forall(y, fp(g(y, g(x, f(z)))))) |- exists(x, forall(y, fp(g(y, g(x, f(z)))))), exists(x, forall(y, fp(g(y, g(x, f(z)))))))
      val t1 = LeftSubstEq(
        Set(exists(x, forall(y, fp(lambda(Seq(y, z), g(z, y))(y, lambda(Seq(y, z), g(z, y))(x, lambda(Seq(z), g(z, z))(z)))))), forall(y, f(y) === lambda(Seq(z), g(z, z))(y)), forall(y, forall(z, g(y, z) === lambda(Seq(y, z), g(z, y))(y, z)))) |- exists(x, forall(y, fp(g(y, g(x, f(z)))))),
        0,
        List((g, lambda(Seq(y, z), g(z, y))), (f, lambda(Seq(z), g(z, z)))),
        (Seq(g2, f2), exists(x, forall(y, fp(g2(y, g2(x, f2(z)))))))
      )
      val t2 = Beta(Set(exists(x, forall(y, fp(g(g(g(z, z), x), y)))), forall(y, f(y) === g(y, y)), forall(y, forall(z, g(y, z) === g(z, y)))) |- exists(x, forall(y, fp(g(y, g(x, f(z)))))), 1)
      val judg = checkSCProof(SCProof(IndexedSeq(t0, t1, t2)))
      assert(judg.isValid, "\n" + judg.repr)
    }
  }

  test("Verification of RightSubstEq") {
    {
      val t0 = Hypothesis(fp(x) |- fp(x), fp(x))
      val t1 = Hypothesis(x === y |- x === y, x === y)
      val t2 = RightSubstEq(Set(fp(x), x === y) |- fp(y), 0, Seq((x, y)), (Seq(sT), fp(sT)))
      assert(checkSCProof(SCProof(IndexedSeq(t0, t1))).isValid)
    }
    {
      val t0 = Hypothesis(exists(x, fp(f(x))) |- exists(x, fp(f(x))), exists(x, fp(f(x))))
      val t1 = RightSubstEq(
        Set(exists(x, fp(f(x))), forall(y, f(y) === lambda(x, g(x, x))(y))) |- exists(x, fp(lambda(x, g(x, x))(x))),
        0,
        Seq((f, lambda(x, g(x, x)))),
        (Seq(f2), exists(x, fp(f2(x))))
      )
      val t2 = Beta(
        Set(exists(x, fp(f(x))), forall(y, f(y) === g(y, y))) |- exists(x, fp(g(x, x))),
        1
      )
      val judg = checkSCProof(SCProof(IndexedSeq(t0, t1, t2)))
      assert(judg.isValid, "\n" + judg.repr)
    }
    {
      val t0 = Hypothesis(exists(x, fp(f(x))) |- exists(x, fp(f(x))), exists(x, fp(f(x))))
      val t1 = RightSubstEq(
        Set(exists(x, fp(f(x))), forall(y, f(y) ===  lambda(x, g(x, x))(y))) |- exists(x, fp(lambda(z, g(z, z))(x))),
        0,
        Seq((f, lambda(z, g(z, z)))),
        (Seq(f2), exists(x, fp(f2(x))))
      )
      val t2 = Beta(
        Set(exists(x, fp(f(x))), forall(y, f(y) === g(y, y))) |- exists(x, fp(g(x, x))),
        1
      )
      val judg = checkSCProof(SCProof(IndexedSeq(t0, t1, t2)))
      assert(judg.isValid, "\n" + judg.repr)
    }
    {
      val t0 = Hypothesis(exists(x, forall(y, fp(g(y, g(x, z))))) |- exists(x, forall(y, fp(g(y, g(x, z))))), exists(x, forall(y, fp(g(y, g(x, z))))))
      val t1 = RightSubstEq(
        Set(
          exists(x, forall(y, fp(g(y, g(x, z))))), 
          forall(y, forall(z, g(y, z) ===lambda(Seq(y, z), g(z, y))(y, z)))
        ) |- exists(x, forall(y, fp(lambda(Seq(y, z), g(z, y))(y, g(x, z))))),
        0,
        Seq((g, lambda(Seq(y, z), g(z, y)))),
        (Seq(g2), exists(x, forall(y, fp(g2(y, g(x, z))))))
      )
      val judg = checkSCProof(SCProof(IndexedSeq(t0, t1)))
      assert(judg.isValid, "\n" + judg.repr)
    }
    {
      val t0 = Hypothesis(exists(x, forall(y, fp(g(y, g(x, z))))) |- exists(x, forall(y, fp(g(y, g(x, z))))), exists(x, forall(y, fp(g(y, g(x, z))))))
      val t1 = RightSubstEq(
        Set(
          exists(x, forall(y, fp(g(y, g(x, z))))), 
          forall(y, forall(z, g(y, z) === lambda(Seq(y, z), g(z, y))(y, z)))
        ) |- exists(x, forall(y, fp(lambda(Seq(y, z), g(z, y))(y, lambda(Seq(y, z), g(z, y))(x, z))))),
        0,
        Seq((g, lambda(Seq(y, z), g(z, y)))),
        (Seq(g2), exists(x, forall(y, fp(g2(y, g2(x, z))))))
      )
      val judg = checkSCProof(SCProof(IndexedSeq(t0, t1)))
      assert(judg.isValid, "\n" + judg.repr)
    }
    //
    {
      val t0 = Hypothesis(P(x) |- P(x), P(x))
      val t1 = RightSubstIff(Set(P(x), P(x) <=> P(y)) |- P(y), 0, Seq((P(x), P(y))), (Seq(X), X))
      assert(checkSCProof(SCProof(IndexedSeq(t0, t1))).isValid)
    }
    {
      val t0 = Hypothesis(exists(x, P(x)) |- exists(x, P(x)), exists(x, P(x)))
      val t1 = RightSubstIff(
        Set(exists(x, P(x)), forall(y, P(y) <=> lambda(x, Q(x, x))(y))) |- exists(x, lambda(x, Q(x, x))(x)),
        0,
        Seq((P, lambda(x, Q(x, x)))),
        (Seq(P2), exists(x, P2(x)))
      )
      val t2 = Beta(
        Set(exists(x, P(x)), forall(y, P(y) <=> Q(y, y))) |- exists(x, Q(x, x)),
        1
      )
      val judg = checkSCProof(SCProof(IndexedSeq(t0, t1, t2)))
      assert(judg.isValid, "\n" + judg.repr)
    }
    {
      val t0 = Hypothesis(exists(x, P(x)) |- exists(x, P(x)), exists(x, P(x)))
      val t1 = RightSubstIff(
        Set(exists(x, P(x)), forall(y, P(y) <=> lambda(x, Q(x, x))(y))) |- exists(x, lambda(z, Q(z, z))(x)),
        0,
        Seq((P, lambda(z, Q(z, z)))),
        (Seq(P2), exists(x, P2(x)))
      )
      val t2 = Beta(
        Set(exists(x, P(x)), forall(y, P(y) <=> Q(y, y))) |- exists(x, Q(x, x)),
        1
      )
      val judg = checkSCProof(SCProof(IndexedSeq(t0, t1, t2)))
      assert(judg.isValid, "\n" + judg.repr)
    }
    {
      val t0 = Hypothesis(exists(x, forall(y, Q(y, g(x, z)))) |- exists(x, forall(y, Q(y, g(x, z)))), exists(x, forall(y, Q(y, g(x, z)))))
      val t1 = RightSubstIff(
        Set(exists(x, forall(y, Q(y, g(x, z)))), forall(x, forall(y, Q(x, y) <=> lambda(Seq(y, z), Q(z, y))(x, y)))) |- exists(x, forall(y, lambda(Seq(y, z), Q(z, y))(y, g(x, z)))),
        0,
        Seq((Q, lambda(Seq(y, z), Q(z, y)))),
        (Seq(Q2), exists(x, forall(y, Q2(y, g(x, z)))))
      )
      val judg = checkSCProof(SCProof(IndexedSeq(t0, t1)))
      assert(judg.isValid, "\n" + judg.repr)
    }
    {
      val t0 = Hypothesis(exists(x, forall(y, fp(g(y, g(x, f(z)))))) |- exists(x, forall(y, fp(g(y, g(x, f(z)))))), exists(x, forall(y, fp(g(y, g(x, f(z)))))))
      val t1 = RightSubstEq(
        Set(exists(x, forall(y, fp(g(y, g(x, f(z)))))), forall(y, f(y) === lambda(Seq(z), g(z, z))(y)), forall(y, forall(z, g(y, z) === lambda(Seq(y, z), g(z, y))(y, z)))) |- exists(x, forall(y, fp(lambda(Seq(y, z), g(z, y))(y, lambda(Seq(y, z), g(z, y))(x, lambda(Seq(z), g(z, z))(z)))))),
        0,
        List((g, lambda(Seq(y, z), g(z, y))), (f, lambda(Seq(z), g(z, z)))),
        (Seq(g2, f2), exists(x, forall(y, fp(g2(y, g2(x, f2(z)))))))
      )
      val t2 = Beta(Set(exists(x, forall(y, fp(g(y, g(x, f(z)))))), forall(y, f(y) === g(y, y)), forall(y, forall(z, g(y, z) === g(z, y)))) |- exists(x, forall(y, fp(g(g(g(z, z), x), y)))), 1)
      val judg = checkSCProof(SCProof(IndexedSeq(t0, t1, t2)))
      assert(judg.isValid, "\n" + judg.repr)
    }
  }

  test("Commutativity on a random large formula") {
    val k = 9
    val r = new Random()
    val vars = (0 until 1 << k).map(i => Constant(s"P$i", Formula))

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
