package lisa.utils

import lisa.kernel.fol.FOL._
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus._
import lisa.utils.KernelHelpers.{_, given}
import lisa.utils.Serialization._
import org.scalatest.funsuite.AnyFunSuite

import java.io.ByteArrayInputStream
import java.io.ByteArrayOutputStream
import java.io.DataInputStream
import java.io.DataOutputStream
import scala.collection.mutable.{Map => MutMap}

/**
 * Tests for serialization and deserialization of proofs
 */
class SerializationTest extends AnyFunSuite with TestUtils {

  import scala.collection.immutable.{SortedSet => SSet}

  ///////////////////////////////////////////////////////
  // Testing utilities

  def roundTrip[A, B >: A](
      serialize: (A, DataOutputStream) => Unit,
      deserialize: DataInputStream => B,
      equal: (A, B) => Boolean = (a: A, b: B) => a == b
  )(name: String, obj: A): Unit =
    test(s"Serialization: $name") {
      val baos = new ByteArrayOutputStream()
      val dos = new DataOutputStream(baos)
      serialize(obj, dos)
      dos.flush()
      val bytes = baos.toByteArray
      val bais = new ByteArrayInputStream(bytes)
      val dis = new DataInputStream(bais)
      val deserialized = deserialize(dis)
      assert(equal(obj, deserialized), s"Round-trip failed:\n  Original:      $obj\n  Deserialized:  $deserialized")
    }

  def exprRoundTrip(name: String, e: Expression): Unit =
    test(s"Serialization: $name") {
      val baos = new ByteArrayOutputStream()
      val dos = new DataOutputStream(baos)
      val writeMap = MutMap[Long, Line]()
      val line = lineOfExpr(e, dos, writeMap)
      dos.flush()
      val dis = new DataInputStream(new ByteArrayInputStream(baos.toByteArray))
      val readMap = MutMap[Line, Expression]()
      readTreeEntries(dis, writeMap.size, readMap)
      val result = readMap(line)
      assert(result == e, s"Round-trip failed:\n  Original:      $e\n  Deserialized:  $result")
    }

  ///////////////////////////////////////////////////////
  // Variable serialization tests

  def varRT(name: String, v: Variable): Unit = exprRoundTrip(name, v)

  varRT("variable x:Ind", x)
  varRT("variable y:Ind", y)
  varRT("variable z:Ind", z)
  varRT("formula variable", Variable("p", Prop))
  varRT("function variable", Variable("f", Arrow(Ind, Ind)))
  varRT("predicate variable", Variable("P", Arrow(Ind, Prop)))
  varRT("higher-order variable", Variable("F", Arrow(Arrow(Ind, Prop), Prop)))
  varRT("arrow of arrows", Variable("g", Arrow(Arrow(Ind, Ind), Arrow(Ind, Ind))))
  varRT("variable with non-zero index", Variable(Identifier("x", 5), Ind))

  ///////////////////////////////////////////////////////
  // Constant serialization tests

  def cstRT(name: String, c: Constant): Unit = exprRoundTrip(name, c)

  cstRT("propositional constant a", a)
  cstRT("propositional constant b", b)
  cstRT("individual constant", Constant("myc", Ind))
  cstRT("unary function constant", f1)
  cstRT("predicate constant p", p)
  cstRT("binary function constant", f2)
  cstRT("ternary function constant", f3)
  cstRT("constant with non-zero index", Constant(Identifier("k", 3), Prop))

  ///////////////////////////////////////////////////////
  // Expression tree serialization tests

  def exprRT(name: String, e: Expression): Unit = exprRoundTrip(name, e)

  // Leaf expressions
  exprRT("variable as expression", x)
  exprRT("constant as expression", a)
  exprRT("individual constant as expression", Constant("d", Ind))

  // Simple applications
  exprRT("unary predicate application p(x)", Application(p, x))
  exprRT("binary function application f(x,y)", Application(Application(f2, x), y))
  exprRT("negation", Application(neg, a))
  exprRT("implication a => b", Application(Application(implies, a), b))
  exprRT("conjunction a /\\ b", Application(Application(and, a), b))
  exprRT("disjunction a \\/ b", Application(Application(or, a), b))
  exprRT("equality x = y", Application(Application(equality, x), y))

  // Lambda expressions
  exprRT("simple lambda", Lambda(x, Application(p, x)))
  exprRT("nested lambda", Lambda(x, Lambda(y, Application(Application(f2, x), y))))
  exprRT("lambda with formula body", Lambda(x, Application(Application(equality, x), y)))

  // Quantifiers (Application of forall/exists to a lambda)
  exprRT("forall x. p(x)", Application(forall, Lambda(x, Application(p, x))))
  exprRT("exists x. p(x)", Application(exists, Lambda(x, Application(p, x))))

  // Shared subexpressions
  exprRT(
    "shared subexpressions", {
      val px = Application(p, x)
      Application(Application(and, px), px)
    }
  )

  // Deeply nested
  exprRT(
    "deeply nested applications", {
      val fx = Application(f1, x)
      val ffx = Application(f1, fx)
      val fffx = Application(f1, ffx)
      Application(p, fffx)
    }
  )

  ///////////////////////////////////////////////////////
  // Sort string round-trip tests

  test("Serialization: typeToString/typeFromString round-trip Ind") {
    assert(typeFromString(typeToString(Ind))._1 == Ind)
  }
  test("Serialization: typeToString/typeFromString round-trip Prop") {
    assert(typeFromString(typeToString(Prop))._1 == Prop)
  }
  test("Serialization: typeToString/typeFromString round-trip Arrow") {
    val t = Arrow(Ind, Arrow(Ind, Prop))
    assert(typeFromString(typeToString(t))._1 == t)
  }
  test("Serialization: typeToString/typeFromString round-trip nested Arrow") {
    val t = Arrow(Arrow(Ind, Prop), Arrow(Ind, Prop))
    assert(typeFromString(typeToString(t))._1 == t)
  }

  ///////////////////////////////////////////////////////
  // Sequent serialization tests

  val seqRT = roundTrip[Sequent, Sequent](
    (s, dos) => sequentToDOS(s, dos),
    dis => sequentFromDIS(dis)
  )

  seqRT("empty sequent", Sequent(SSet.empty, SSet.empty))
  seqRT("hypothesis-like P |- P", Sequent(SSet(a), SSet(a)))
  seqRT("multi-formula left", Sequent(SSet(a, b, c), SSet.empty))
  seqRT("multi-formula right", Sequent(SSet.empty, SSet(a, b, c)))
  seqRT("both sides", Sequent(SSet(a, b), SSet(c)))
  seqRT("with applications", Sequent(SSet(Application(p, x)), SSet(Application(p, y))))
  seqRT(
    "with quantifiers", {
      val phi = Application(forall, Lambda(x, Application(p, x)))
      Sequent(SSet(phi), SSet(phi))
    }
  )

  ///////////////////////////////////////////////////////
  // Proof serialization tests (via proofsToDataStream/proofsFromDataStream)

  def proofsEqual(p1: SCProof, p2: SCProof): Boolean =
    p1.steps.size == p2.steps.size &&
      p1.imports.size == p2.imports.size &&
      p1.steps.zip(p2.steps).forall(_ == _) &&
      p1.imports.zip(p2.imports).forall(_ == _)

  def proofRT(name: String, proof: SCProof): Unit =
    test(s"Serialization: $name") {
      val treeBaos = new ByteArrayOutputStream()
      val proofBaos = new ByteArrayOutputStream()
      proofsToDataStream(new DataOutputStream(treeBaos), new DataOutputStream(proofBaos), Seq(("_", proof, List.empty)))
      val results = proofsFromDataStream(
        new DataInputStream(new ByteArrayInputStream(treeBaos.toByteArray)),
        new DataInputStream(new ByteArrayInputStream(proofBaos.toByteArray))
      )
      assert(proofsEqual(results.head._2, proof), s"Round-trip failed:\n  Original:      $proof\n  Deserialized:  ${results.head._2}")
    }

  // Hypothesis: a |- a
  proofRT(
    "Hypothesis proof",
    new SCProof(
      IndexedSeq(Hypothesis(Sequent(SSet(a), SSet(a)), a)),
      IndexedSeq.empty
    )
  )

  // RestateTrue: |- top
  proofRT(
    "RestateTrue proof",
    new SCProof(
      IndexedSeq(RestateTrue(Sequent(SSet.empty, SSet(top)))),
      IndexedSeq.empty
    )
  )

  // Weakening with import
  proofRT(
    "Weakening with import",
    new SCProof(
      IndexedSeq(Weakening(Sequent(SSet(a, b), SSet(a)), -1)),
      IndexedSeq(Sequent(SSet(a), SSet(a)))
    )
  )

  // Cut proof
  proofRT(
    "Cut proof", {
      val s1 = Sequent(SSet(a), SSet(a, b))
      val s2 = Sequent(SSet(a, b), SSet(b))
      val bot = Sequent(SSet(a), SSet(b))
      new SCProof(
        IndexedSeq(
          Hypothesis(s1, a),
          Hypothesis(s2, b),
          Cut(bot, 0, 1, a)
        ),
        IndexedSeq.empty
      )
    }
  )

  // LeftAnd
  proofRT(
    "LeftAnd proof", {
      val phi = a; val psi = b
      val premise = Sequent(SSet(phi, psi), SSet(phi))
      val bot = Sequent(SSet(Application(Application(and, phi), psi)), SSet(phi))
      new SCProof(
        IndexedSeq(
          Hypothesis(premise, phi),
          LeftAnd(bot, 0, phi, psi)
        ),
        IndexedSeq.empty
      )
    }
  )

  // RightOr
  proofRT(
    "RightOr proof", {
      val phi = a; val psi = b
      val premise = Sequent(SSet(phi), SSet(phi, psi))
      val bot = Sequent(SSet(phi), SSet(Application(Application(or, phi), psi)))
      new SCProof(
        IndexedSeq(
          Hypothesis(premise, phi),
          RightOr(bot, 0, phi, psi)
        ),
        IndexedSeq.empty
      )
    }
  )

  // LeftNot
  proofRT(
    "LeftNot proof", {
      val phi = a
      val premise = Sequent(SSet.empty, SSet(phi))
      val notPhi = Application(neg, phi)
      val bot = Sequent(SSet(notPhi), SSet(phi))
      new SCProof(
        IndexedSeq(
          RestateTrue(premise),
          LeftNot(bot, 0, phi)
        ),
        IndexedSeq.empty
      )
    }
  )

  // RightNot
  proofRT(
    "RightNot proof", {
      val phi = a
      val premise = Sequent(SSet(phi), SSet.empty)
      val notPhi = Application(neg, phi)
      val bot = Sequent(SSet(phi), SSet(notPhi))
      new SCProof(
        IndexedSeq(
          RestateTrue(premise),
          RightNot(bot, 0, phi)
        ),
        IndexedSeq.empty
      )
    }
  )

  // RightImplies
  proofRT(
    "RightImplies proof", {
      val phi = a; val psi = b
      val premise = Sequent(SSet(phi), SSet(psi))
      val impl = Application(Application(implies, phi), psi)
      val bot = Sequent(SSet.empty, SSet(impl))
      new SCProof(
        IndexedSeq(
          Weakening(premise, -1),
          RightImplies(bot, 0, phi, psi)
        ),
        IndexedSeq(Sequent(SSet(phi), SSet(psi)))
      )
    }
  )

  // LeftImplies
  proofRT(
    "LeftImplies proof", {
      val phi = a; val psi = b
      val s1 = Sequent(SSet(phi), SSet(phi))
      val s2 = Sequent(SSet(psi), SSet(psi))
      val impl = Application(Application(implies, phi), psi)
      val bot = Sequent(SSet(phi, impl), SSet(phi, psi))
      new SCProof(
        IndexedSeq(
          Hypothesis(s1, phi),
          Hypothesis(s2, psi),
          LeftImplies(bot, 0, 1, phi, psi)
        ),
        IndexedSeq.empty
      )
    }
  )

  // Sorry proof
  proofRT(
    "Sorry proof",
    new SCProof(
      IndexedSeq(Sorry(Sequent(SSet(a), SSet(b)))),
      IndexedSeq.empty
    )
  )

  // Restate
  proofRT(
    "Restate proof",
    new SCProof(
      IndexedSeq(
        Hypothesis(Sequent(SSet(a), SSet(a)), a),
        Restate(Sequent(SSet(a), SSet(a)), 0)
      ),
      IndexedSeq.empty
    )
  )

  // LeftIff
  proofRT(
    "LeftIff proof", {
      val phi = a; val psi = b
      val iffPhi = Application(Application(iff, phi), psi)
      val implPhi = Application(Application(implies, phi), psi)
      val premise = Sequent(SSet(implPhi), SSet(phi))
      val bot = Sequent(SSet(iffPhi), SSet(phi))
      new SCProof(
        IndexedSeq(
          Weakening(premise, -1),
          LeftIff(bot, 0, phi, psi)
        ),
        IndexedSeq(premise)
      )
    }
  )

  // RightIff
  proofRT(
    "RightIff proof", {
      val phi = a; val psi = b
      val iffExpr = Application(Application(iff, phi), psi)
      val impl1 = Application(Application(implies, phi), psi)
      val impl2 = Application(Application(implies, psi), phi)
      val s1 = Sequent(SSet.empty, SSet(impl1))
      val s2 = Sequent(SSet.empty, SSet(impl2))
      val bot = Sequent(SSet.empty, SSet(iffExpr))
      new SCProof(
        IndexedSeq(
          Weakening(s1, -1),
          Weakening(s2, -2),
          RightIff(bot, 0, 1, phi, psi)
        ),
        IndexedSeq(s1, s2)
      )
    }
  )

  // LeftOr
  proofRT(
    "LeftOr proof", {
      val phi = a; val psi = b
      val orExpr = Application(Application(or, phi), psi)
      val s1 = Sequent(SSet(phi), SSet(c))
      val s2 = Sequent(SSet(psi), SSet(c))
      val bot = Sequent(SSet(orExpr), SSet(c))
      new SCProof(
        IndexedSeq(
          Weakening(s1, -1),
          Weakening(s2, -2),
          LeftOr(bot, Seq(0, 1), Seq(phi, psi))
        ),
        IndexedSeq(s1, s2)
      )
    }
  )

  // RightAnd
  proofRT(
    "RightAnd proof", {
      val phi = a; val psi = b
      val andExpr = Application(Application(and, phi), psi)
      val s1 = Sequent(SSet(c), SSet(phi))
      val s2 = Sequent(SSet(c), SSet(psi))
      val bot = Sequent(SSet(c), SSet(andExpr))
      new SCProof(
        IndexedSeq(
          Weakening(s1, -1),
          Weakening(s2, -2),
          RightAnd(bot, Seq(0, 1), Seq(phi, psi))
        ),
        IndexedSeq(s1, s2)
      )
    }
  )

  // RightRefl
  proofRT(
    "RightRefl proof", {
      val eq = Application(Application(equality, x), x)
      new SCProof(
        IndexedSeq(RightRefl(Sequent(SSet.empty, SSet(eq)), eq)),
        IndexedSeq.empty
      )
    }
  )

  // LeftForall
  proofRT(
    "LeftForall proof", {
      val px = Application(p, x)
      val py = Application(p, y)
      val forallPx = Application(forall, Lambda(x, px))
      val premise = Sequent(SSet(py), SSet(py))
      val bot = Sequent(SSet(forallPx), SSet(py))
      new SCProof(
        IndexedSeq(
          Hypothesis(premise, py),
          LeftForall(bot, 0, px, x, y)
        ),
        IndexedSeq.empty
      )
    }
  )

  // RightExists
  proofRT(
    "RightExists proof", {
      val px = Application(p, x)
      val py = Application(p, y)
      val existsPx = Application(exists, Lambda(x, px))
      val premise = Sequent(SSet(py), SSet(py))
      val bot = Sequent(SSet(py), SSet(existsPx))
      new SCProof(
        IndexedSeq(
          Hypothesis(premise, py),
          RightExists(bot, 0, px, x, y)
        ),
        IndexedSeq.empty
      )
    }
  )

  // RightForall
  proofRT(
    "RightForall proof", {
      val px = Application(p, x)
      val forallPx = Application(forall, Lambda(x, px))
      val premise = Sequent(SSet.empty, SSet(px))
      val bot = Sequent(SSet.empty, SSet(forallPx))
      new SCProof(
        IndexedSeq(
          Weakening(premise, -1),
          RightForall(bot, 0, px, x)
        ),
        IndexedSeq(premise)
      )
    }
  )

  // LeftExists
  proofRT(
    "LeftExists proof", {
      val px = Application(p, x)
      val existsPx = Application(exists, Lambda(x, px))
      val premise = Sequent(SSet(px), SSet.empty)
      val bot = Sequent(SSet(existsPx), SSet.empty)
      new SCProof(
        IndexedSeq(
          Weakening(premise, -1),
          LeftExists(bot, 0, px, x)
        ),
        IndexedSeq(premise)
      )
    }
  )

  // InstSchema
  proofRT(
    "InstSchema proof", {
      val xv = Variable("X", Prop)
      val premise = Sequent(SSet(xv), SSet(xv))
      val bot = Sequent(SSet(a), SSet(a))
      new SCProof(
        IndexedSeq(
          Hypothesis(premise, xv),
          InstSchema(bot, 0, Map(xv -> a))
        ),
        IndexedSeq.empty
      )
    }
  )

  ///////////////////////////////////////////////////////////////////////////////
  // Dual-stream proofsToDataStream/proofsFromDataStream round-trip. This is the
  // default serialization mode- using one stream for trees and one for proofs.

  test("Serialization: proofsToDataStream/proofsFromDataStream round-trip") {
    val proof = new SCProof(
      IndexedSeq(
        Hypothesis(Sequent(SSet(a), SSet(a)), a),
        Hypothesis(Sequent(SSet(b), SSet(b)), b),
        Cut(Sequent(SSet(a), SSet(b)), 0, 1, a)
      ),
      IndexedSeq.empty
    )

    val treeBaos = new ByteArrayOutputStream()
    val proofBaos = new ByteArrayOutputStream()
    val treesDOS = new DataOutputStream(treeBaos)
    val proofDOS = new DataOutputStream(proofBaos)

    proofsToDataStream(treesDOS, proofDOS, Seq(("myThm", proof, List("just1"))))
    treesDOS.flush()
    proofDOS.flush()

    val treesDIS = new DataInputStream(new ByteArrayInputStream(treeBaos.toByteArray))
    val proofDIS = new DataInputStream(new ByteArrayInputStream(proofBaos.toByteArray))

    val results = proofsFromDataStream(treesDIS, proofDIS)
    assert(results.size == 1)
    assert(results.head._1 == "myThm")
    assert(results.head._3 == List("just1"))
    assert(proofsEqual(results.head._2, proof))
  }

  test("Serialization: proofsToDataStream with multiple theorems") {
    val proof1 = new SCProof(
      IndexedSeq(Hypothesis(Sequent(SSet(a), SSet(a)), a)),
      IndexedSeq.empty
    )
    val proof2 = new SCProof(
      IndexedSeq(Hypothesis(Sequent(SSet(b), SSet(b)), b)),
      IndexedSeq.empty
    )

    val treeBaos = new ByteArrayOutputStream()
    val proofBaos = new ByteArrayOutputStream()
    val treesDOS = new DataOutputStream(treeBaos)
    val proofDOS = new DataOutputStream(proofBaos)

    proofsToDataStream(
      treesDOS,
      proofDOS,
      Seq(
        ("thm1", proof1, List.empty),
        ("thm2", proof2, List.empty)
      )
    )
    treesDOS.flush()
    proofDOS.flush()

    val treesDIS = new DataInputStream(new ByteArrayInputStream(treeBaos.toByteArray))
    val proofDIS = new DataInputStream(new ByteArrayInputStream(proofBaos.toByteArray))

    val results = proofsFromDataStream(treesDIS, proofDIS)
    assert(results.size == 2)
    assert(results(0)._1 == "thm1")
    assert(results(1)._1 == "thm2")
    assert(proofsEqual(results(0)._2, proof1))
    assert(proofsEqual(results(1)._2, proof2))
  }

  test("Serialization: LeftSubstEq round-trip") {
    val feq = Application(Application(equality, x), y)
    val px = Application(p, x)
    val py = Application(p, y)
    val v = Variable("v", Ind)
    val lambdaPhi = (Seq(v), Application(p, v): Expression)
    val premise = Sequent(SSet(px), SSet(px))
    val bot = Sequent(SSet(feq, py), SSet(px))
    val proof = new SCProof(
      IndexedSeq(
        Hypothesis(premise, px),
        LeftSubstEq(bot, 0, Seq((x, y)), lambdaPhi)
      ),
      IndexedSeq.empty
    )

    val treeBaos = new ByteArrayOutputStream()
    val proofBaos = new ByteArrayOutputStream()
    proofsToDataStream(new DataOutputStream(treeBaos), new DataOutputStream(proofBaos), Seq(("t", proof, List.empty)))

    val results = proofsFromDataStream(
      new DataInputStream(new ByteArrayInputStream(treeBaos.toByteArray)),
      new DataInputStream(new ByteArrayInputStream(proofBaos.toByteArray))
    )
    assert(proofsEqual(results.head._2, proof))
  }

  test("Serialization: RightSubstEq round-trip") {
    val feq = Application(Application(equality, x), y)
    val px = Application(p, x)
    val py = Application(p, y)
    val v = Variable("v", Ind)
    val lambdaPhi = (Seq(v), Application(p, v): Expression)
    val premise = Sequent(SSet.empty, SSet(px))
    val bot = Sequent(SSet(feq), SSet(py))
    val proof = new SCProof(
      IndexedSeq(
        Weakening(premise, -1),
        RightSubstEq(bot, 0, Seq((x, y)), lambdaPhi)
      ),
      IndexedSeq(premise)
    )

    val treeBaos = new ByteArrayOutputStream()
    val proofBaos = new ByteArrayOutputStream()
    proofsToDataStream(new DataOutputStream(treeBaos), new DataOutputStream(proofBaos), Seq(("t", proof, List.empty)))

    val results = proofsFromDataStream(
      new DataInputStream(new ByteArrayInputStream(treeBaos.toByteArray)),
      new DataInputStream(new ByteArrayInputStream(proofBaos.toByteArray))
    )
    assert(proofsEqual(results.head._2, proof))
  }
}
