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
import java.io.EOFException
import scala.collection.mutable.{Map => MutMap}

/**
 * Tests for serialization and deserialization of proofs
 */
class SerializationTest extends AnyFunSuite with TestUtils {

  test("Serialization: leaf helpers use the same tags as proof trees") {
    val bytes = new ByteArrayOutputStream
    val out = new DataOutputStream(bytes)
    variableToDOS(x, out)
    assert(bytes.toByteArray.head == 0)
    bytes.reset()
    constantToDos(a, out)
    assert(bytes.toByteArray.head == 1)
  }

  test("Serialization: reject a truncated tree entry") {
    val trees = new ByteArrayOutputStream
    val proofs = new ByteArrayOutputStream
    val proof = SCProof(Hypothesis(Sequent(Set(a), Set(a)), a))
    proofsToDataStream(new DataOutputStream(trees), new DataOutputStream(proofs), Seq(("truncated", proof, Nil)))
    intercept[EOFException] {
      proofsFromDataStream(
        new DataInputStream(new ByteArrayInputStream(trees.toByteArray.dropRight(1))),
        new DataInputStream(new ByteArrayInputStream(proofs.toByteArray))
      )
    }
  }

  test("Serialization: reject an unknown tree tag") {
    intercept[IllegalArgumentException] {
      proofsFromDataStream(
        new DataInputStream(new ByteArrayInputStream(Array[Byte](99))),
        new DataInputStream(new ByteArrayInputStream(Array.emptyByteArray))
      )
    }
  }

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
      IndexedSeq(Hypothesis(Sequent(Set(a), Set(a)), a)),
      IndexedSeq.empty
    )
  )

  // RestateTrue: |- top
  proofRT(
    "RestateTrue proof",
    new SCProof(
      IndexedSeq(RestateTrue(Sequent(Set.empty, Set(top)))),
      IndexedSeq.empty
    )
  )

  // Weakening with import
  proofRT(
    "Weakening with import",
    new SCProof(
      IndexedSeq(Weakening(Sequent(Set(a, b), Set(a)), -1)),
      IndexedSeq(Sequent(Set(a), Set(a)))
    )
  )

  // Cut proof
  proofRT(
    "Cut proof", {
      val s1 = Sequent(Set(a), Set(a, b))
      val s2 = Sequent(Set(a, b), Set(b))
      val bot = Sequent(Set(a), Set(b))
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
      val premise = Sequent(Set(phi, psi), Set(phi))
      val bot = Sequent(Set(Application(Application(and, phi), psi)), Set(phi))
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
      val premise = Sequent(Set(phi), Set(phi, psi))
      val bot = Sequent(Set(phi), Set(Application(Application(or, phi), psi)))
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
      val premise = Sequent(Set.empty, Set(phi))
      val notPhi = Application(neg, phi)
      val bot = Sequent(Set(notPhi), Set(phi))
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
      val premise = Sequent(Set(phi), Set.empty)
      val notPhi = Application(neg, phi)
      val bot = Sequent(Set(phi), Set(notPhi))
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
      val premise = Sequent(Set(phi), Set(psi))
      val impl = Application(Application(implies, phi), psi)
      val bot = Sequent(Set.empty, Set(impl))
      new SCProof(
        IndexedSeq(
          Weakening(premise, -1),
          RightImplies(bot, 0, phi, psi)
        ),
        IndexedSeq(Sequent(Set(phi), Set(psi)))
      )
    }
  )

  // LeftImplies
  proofRT(
    "LeftImplies proof", {
      val phi = a; val psi = b
      val s1 = Sequent(Set(phi), Set(phi))
      val s2 = Sequent(Set(psi), Set(psi))
      val impl = Application(Application(implies, phi), psi)
      val bot = Sequent(Set(phi, impl), Set(phi, psi))
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
      IndexedSeq(Sorry(Sequent(Set(a), Set(b)))),
      IndexedSeq.empty
    )
  )

  // Restate
  proofRT(
    "Restate proof",
    new SCProof(
      IndexedSeq(
        Hypothesis(Sequent(Set(a), Set(a)), a),
        Restate(Sequent(Set(a), Set(a)), 0)
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
      val premise = Sequent(Set(implPhi), Set(phi))
      val bot = Sequent(Set(iffPhi), Set(phi))
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
      val s1 = Sequent(Set.empty, Set(impl1))
      val s2 = Sequent(Set.empty, Set(impl2))
      val bot = Sequent(Set.empty, Set(iffExpr))
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
      val s1 = Sequent(Set(phi), Set(c))
      val s2 = Sequent(Set(psi), Set(c))
      val bot = Sequent(Set(orExpr), Set(c))
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
      val s1 = Sequent(Set(c), Set(phi))
      val s2 = Sequent(Set(c), Set(psi))
      val bot = Sequent(Set(c), Set(andExpr))
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
        IndexedSeq(RightRefl(Sequent(Set.empty, Set(eq)), eq)),
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
      val premise = Sequent(Set(py), Set(py))
      val bot = Sequent(Set(forallPx), Set(py))
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
      val premise = Sequent(Set(py), Set(py))
      val bot = Sequent(Set(py), Set(existsPx))
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
      val premise = Sequent(Set.empty, Set(px))
      val bot = Sequent(Set.empty, Set(forallPx))
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
      val premise = Sequent(Set(px), Set.empty)
      val bot = Sequent(Set(existsPx), Set.empty)
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
      val premise = Sequent(Set(xv), Set(xv))
      val bot = Sequent(Set(a), Set(a))
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
        Hypothesis(Sequent(Set(a), Set(a)), a),
        Hypothesis(Sequent(Set(b), Set(b)), b),
        Cut(Sequent(Set(a), Set(b)), 0, 1, a)
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
      IndexedSeq(Hypothesis(Sequent(Set(a), Set(a)), a)),
      IndexedSeq.empty
    )
    val proof2 = new SCProof(
      IndexedSeq(Hypothesis(Sequent(Set(b), Set(b)), b)),
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
    val premise = Sequent(Set(px), Set(px))
    val bot = Sequent(Set(feq, py), Set(px))
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

  test("Serialization: resolve definitions whose identifiers contain underscores") {
    val theory = new lisa.kernel.proof.RunningTheory
    val constant = Constant(Identifier("defined_with_underscores", 3), Prop)
    val definition = theory.makeDefinition(constant, top, Seq.empty).get
    val statement = theory.sequentFromJustification(definition)
    val proof = SCProof(IndexedSeq(Restate(statement, -1)), IndexedSeq(statement))
    val trees = new ByteArrayOutputStream
    val steps = new ByteArrayOutputStream
    thmsToDataStream(new DataOutputStream(trees), new DataOutputStream(steps), theory,
      List(("test.underscore", proof, List(("test", definition)))))
    val read = thmsFromDataStream(
      new DataInputStream(new ByteArrayInputStream(trees.toByteArray)),
      new DataInputStream(new ByteArrayInputStream(steps.toByteArray)),
      theory
    )
    assert(read.head._1.proposition == statement)
    assert(lisa.kernel.proof.SCProofChecker.checkSCProof(read.head._2).isValid)
  }

  test("Serialization: RightSubstEq round-trip") {
    val feq = Application(Application(equality, x), y)
    val px = Application(p, x)
    val py = Application(p, y)
    val v = Variable("v", Ind)
    val lambdaPhi = (Seq(v), Application(p, v): Expression)
    val premise = Sequent(Set.empty, Set(px))
    val bot = Sequent(Set(feq), Set(py))
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
