package lisa.utils

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.Sequent
import lisa.utils.Serialization.*
import lisa.utils.kernel.*
import org.scalatest.funsuite.AnyFunSuite

import java.io.*
import scala.collection.mutable.{Map => MutMap}

class SerializationTest extends AnyFunSuite:
  private val x = Variable(Identifier("x"), Ind)
  private val y = Variable(Identifier("y"), Ind)
  private val f = Constant(Identifier("f"), Arrow(Ind, Ind))
  private val p = Constant(Identifier("p"), Prop)
  private val q = Constant(Identifier("q"), Prop)
  private val statement = Sequent(Set(p), Set(q))

  private def hex(bytes: Array[Byte]): String = bytes.map("%02x".format(_)).mkString

  private def expressionBytes(expression: Expression): (Array[Byte], Int) =
    val bytes = ByteArrayOutputStream()
    val dos = DataOutputStream(bytes)
    val lines = MutMap[Long, Line]()
    val line = lineOfExpr(expression, dos, lines)
    dos.flush()
    (bytes.toByteArray, line)

  private def proofBytes(proof: LinearProof): (Array[Byte], Array[Byte]) =
    val trees = ByteArrayOutputStream()
    val steps = ByteArrayOutputStream()
    val treesDOS = DataOutputStream(trees)
    val stepsDOS = DataOutputStream(steps)
    proofToDataStream(treesDOS, stepsDOS, proof)
    treesDOS.flush()
    stepsDOS.flush()
    (trees.toByteArray, steps.toByteArray)

  private def roundTrip(proof: LinearProof): LinearProof =
    val (trees, steps) = proofBytes(proof)
    proofFromDataStream(
      DataInputStream(ByteArrayInputStream(trees)),
      DataInputStream(ByteArrayInputStream(steps))
    )

  private def stepsEqual(left: ProofStep, right: ProofStep): Boolean = (left, right) match
    case (LeftOr(ls, lp, le), LeftOr(rs, rp, re)) => ls == rs && lp.sameElements(rp) && le == re
    case (RightAnd(ls, lp, le), RightAnd(rs, rp, re)) => ls == rs && lp.sameElements(rp) && le == re
    case _ => left == right

  private def proofsEqual(left: LinearProof, right: LinearProof): Boolean =
    left.imports.sameElements(right.imports) &&
      left.steps.length == right.steps.length &&
      left.steps.zip(right.steps).forall(stepsEqual)

  test("legacy variable tree bytes remain unchanged"):
    val (bytes, line) = expressionBytes(x)
    assert(line == 0)
    assert(hex(bytes) == "0000017800000000000154")

  test("legacy compound tree bytes and DAG line order remain unchanged"):
    val expression = Lambda(x, Application(f, x))
    val (bytes, line) = expressionBytes(expression)
    assert(line == 3)
    assert(
      hex(bytes) ==
        "0000017800000000000154" +
        "010001660000000000033e5454" +
        "030000000100000000" +
        "020000000000000002"
    )

  test("sort encoding remains unchanged"):
    assert(typeToString(Ind) == "T")
    assert(typeToString(Prop) == "F")
    assert(typeToString(Arrow(Ind, Arrow(Ind, Prop))) == ">T>TF")
    assert(typeFromString(">T>TF") == (Arrow(Ind, Arrow(Ind, Prop)), ""))

  test("self-contained sequent round trip"):
    val original = Sequent(Set(p, implies(p)(q)), Set(q))
    val bytes = ByteArrayOutputStream()
    sequentToDOS(original, DataOutputStream(bytes))
    val restored = sequentFromDIS(DataInputStream(ByteArrayInputStream(bytes.toByteArray)))
    assert(restored == original)

  test("legacy proof-step tags remain fixed and new tags are appended"):
    assert(
      Seq(
        Tag.restate,
        Tag.restateTrue,
        Tag.hypothesis,
        Tag.cut,
        Tag.leftAnd,
        Tag.leftOr,
        Tag.leftImplies,
        Tag.leftIff,
        Tag.leftNot,
        Tag.leftForall,
        Tag.leftExists,
        Tag.rightAnd,
        Tag.rightOr,
        Tag.rightImplies,
        Tag.rightIff,
        Tag.rightNot,
        Tag.rightForall,
        Tag.rightExists,
        Tag.rightEpsilon,
        Tag.weakening,
        Tag.beta,
        Tag.leftRefl,
        Tag.rightRefl,
        Tag.leftSubstEq,
        Tag.rightSubstEq,
        Tag.instSchema,
        Tag.scSubproof,
        Tag.sorry
      ) == Seq(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28)
    )
    assert(Seq(Tag.axiom, Tag.assume, Tag.discharge, Tag.definition) == Seq(29, 30, 31, 32))

  test("one legacy Hypothesis proof has byte-identical payload"):
    val proof = LinearProof(Array(Hypothesis(Sequent(Set(p), Set(p)), p)), Array.empty)
    val (trees, steps) = proofBytes(proof)
    assert(hex(trees) == "0100017000000000000146")
    assert(hex(steps) == "00000000000000010200010000000000010000000000000000")

  test("all linear proof steps round trip"):
    val phi = Application(Constant(Identifier("P"), Arrow(Ind, Prop)), x)
    val steps: Array[ProofStep] = Array(
      Restate(statement, -1),
      RestateTrue(statement),
      Hypothesis(statement, p),
      Cut(statement, 0, 1, p),
      LeftAnd(statement, 0, p, q),
      LeftOr(statement, Array(0, 1), Seq(p, q)),
      LeftImplies(statement, 0, 1, p, q),
      LeftIff(statement, 0, p, q),
      LeftNot(statement, 0, p),
      LeftForall(statement, 0, phi, x, y),
      LeftExists(statement, 0, phi, x),
      RightAnd(statement, Array(0, 1), Seq(p, q)),
      RightOr(statement, 0, p, q),
      RightImplies(statement, 0, p, q),
      RightIff(statement, 0, 1, p, q),
      RightNot(statement, 0, p),
      RightForall(statement, 0, phi, x),
      RightExists(statement, 0, phi, x, y),
      RightEpsilon(statement, 0, phi, x, y),
      Weakening(statement, 0),
      LeftRefl(statement, 0, phi),
      RightRefl(statement, phi),
      LeftSubstEq(statement, 0, Seq(x -> y), (Seq(x), phi)),
      RightSubstEq(statement, 0, Seq(x -> y), (Seq(x), phi)),
      InstSchema(statement, 0, Map(x -> y)),
      Sorry(statement),
      Axiom(statement),
      Assume(statement),
      Discharge(statement, 0, -1),
      Definition(statement, f, Seq(x), x)
    )
    val original = LinearProof(steps, Array(statement))
    assert(proofsEqual(original, roundTrip(original)))

  test("legacy named-proof envelope round trip"):
    val original = LinearProof(Array(Sorry(statement)), Array(statement))
    val trees = ByteArrayOutputStream()
    val steps = ByteArrayOutputStream()
    proofsToDataStream(
      DataOutputStream(trees),
      DataOutputStream(steps),
      Seq(("example", original, List("axiom-name")))
    )
    val restored = proofsFromDataStream(
      DataInputStream(ByteArrayInputStream(trees.toByteArray)),
      DataInputStream(ByteArrayInputStream(steps.toByteArray))
    )
    assert(restored.head._1 == "example")
    assert(restored.head._3 == List("axiom-name"))
    assert(proofsEqual(original, restored.head._2))
