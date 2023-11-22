package lisa.test.utils

import lisa.automation.Tautology
import lisa.test.automation.TableauTest
import lisa.utils.K
import lisa.utils.K.getJustification
import lisa.utils.K.|-
import lisa.utils.Serialization.*
import org.scalatest.funsuite.AnyFunSuite

import java.io._

//import lisa.automation.TableauTest

class SerializationTest extends AnyFunSuite {

  val theory = K.RunningTheory()

  val testfile = "SerializationTest" // chances of collision with an existing file is quite low

  def test(proof: K.SCProof, name: String, theory: K.RunningTheory, justs: List[theory.Justification]) = {
    thmsToFile(testfile, theory, List((name, proof, justs.map(("test", _)))))
    val thm = thmsFromFile(testfile, theory)
    File(testfile + ".trees").delete()
    File(testfile + ".proof").delete()
    thm.head
  }

  def testMulti(theory: K.RunningTheory, thms: List[(String, K.SCProof, List[theory.Justification])]) = {
    thmsToFile(testfile, theory, thms.map(thm => (thm._1, thm._2, thm._3.map(("test", _)))))
    val thm = thmsFromFile(testfile, theory)
    File(testfile + ".trees").delete()
    File(testfile + ".proof").delete()
    thm
  }

  test("exporting a proof to a file and back should work, propositional tableau") {
    val proofs = TableauTest.posi
    proofs.foreach(p =>
      try {
        val proof = p._4.get
        val no = p._1
        test(proof, "posi" + no, theory, Nil)
      } catch {
        case e: Exception =>
          println("Exception thrown for test case posi" + p._1)
          throw e
      }
    )
  }

  test("exporting a proof to a file and back should work, propositional OL tautology") {
    val proofs = TableauTest.posi
    proofs.foreach(p =>
      try {
        val formula = p._2
        val no = p._1
        val proof = Tautology.solveSequent(() |- formula.underlying) match {
          case Left(proof) => proof
          case Right(_) => throw new Exception("OLPropositionalSolver failed to prove a tautology")
        }
        test(proof, "posiOL" + no, theory, Nil)
      } catch {
        case e: Exception =>
          println("Exception thrown for test case posi" + p._1)
          throw e
      }
    )
  }

  test("exporting a proof to a file and back should work, first order quantifier free tableau") {
    val proofs = TableauTest.posqf
    proofs.foreach(p =>
      try {
        val proof = p._4.get
        val no = p._1
        test(proof, "posqf" + no, theory, Nil)
      } catch {
        case e: Exception =>
          println("Exception thrown for test case posqf" + p._1)
          throw e
      }
    )
  }

  test("exporting a proof to a file and back should work, first order quantifier free OL tautology") {
    val proofs = TableauTest.posqf
    proofs.foreach(p =>
      try {
        val formula = p._2
        val no = p._1
        val proof = Tautology.solveSequent(() |- formula.underlying) match {
          case Left(proof) => proof
          case Right(_) => throw new Exception("OLPropositionalSolver failed to prove a tautology")
        }
        test(proof, "posqfOL" + no, theory, Nil)
      } catch {
        case e: Exception =>
          println("Exception thrown for test case posqf" + p._1)
          throw e
      }
    )
  }

  test("exporting a proof to a file and back should work, first order easy tableau") {
    val proofs = TableauTest.poseasy
    proofs.foreach(p =>
      try {
        val proof = p._4.get
        val no = p._1
        test(proof, "poseasy" + no, theory, Nil)
      } catch {
        case e: Exception =>
          println("Exception thrown for test case poseasy" + p._1)
          throw e
      }
    )
  }

  test("exporting a proof to a file and back should work, first order hard tableau") {
    val proofs = TableauTest.poshard
    proofs.foreach(p =>
      try {
        val proof = p._4.get
        val no = p._1
        test(proof, "poshard" + no, theory, Nil)
      } catch {
        case e: Exception =>
          println("Exception thrown for test case poshard" + p._1)
          throw e
      }
    )
  }

  test("exporting a proof to a file and back should work, with imports") {
    import lisa.maths.settheory.SetTheory as ST
    val thms = List(
      // ("russelsParadox", ST.russelsParadox),
      ("setUnionMembership", ST.setUnionMembership),
      ("inductiveSetExists", ST.inductiveSetExists),
      ("setWithNoElementsIsEmpty", ST.setWithNoElementsIsEmpty),
      ("emptySetIsItsOwnOnlySubset", ST.emptySetIsItsOwnOnlySubset)
    )
    thms.foreach(thm =>
      try {
        val proof = thm._2.kernelProof.get
        val justifs = thm._2.highProof.get.justifications.map(_.innerJustification)

        test(proof, thm._1 + "_test", ST.theory, justifs)
      } catch {
        case e: Exception =>
          println("Exception thrown for string encoding-decoding of theorem " + thm._1)
          throw e
      }
    )
  }

  test("exporting multiple theorems at once to a file and back should work") {
    import lisa.maths.settheory.SetTheory as ST
    val thms = List(
      // ("russelsParadox", ST.russelsParadox),
      ("setUnionMembership", ST.setUnionMembership),
      ("inductiveSetExists", ST.inductiveSetExists),
      ("setWithNoElementsIsEmpty", ST.setWithNoElementsIsEmpty),
      ("emptySetIsItsOwnOnlySubset", ST.emptySetIsItsOwnOnlySubset)
    )

    val thmBack = testMulti(
      ST.theory,
      thms.map(thm =>
        val proof = thm._2.kernelProof.get
        val justifs = thm._2.highProof.get.justifications.map(_.innerJustification)

        (thm._1, proof, justifs)
      )
    )
    assert(thmBack.length == thms.length)
    thmBack
      .zip(thms)
      .foreach(pair => {
        val thm = pair._1
        val thmOrig = pair._2
        assert(thm._1.name == thmOrig._1)
        assert(thm._1.proposition == thmOrig._2.innerJustification.proposition)
      })
  }

}
