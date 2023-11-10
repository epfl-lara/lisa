package lisa.test.utils

import org.scalatest.funsuite.AnyFunSuite
import lisa.utils.Serialization.*
import lisa.utils.K
import lisa.utils.K.|-
import lisa.utils.K.getJustification
import lisa.test.automation.TableauTest
import java.io._

//import lisa.automation.TableauTest

class SerializationTest extends AnyFunSuite {

  val theory = K.RunningTheory()

  def test(proof:K.SCProof, name:String, theory: K.RunningTheory, justs: List[theory.Justification]): Unit = {
    thmToFile("test", theory, name, proof, justs)
    val thm = thmFromFile("test", theory)
    File("test.trees").delete()
    File("test.proof").delete()
  }

  test("exporting a proof to a list of string and back should work, propositional tableau") {
    val proofs = TableauTest.posi
    proofs.foreach(p => 
        try {
            val proof = p._4.get
            val no = p._1
            test(proof, "posi" + no, theory, Nil)
        }
        catch {
            case e: Exception => println("Exception thrown for test case posi" + p._1 )
                throw e
        }
    )
  }

  test("exporting a proof to a list of string and back should work, propositional OL tautology") {
    val proofs = TableauTest.posi
    proofs.foreach(p => 
        try {
            val formula = p._2
            val no = p._1
            val proof = lisa.automation.kernel.OLPropositionalSolver.solveSequent(() |- formula.underlying) match {
                case Left(proof) => proof
                case Right(_) => throw new Exception("OLPropositionalSolver failed to prove a tautology")
            }
            test(proof, "posiOL" + no, theory, Nil)
        }
        catch {
            case e: Exception => println("Exception thrown for test case posi" + p._1 )
                throw e
        }
    )
  }

  test("exporting a proof to a list of string and back should work, first order quantifier free tableau") {
    val proofs = TableauTest.posqf
    proofs.foreach(p => 
        try {
            val proof = p._4.get
            val no = p._1
            test(proof, "posqf" + no, theory, Nil)
        }
        catch {
            case e: Exception => println("Exception thrown for test case posqf" + p._1 )
                throw e
        }
    )
  }

  test("exporting a proof to a list of string and back should work, first order quantifier free OL tautology") {
    val proofs = TableauTest.posqf
    proofs.foreach(p => 
        try {
            val formula = p._2
            val no = p._1
            val proof = lisa.automation.kernel.OLPropositionalSolver.solveSequent(() |- formula.underlying) match {
                case Left(proof) => proof
                case Right(_) => throw new Exception("OLPropositionalSolver failed to prove a tautology")
            }
            test(proof, "posqfOL" + no, theory, Nil)
        }
        catch {
            case e: Exception => println("Exception thrown for test case posqf" + p._1 )
                throw e
        }
    )
  }

  test("exporting a proof to a list of string and back should work, first order easy tableau") {
    val proofs = TableauTest.poseasy
    proofs.foreach(p => 
        try {
            val proof = p._4.get
            val no = p._1
            test(proof, "poseasy" + no, theory, Nil)
        }
        catch {
            case e: Exception => println("Exception thrown for test case poseasy" + p._1 )
                throw e
        }
        
    )
  }

  test("exporting a proof to a list of string and back should work, first order hard tableau") {
    val proofs = TableauTest.poshard
    proofs.foreach(p => 
        try {
            val proof = p._4.get
            val no = p._1
            test(proof, "poshard" + no, theory, Nil)
        }
        catch {
            case e: Exception => println("Exception thrown for test case poshard" + p._1 )
                throw e
        }
    )
  }



  test("exporting a proof to a list of string and back should work, with imports") {
    import lisa.mathematics.settheory.SetTheory as ST
    val thms = List(
        //("russelsParadox", ST.russelsParadox), 
        ("setUnionMembership", ST.setUnionMembership), 
        ("inductiveSetExists", ST.inductiveSetExists), 
        ("setWithNoElementsIsEmpty", ST.setWithNoElementsIsEmpty), 
        ("emptySetIsItsOwnOnlySubset", ST.emptySetIsItsOwnOnlySubset)
    )
    thms.foreach(thm => 
        try {
            val proof = thm._2.proof.toSCProof
            val justifs = thm._2.proof.justifications.map(_.innerJustification)

            test(proof, thm._1 + "_test", ST.theory, justifs)
        }
        catch {
            case e: Exception => println("Exception thrown for string encoding-decoding of theorem " + thm._1 )
                throw e
        }
    )
  }



}