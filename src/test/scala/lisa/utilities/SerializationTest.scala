import org.scalatest.funsuite.AnyFunSuite
import lisa.utils.Serialization.*
import lisa.utils.K
import lisa.utils.K.|-
import lisa.utils.K.getJustification

//import lisa.automation.TableauTest

class SerializationTest extends AnyFunSuite {
/*
  test("exporting a proof to a list of string and back should work, propositional tableau") {
    val proofs = TableauTest.posi
    proofs.foreach(p => 
        try {
            val proof = p._4.get
            val no = p._1
            val lines = flatProofToString(proof, "posi" + no)
            val proof2 = SeqStringToProof(lines)
            assert(K.SCProofChecker.checkSCProof(proof2._1).isValid, "proof corresponding to test case posi" + no + " is not valid")
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
            val lines = flatProofToString(proof, "posi" + no)
            val proof2 = SeqStringToProof(lines)
            assert(K.SCProofChecker.checkSCProof(proof2._1).isValid, "proof corresponding to test case posiOL" + no + " is not valid")
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
            val lines = flatProofToString(proof, "posqf" + no)
            val proof2 = SeqStringToProof(lines)
            assert(K.SCProofChecker.checkSCProof(proof2._1).isValid, "proof corresponding to test case posqf" + no + " is not valid")
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
            val lines = flatProofToString(proof, "posqf" + no)
            val proof2 = SeqStringToProof(lines)
            assert(K.SCProofChecker.checkSCProof(proof2._1).isValid, "proof corresponding to test case posqfOL" + no + " is not valid")
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
            val lines = flatProofToString(proof, "poseasy" + no)
            val proof2 = SeqStringToProof(lines)
            assert(K.SCProofChecker.checkSCProof(proof2._1).isValid, "proof corresponding to test case poseasy" + no + " is not valid")
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
            val lines = flatProofToString(proof, "poshard" + no)
            val proof2 = SeqStringToProof(lines)
            assert(K.SCProofChecker.checkSCProof(proof2._1).isValid, "proof corresponding to test case poshard" + no + " is not valid")
        }
        catch {
            case e: Exception => println("Exception thrown for test case poshard" + p._1 )
                throw e
        }
    )
  }

*/

  //TODO: Finish this. Deal with justifications, create theorems (unless they are already in the library)

  test("exporting a proof to a list of string and back should work, with imports") {
    import lisa.mathematics.settheory.SetTheory as ST
    println("START THEOREMS_________________________________________")
    val thms = List(
        ("russelsParadox", ST.russelsParadox), 
        ("setUnionMembership", ST.setUnionMembership), 
        ("inductiveSetExists", ST.inductiveSetExists), 
        ("setWithNoElementsIsEmpty", ST.setWithNoElementsIsEmpty), 
        ("emptySetIsItsOwnOnlySubset", ST.emptySetIsItsOwnOnlySubset)
    )
    thms.foreach(thm => 
        try {
            val proof = thm._2.proof.toSCProof
            val justifs = thm._2.proof.justifications.map(_.innerJustification)

            val lines = thmToString(ST.theory, thm._2.innerJustification, proof, justifs)

            val proof2 = SeqStringToProof(lines)
            proof2._3.foreach(j => println(j))
            val justifs2 = proof2._3.map(ST.theory.getJustification)
            assert(K.SCProofChecker.checkSCProof(proof2._1).isValid && justifs2 == justifs, "decoded proof of theorem " + thm._1 + " is not valid")
        }
        catch {
            case e: Exception => println("Exception thrown for string encoding-decoding of theorem " + thm._1 )
                throw e
        }
    )
  }



}