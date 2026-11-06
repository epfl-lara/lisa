package lisa.utils.prooflib

import lisa.kernel.proof.{RunningTheory, SCProofChecker}
import lisa.utils.fol.FOL.*
import lisa.utils.prooflib.BasicStepTactic.*
import org.scalatest.funsuite.AnyFunSuite

class ImportIndexSuite extends AnyFunSuite:
  private object TestLibrary extends Library:
    val theory = new RunningTheory

  import TestLibrary.*
  private given TestLibrary.type = TestLibrary
  private given OutputManager = new OutputManager:
    val stringWriter = java.io.Writer.nullWriter()
    def finishOutput(exception: Exception): Nothing = throw exception

  private val p = variable[Prop]
  private lazy val first = Theorem(p |- p) { have(thesis) by Hypothesis }
  private lazy val second = Theorem(p |- p) { have(thesis) by Hypothesis }

  private def colliding(theorem: THM): THM =
    new THMFromKernel(theorem.statement, theorem.fullName, theorem.kind,
      theorem.innerJustification, theorem.proofStatistics, theorem.wasCached, theorem.sorryDependencies):
      override def hashCode(): Int = 0

  test("read statements without importing and keep negative indices stable"):
    val proof = new BaseProof(first.asInstanceOf[THMFromProof])
    given proof.type = proof
    assert(proof.sequentOfFact(first) == first.statement)
    assert(proof.getImports.isEmpty)
    assert(proof.sequentAndIntOfFact(first)._2 == -1)
    val snapshot = proof.getImports
    assert(proof.sequentAndIntOfFact(second)._2 == -2)
    assert(proof.sequentAndIntOfFact(first)._2 == -1)
    assert(snapshot.size == 1 && proof.getImports.size == 2)
    assert(proof.sequentOfFact(-1) == first.statement)
    assert(proof.sequentOfFact(-2) == second.statement)
    have(first)
    assert(SCProofChecker.checkSCProof(proof.toSCProof).isValid)

  test("distinguish justifications with equal hashes and equal statements"):
    val proof = new BaseProof(first.asInstanceOf[THMFromProof])
    given proof.type = proof
    val a = colliding(first)
    val b = colliding(second)
    assert(a.hashCode == b.hashCode && a.statement == b.statement)
    assert(proof.sequentAndIntOfFact(a)._2 == -1)
    assert(proof.sequentAndIntOfFact(b)._2 == -2)
    assert(proof.sequentAndIntOfFact(a)._2 == -1)
    assert(proof.getImports.size == 2)
    have(a)
    assert(SCProofChecker.checkSCProof(proof.toSCProof).isValid)

  test("interleave parent steps and justifications without sharing import indices"):
    val parent = new BaseProof(first.asInstanceOf[THMFromProof])
    given parent.type = parent
    val a = have(p |- p) by Hypothesis
    val b = have(p |- p) by Hypothesis
    val child = parent.newInnerProof(None)
    assert(child.sequentOfFact(a) == a.bot)
    assert(child.getImports.isEmpty)
    assert(child.sequentAndIntOfFact(a)._2 == -1)
    assert(child.sequentAndIntOfFact(first)._2 == -2)
    assert(child.sequentAndIntOfFact(b)._2 == -3)
    assert(child.sequentAndIntOfFact(second)._2 == -4)
    assert(child.sequentAndIntOfFact(first)._2 == -2)
    assert(child.sequentAndIntOfFact(a)._2 == -1)
    assert(parent.getImports.isEmpty)
    val judgement = child.ValidProofTactic(a.bot, Seq(SC.Restate(a.bot.underlying, -1)), Seq(a))(using Restate)
    child.newProofStep(judgement)
    assert(SCProofChecker.checkSCProof(child.toSCProof).isValid)
