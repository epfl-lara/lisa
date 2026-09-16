package lisa.automation

import lisa.SetTheoryLibrary
import lisa.SetTheoryLibrary.*
import lisa.utils.K
import lisa.utils.fol.FOL.*
import lisa.utils.prooflib.BasicStepTactic.*
import lisa.utils.prooflib.OutputManager
import org.scalatest.funsuite.AnyFunSuite

class SubstitutionContextSuite extends AnyFunSuite:
  private given SetTheoryLibrary.type = SetTheoryLibrary
  private given OutputManager = new OutputManager:
    val stringWriter = new java.io.StringWriter
    def finishOutput(exception: Exception): Nothing = throw exception

  private val x, y = variable[Ind]
  private val p = variable[Ind >>: Prop]
  private val q = variable[Prop]
  private val premise = Theorem(p(x) |- p(x)) { have(thesis) by Hypothesis }

  test("rewrite a premise under additional ambient assumptions"):
    val proof = new BaseProof(premise.asInstanceOf[THMFromProof])
    given proof.type = proof
    proof.addAssumption(q)
    val goal = Set(q, x === y, p(y)) |- p(y)
    val result = Substitution.Apply(x === y)(premise)(goal)
    assert(result.isValid)
    val step = have(result)
    assert(step.statement == goal)
    assert(K.SCProofChecker.checkSCProof(proof.toSCProof).isValid)
