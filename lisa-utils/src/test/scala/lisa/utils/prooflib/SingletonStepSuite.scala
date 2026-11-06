package lisa.utils.prooflib

import lisa.kernel.proof.{RunningTheory, SCProofChecker}
import lisa.utils.fol.FOL.*
import lisa.utils.prooflib.BasicStepTactic.*
import org.scalatest.funsuite.AnyFunSuite

class SingletonStepSuite extends AnyFunSuite:
  private object TestLibrary extends Library:
    val theory = new RunningTheory

  import TestLibrary.*
  private given TestLibrary.type = TestLibrary
  private given OutputManager = new OutputManager:
    val stringWriter = java.io.Writer.nullWriter()
    def finishOutput(exception: Exception): Nothing = throw exception

  private val p, q = variable[Prop]
  private lazy val owner = Theorem(p |- p) { have(thesis) by Hypothesis }
  private lazy val other = Theorem(p |- p) { have(thesis) by Hypothesis }

  test("store premise-free steps directly and retain multi-step groups"):
    val proof = new BaseProof(owner.asInstanceOf[THMFromProof])
    given proof.type = proof
    val leaf = have(p |- p) by Hypothesis
    assert(leaf.scps.isInstanceOf[SC.Hypothesis])
    val body = Seq(SC.Restate(leaf.innerBot, -1), SC.Restate(leaf.innerBot, 0))
    val grouped = proof.newProofStep(proof.ValidProofTactic(leaf.bot, body, Seq(leaf))(using Restate))
    val wrapper = grouped.scps.asInstanceOf[SC.SCSubproof]
    assert(wrapper.sp.steps == body && wrapper.premises == Seq(leaf.position))
    assert(SCProofChecker.checkSCProof(proof.toSCProof).isValid)

  test("remap reordered and repeated imports without changing the judgement"):
    val proof = new BaseProof(owner.asInstanceOf[THMFromProof])
    given proof.type = proof
    val local = have(p |- p) by Hypothesis
    proof.sequentAndIntOfFact(other)
    val goal = p |- ((p /\ p) /\ p)
    val raw = SC.RightAnd(goal.underlying, Seq(-3, -2, -1), Seq.fill(3)(p.underlying))
    val judgement = proof.ValidProofTactic(goal, Seq(raw), Seq(owner, local, owner))(using RightAnd)
    val result = proof.newProofStep(judgement)
    assert(result.scps.premises == Seq(-2, local.position, -2))
    assert(raw.premises == Seq(-3, -2, -1))
    assert(judgement.scps == Seq(raw))
    assert(proof.getImports.size == 2)
    assert(SCProofChecker.checkSCProof(proof.toSCProof).isValid)

  test("resolve instantiated facts before assigning the step position"):
    val proof = new BaseProof(owner.asInstanceOf[THMFromProof])
    val instantiated = proof.InstantiatedFact(owner, Seq(p := q))
    val goal = q |- q
    val result = proof.newProofStep(proof.ValidProofTactic(goal, Seq(SC.Restate(goal.underlying, -1)), Seq(instantiated))(using Restate))
    assert(result.position == 1)
    assert(result.scps.premises == Seq(0))
    assert(proof.getSteps.head.innerBot == goal.underlying)
    assert(SCProofChecker.checkSCProof(proof.toSCProof).isValid)

  test("remap an existing subproof without wrapping it again or changing its body"):
    val proof = new BaseProof(owner.asInstanceOf[THMFromProof])
    given proof.type = proof
    val local = have(p |- p) by Hypothesis
    val inner = K.SCProof(Vector(SC.Restate(local.innerBot, -1)), Vector(local.innerBot))
    val raw = SC.SCSubproof(inner, Seq(-1))
    val result = proof.newProofStep(proof.ValidProofTactic(local.bot, Seq(raw), Seq(local))(using Restate))
    val mapped = result.scps.asInstanceOf[SC.SCSubproof]
    assert(mapped.sp eq inner)
    assert(mapped.premises == Seq(local.position))
    assert(inner.steps.head.premises == Seq(-1))
    assert(SCProofChecker.checkSCProof(proof.toSCProof).isValid)

  test("keep self and forward references invalid after shifting indices"):
    for index <- Seq(0, 1) do
      val proof = new BaseProof(owner.asInstanceOf[THMFromProof])
      given proof.type = proof
      have(p |- p) by Hypothesis
      val goal = p |- p
      val result = proof.newProofStep(proof.ValidProofTactic(goal, Seq(SC.Restate(goal.underlying, index)), Nil)(using Restate))
      assert(result.scps.premises == Seq(result.position + index))
      assert(!SCProofChecker.checkSCProof(proof.toSCProof).isValid)
    val proof = new BaseProof(owner.asInstanceOf[THMFromProof])
    val goal = p |- p
    intercept[IndexOutOfBoundsException]:
      proof.newProofStep(proof.ValidProofTactic(goal, Seq(SC.Restate(goal.underlying, -2)), Seq(owner))(using Restate))

  test("require primitive rules to accept the actual parent sequents"):
    val proof = new BaseProof(owner.asInstanceOf[THMFromProof])
    given proof.type = proof
    val goal = p |- p
    val equivalent = Sequent(Set.empty, Set(p ==> p))
    val exposed = proof.newProofStep(proof.ValidProofTactic(goal, Seq(SC.RestateTrue(equivalent.underlying)), Nil)(using Restate))
    val normal = have(goal) by Hypothesis
    val cut = SC.Cut(goal.underlying, -1, -2, p.underlying)
    val wrapped = SC.SCSubproof(K.SCProof(Vector(cut), Vector(goal.underlying, goal.underlying)), Seq(exposed.position, normal.position))
    assert(SCProofChecker.checkSCProof(K.SCProof(Vector(exposed.scps, normal.scps, wrapped))).isValid)
    val direct = proof.newProofStep(proof.ValidProofTactic(goal, Seq(cut), Seq(exposed, normal))(using Cut))
    assert(direct.scps.isInstanceOf[SC.Cut])
    assert(direct.scps.premises == Seq(exposed.position, normal.position))
    assert(!SCProofChecker.checkSCProof(proof.toSCProof).isValid)
