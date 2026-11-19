package lisa.utils.prooflib

import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.SCProofChecker
import lisa.utils.fol.FOL._
import lisa.utils.prooflib.BasicStepTactic._
import org.scalatest.funsuite.AnyFunSuite

class SubstitutionTacticSuite extends AnyFunSuite:
  private object TestLibrary extends Library:
    val theory = new RunningTheory

  import TestLibrary.*
  private given TestLibrary.type = TestLibrary
  private given OutputManager = new OutputManager:
    val stringWriter = java.io.Writer.nullWriter()
    def finishOutput(exception: Exception): Nothing = throw exception

  private val p = variable[Prop]
  private val a, b, x, z = variable[Ind]
  private val P = variable[Ind >>: Prop]
  private val F, G = variable[Ind >>: Ind]
  private lazy val owner = Theorem(p |- p) { have(thesis) by Hypothesis }

  test("emit a single primitive with two remapped premises"):
    val proof = new BaseProof(owner.asInstanceOf[THMFromProof])
    given proof.type = proof
    val premise = have(P(a) |- P(a)) by Hypothesis
    val comparison = have((a === b) |- (a === b)) by Hypothesis
    val result = have((P(a), a === b) |- P(b)) by RightSubst.withParameters(using TestLibrary, proof)(Seq((a, b, Nil)), Seq(x) -> P(x))(premise, Seq(comparison))
    assert(result.scps.isInstanceOf[SC.RightSubst])
    assert(result.scps.premises == Seq(premise.position, comparison.position))
    assert(SCProofChecker.checkSCProof(proof.toSCProof).isValid)

  test("accept a proved comparison or an assumed pair on either side"):
    val proof = new BaseProof(owner.asInstanceOf[THMFromProof])
    given proof.type = proof
    val premise = have(P(a) |- P(a)) by Hypothesis
    val comparison = have((a === b) |- (a === b)) by Hypothesis
    have((P(a), a === b) |- P(b)) by RightSubst(using TestLibrary, proof)(comparison, x -> P(x))(premise)
    have((P(a), a === b) |- P(b)) by RightSubst(using TestLibrary, proof)(Seq(a -> b), Seq(x) -> P(x))(premise)
    have((P(b), a === b) |- P(a)) by LeftSubst(using TestLibrary, proof)(comparison, x -> P(x))(premise)
    assert(SCProofChecker.checkSCProof(proof.toSCProof).isValid)

  test("emit one simultaneous primitive with all remapped comparisons"):
    val proof = new BaseProof(owner.asInstanceOf[THMFromProof])
    given proof.type = proof
    val premise = have(P(a) /\ P(b) |- P(a) /\ P(b)) by Hypothesis
    val first = have(a === b |- a === b) by Hypothesis
    val second = have(b === a |- b === a) by Hypothesis
    val replacements = Seq((a, b, Seq.empty[Variable[?]]), (b, a, Seq.empty[Variable[?]]))
    val result = have((P(a) /\ P(b), a === b, b === a) |- (P(b) /\ P(a))) by
      RightSubst.withParameters(using TestLibrary, proof)(replacements, Seq(x, z) -> (P(x) /\ P(z)))(premise, Seq(first, second))
    assert(result.scps.isInstanceOf[SC.RightSubst])
    assert(result.scps.premises == Seq(premise.position, first.position, second.position))
    assert(SCProofChecker.checkSCProof(proof.toSCProof).isValid)

  test("instantiate a lifted equality proof"):
    val proof = new BaseProof(owner.asInstanceOf[THMFromProof])
    given proof.type = proof
    val equation = forall(z, F(z) === G(z))
    val comparison = have(equation |- equation) by Hypothesis
    val premise = have(P(F(a)) |- P(F(a))) by Hypothesis
    have((P(F(a)), equation) |- P(G(a))) by RightSubst(using TestLibrary, proof)(comparison, F -> P(F(a)))(premise)
    assert(SCProofChecker.checkSCProof(proof.toSCProof).isValid)

  test("explicit substitution accepts non-first-order argument sorts"):
    val proof = new BaseProof(owner.asInstanceOf[THMFromProof])
    given proof.type = proof
    val f = variable[Prop >>: Ind]
    val g = variable[Prop >>: Ind]
    val hole = variable[Prop >>: Ind]
    val argument = variable[Prop]
    val comparison = have(() |- (f(argument) === g(argument))) by Sorry
    val premise = have(() |- P(f(p))) by Sorry
    val result = have(() |- P(g(p))) by RightSubst.withParameters(using TestLibrary, proof)(
      Seq((f, g, Seq(argument))),
      Seq(hole) -> P(hole(p))
    )(premise, Seq(comparison))
    assert(result.scps.isInstanceOf[SC.RightSubst])
    assert(SCProofChecker.checkSCProof(proof.toSCProof).isValid)

  test("choose comparison arguments fresh in a lifted proof's residual context"):
    val proof = new BaseProof(owner.asInstanceOf[THMFromProof])
    given proof.type = proof
    val equation = forall(z, F(z) === G(z))
    val comparison = have(P(z) |- equation) by Sorry
    val premise = have(P(F(a)) |- P(F(a))) by Hypothesis
    have((P(F(a)), P(z)) |- P(G(a))) by RightSubst(using TestLibrary, proof)(comparison, F -> P(F(a)))(premise)
    assert(SCProofChecker.checkSCProof(proof.toSCProof).isValid)
