package lisa.automation

import lisa.front.fol.FOL.*
import lisa.automation.Proof2.*
import lisa.kernel.proof.SCProofChecker
import lisa.utils.Printer

import org.scalatest.funsuite.AnyFunSuite
import scala.language.adhocExtensions

class ProofTests extends AnyFunSuite {

  val (a, b, c) = (SchematicPredicateLabel[0]("a"), SchematicPredicateLabel[0]("b"), SchematicPredicateLabel[0]("c"))
  val (s, t, u) = (SchematicTermLabel[0]("s"), SchematicTermLabel[0]("t"), SchematicTermLabel[0]("u"))
  val (x, y) = (VariableLabel("x"), VariableLabel("y"))

  private def checkProofs(proofs: Proof*): Unit = {
    val emptyEnvironment: ProofEnvironment = newEmptyEnvironment()
    proofs.foreach { proof =>
      val result = evaluateProof(proof)(emptyEnvironment).map(reconstructSCProof)
      assert(result.nonEmpty)
      val scProof = result.get._1
      val judgement = SCProofChecker.checkSCProof(scProof)
      println(Printer.prettySCProof(judgement))
      println()
      assert(judgement.isValid)
      assert(scProof.imports.isEmpty)
      assert(lisa.kernel.proof.SequentCalculus.isSameSequent(scProof.conclusion, proof.initialState.goals.head))
    }
  }

  test("introduction rules") {
    checkProofs(
      Proof(
        (a, b /\ c) |- (b /\ c, b)
      )(
        RuleHypothesis(RuleParameters().withIndices(0)(1)(0)),
      ),
      Proof(
        (a /\ b) |- a
      )(
        RuleIntroductionLeftAnd(),
        RuleHypothesis(RuleParameters().withIndices(0)(0)(0)),
      ),
      Proof(
        (a, b) |- (a /\ b)
      )(
        RuleIntroductionRightAnd(RuleParameters().withIndices(0)()(0)),
        RuleHypothesis(RuleParameters().withIndices(0)(0)(0)),
        RuleHypothesis(RuleParameters().withIndices(0)(1)(0)),
      ),
      Proof(
        (a \/ b) |- (a, b)
      )(
        RuleIntroductionLeftOr(RuleParameters().withIndices(0)(0)()),
        RuleHypothesis(RuleParameters().withIndices(0)(0)(0)),
        RuleHypothesis(RuleParameters().withIndices(0)(0)(1)),
      ),
      Proof(
        a |- (a \/ b)
      )(
        RuleIntroductionRightOr(RuleParameters().withIndices(0)()(0)),
        RuleHypothesis(RuleParameters().withIndices(0)(0)(0)),
      ),
      Proof(
        (a ==> b, a) |- b
      )(
        RuleIntroductionLeftImplies(RuleParameters().withIndices(0)(0)()),
        RuleHypothesis(RuleParameters().withIndices(0)(0)(1)),
        RuleHypothesis(RuleParameters().withIndices(0)(1)(0)),
      ),
      Proof(
        () |- (a ==> a)
      )(
        RuleIntroductionRightImplies(RuleParameters().withIndices(0)()(0)),
        RuleHypothesis(RuleParameters().withIndices(0)(0)(0)),
      ),
      Proof(
        (a <=> b) |- (b ==> a)
      )(
        RuleIntroductionLeftIff(RuleParameters().withIndices(0)(0)()),
        RuleHypothesis(RuleParameters().withIndices(0)(1)(0)),
      ),
      Proof(
        (a ==> b, b ==> a) |- (a <=> b)
      )(
        RuleIntroductionRightIff(RuleParameters().withIndices(0)()(0)),
        RuleHypothesis(RuleParameters().withIndices(0)(0)(0)),
        RuleHypothesis(RuleParameters().withIndices(0)(1)(0)),
      ),
      Proof(
        (a, !a) |- b
      )(
        RuleIntroductionLeftNot(RuleParameters().withIndices(0)(1)()),
        RuleHypothesis(RuleParameters().withIndices(0)(0)(1)), // FIXME shouldn't it be 0?
      ),
      Proof(
        () |- (!a, a)
      )(
        RuleIntroductionRightNot(RuleParameters().withIndices(0)()(0)),
        RuleHypothesis(RuleParameters().withIndices(0)(0)(0)),
      ),
      Proof(
        () |- (t === t)
      )(
        RuleEliminationLeftRefl(RuleParameters().withFunction(Notations.s, t)),
        RuleHypothesis(),
      ),
      Proof(
        () |- (t === t)
      )(
        RuleIntroductionRightRefl(RuleParameters().withFunction(Notations.s, t)),
      ),
    )
  }

  test("introduction higher order") {
    checkProofs(
      Proof(
        forall(x, u === x) |- (u === s)
      )(
        RuleIntroductionLeftForall(
          RuleParameters()
            .withPredicate(Notations.p, x => u === x)
            .withFunction(Notations.t, s)
        ),
        RuleHypothesis(),
      ),
      Proof(
        a |- forall(x, (u === x) \/ a)
      )(
        RuleIntroductionRightForall(
          RuleParameters()
            .withPredicate(Notations.p, x => (u === x) \/ a)
        ),
        RuleIntroductionRightOr(),
        RuleHypothesis(),
      ),
      Proof(
        exists(x, (s === x) /\ a) |- a
      )(
        RuleIntroductionLeftExists(
          RuleParameters()
            .withPredicate(Notations.p, x => (s === x) /\ a)
        ),
        RuleIntroductionLeftAnd(),
        RuleHypothesis(),
      ),
      Proof(
        (s === t) |- exists(x, s === x)
      )(
        RuleIntroductionRightExists(
          RuleParameters()
            .withPredicate(Notations.p, s === _)
            .withFunction(Notations.t, t)
        ),
        RuleHypothesis(),
      ),
      Proof(
        (s === t, u === t) |- (u === s)
      )(
        RuleIntroductionLeftSubstEq(
          RuleParameters()
            .withPredicate(Notations.p, u === _)
        ),
        RuleHypothesis(),
      ),
      Proof(
        (s === t, u === s) |- (u === t)
      )(
        RuleIntroductionRightSubstEq(
          RuleParameters()
            .withPredicate(Notations.p, u === _)
        ),
        RuleHypothesis(),
      ),
      Proof(
        (a <=> b, c <=> b) |- (c <=> a)
      )(
        RuleIntroductionLeftSubstIff(
          RuleParameters()
            .withConnector(Notations.f, c <=> _)
        ),
        RuleHypothesis(),
      ),
      Proof(
        (a <=> b, c <=> a) |- (c <=> b)
      )(
        RuleIntroductionRightSubstIff(
          RuleParameters()
            .withConnector(Notations.f, c <=> _)
        ),
        RuleHypothesis(),
      ),
    )

    // TODO remaining rules
  }

  test("elimination rules") {
    checkProofs(
      Proof(
        (s === t) |- (t === s)
      )(
        RuleEliminationLeftSubstIff(
          RuleParameters()
            .withConnector(Notations.f, identity)
            .withPredicate(Notations.a, t === s)
            .withPredicate(Notations.b, s === t)
        ),
        RuleHypothesis(),
        TacticalRewrite((s === t) |- (s === t)),
        RuleHypothesis(),
      ),
      Proof(
        (s === t) |- (t === s)
      )(
        RuleEliminationRightSubstIff(
          RuleParameters()
            .withConnector(Notations.f, identity)
            .withPredicate(Notations.a, s === t)
            .withPredicate(Notations.b, t === s)
        ),
        RuleHypothesis(),
        TacticalRewrite((s === t) |- (s === t)),
        RuleHypothesis(),
      ),
      Proof(
        (s === t, t === u) |- (s === u)
      )(
        RuleEliminationLeftSubstEq(
          RuleParameters()
            .withPredicate(Notations.p, _ === u)
            .withFunction(Notations.s, s)
            .withFunction(Notations.t, t)
        ),
        RuleHypothesis(),
        RuleHypothesis(),
      ),
      Proof(
        (s === t, t === u) |- (s === u)
      )(
        RuleEliminationRightSubstEq(
          RuleParameters()
            .withPredicate(Notations.p, _ === u)
            .withFunction(Notations.s, t)
            .withFunction(Notations.t, s)
        ),
        RuleHypothesis(),
        TacticalRewrite((s === t, t === u) |- (s === t)),
        RuleHypothesis(),
      ),
    )
  }

  test("environment") {
    val ctx = newEmptyEnvironment()

    val thm1 = ctx.mkTheorem(
      Proof(
        () |- ((a /\ b) ==> (b /\ a))
      )(
        TacticSolverNative,
      )
    )

    val thm2 = ctx.mkTheorem(
      Proof(
        () |- ((b /\ a) ==> (a /\ b))
      )(
        TacticSolverNative,
      )
    )

    val thm3 = RuleIntroductionRightIff(thm1, thm2).get

    val reconstructed = reconstructSCProofForTheorem(thm3)

    println(Printer.prettySCProof(reconstructed))

    assert(SCProofChecker.checkSCProof(reconstructed).isValid)
  }

}
