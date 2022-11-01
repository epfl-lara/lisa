package lisa.automation

import lisa.automation.Proof2.*
import lisa.front.fol.FOL.*
import lisa.kernel.proof.SCProofChecker
import lisa.utils.FOLPrinter
import org.scalatest.Ignore
import org.scalatest.funsuite.AnyFunSuite

import scala.language.adhocExtensions

// Not working while the front's unifier is not repaired.
@Ignore
class ProofTests extends AnyFunSuite {

  val (a, b, c) = (SchematicPredicateLabel[0]("a"), SchematicPredicateLabel[0]("b"), SchematicPredicateLabel[0]("c"))
  val (s, t, u) = (SchematicTermLabel[0]("s"), SchematicTermLabel[0]("t"), SchematicTermLabel[0]("u"))
  val (x, y) = (VariableLabel("x"), VariableLabel("y"))

  private def checkProof(proof: Proof): Unit = {
    val emptyEnvironment: ProofEnvironment = newEmptyEnvironment()
    val result = evaluateProof(proof)(emptyEnvironment).map(reconstructSCProof)
    assert(result.nonEmpty, s"kernel proof was empty for $proof")
    val scProof = result.get._1
    val judgement = SCProofChecker.checkSCProof(scProof)
    assert(judgement.isValid, FOLPrinter.prettySCProof(judgement))
    assert(scProof.imports.isEmpty, s"proof unexpectedly uses imports: ${FOLPrinter.prettySCProof(judgement)}")
    assert(
      lisa.kernel.proof.SequentCalculus.isSameSequent(scProof.conclusion, proof.initialState.goals.head),
      s"proof does not prove ${FOLPrinter.prettySequent(proof.initialState.goals.head)}:\nPrinter.prettySCProof(judgement)"
    )
  }

  test("hypothesis") {
    checkProof(
      Proof(
        (a, b /\ c) |- (b /\ c, b)
      )(
        RuleHypothesis(RuleParameters().withIndices(0)(1)(0))
      )
    )

  }

  test("left and") {
    checkProof(
      Proof(
        (a /\ b) |- a
      )(
        RuleIntroductionLeftAnd(),
        RuleHypothesis(RuleParameters().withIndices(0)(0)(0))
      )
    )
  }

  test("right and") {
    checkProof(
      Proof(
        (a, b) |- (a /\ b)
      )(
        RuleIntroductionRightAnd(RuleParameters().withIndices(0)()(0)),
        RuleHypothesis(RuleParameters().withIndices(0)(0)(0)),
        RuleHypothesis(RuleParameters().withIndices(0)(1)(0))
      )
    )
  }

  test("left or") {
    checkProof(
      Proof(
        (a \/ b) |- (a, b)
      )(
        RuleIntroductionLeftOr(RuleParameters().withIndices(0)(0)()),
        RuleHypothesis(RuleParameters().withIndices(0)(0)(0)),
        RuleHypothesis(RuleParameters().withIndices(0)(0)(1))
      )
    )
  }

  test("right or") {
    checkProof(
      Proof(
        a |- (a \/ b)
      )(
        RuleIntroductionRightOr(RuleParameters().withIndices(0)()(0)),
        RuleHypothesis(RuleParameters().withIndices(0)(0)(0))
      )
    )
  }

  test("left implies") {
    checkProof(
      Proof(
        (a ==> b, a) |- b
      )(
        RuleIntroductionLeftImplies(RuleParameters().withIndices(0)(0)()),
        RuleHypothesis(RuleParameters().withIndices(0)(0)(1)),
        RuleHypothesis(RuleParameters().withIndices(0)(1)(0))
      )
    )
  }

  test("right implies") {
    checkProof(
      Proof(
        () |- (a ==> a)
      )(
        RuleIntroductionRightImplies(RuleParameters().withIndices(0)()(0)),
        RuleHypothesis(RuleParameters().withIndices(0)(0)(0))
      )
    )
  }

  test("left iff") {
    checkProof(
      Proof(
        (a <=> b) |- (b ==> a)
      )(
        RuleIntroductionLeftIff(RuleParameters().withIndices(0)(0)()),
        RuleHypothesis(RuleParameters().withIndices(0)(1)(0))
      )
    )
  }

  test("right iff") {
    checkProof(
      Proof(
        (a ==> b, b ==> a) |- (a <=> b)
      )(
        RuleIntroductionRightIff(RuleParameters().withIndices(0)()(0)),
        RuleHypothesis(RuleParameters().withIndices(0)(0)(0)),
        RuleHypothesis(RuleParameters().withIndices(0)(1)(0))
      )
    )
  }

  test("left not") {
    checkProof(
      Proof(
        (a, !a) |- b
      )(
        RuleIntroductionLeftNot(RuleParameters().withIndices(0)(1)()),
        RuleHypothesis(RuleParameters().withIndices(0)(0)(1)) // FIXME shouldn't it be 0?
      )
    )
  }

  test("right not") {
    checkProof(
      Proof(
        () |- (!a, a)
      )(
        RuleIntroductionRightNot(RuleParameters().withIndices(0)()(0)),
        RuleHypothesis(RuleParameters().withIndices(0)(0)(0))
      )
    )
  }

  test("left =") {
    checkProof(
      Proof(
        () |- (t === t)
      )(
        RuleEliminationLeftRefl(RuleParameters().withFunction(Notations.s, t)),
        RuleHypothesis()
      )
    )
  }

  test("right =") {
    checkProof(
      Proof(
        () |- (t === t)
      )(
        RuleIntroductionRightRefl(RuleParameters().withFunction(Notations.s, t))
      )
    )
  }

  test("introduction higher order") {
    checkProof(
      Proof(
        forall(x, u === x) |- (u === s)
      )(
        RuleIntroductionLeftForall(
          RuleParameters()
            .withPredicate(Notations.p, x => u === x)
            .withFunction(Notations.t, s)
        ),
        RuleHypothesis()
      )
    )
  }

  test("right forall right or") {
    checkProof(
      Proof(
        a |- forall(x, (u === x) \/ a)
      )(
        RuleIntroductionRightForall(
          RuleParameters()
            .withPredicate(Notations.p, x => (u === x) \/ a)
        ),
        RuleIntroductionRightOr(),
        RuleHypothesis()
      )
    )
  }

  test("left exists left and") {
    checkProof(
      Proof(
        exists(x, (s === x) /\ a) |- a
      )(
        RuleIntroductionLeftExists(
          RuleParameters()
            .withPredicate(Notations.p, x => (s === x) /\ a)
        ),
        RuleIntroductionLeftAnd(),
        RuleHypothesis()
      )
    )
  }

  test("right exists") {
    checkProof(
      Proof(
        (s === t) |- exists(x, s === x)
      )(
        RuleIntroductionRightExists(
          RuleParameters()
            .withPredicate(Notations.p, s === _)
            .withFunction(Notations.t, t)
        ),
        RuleHypothesis()
      )
    )
  }

  test("left subst =") {
    checkProof(
      Proof(
        (s === t, u === t) |- (u === s)
      )(
        RuleIntroductionLeftSubstEq(
          RuleParameters()
            .withPredicate(Notations.p, u === _)
        ),
        RuleHypothesis()
      )
    )
  }

  test("right subst =") {
    checkProof(
      Proof(
        (s === t, u === s) |- (u === t)
      )(
        RuleIntroductionRightSubstEq(
          RuleParameters()
            .withPredicate(Notations.p, u === _)
        ),
        RuleHypothesis()
      )
    )
  }

  test("left subst iff") {
    checkProof(
      Proof(
        (a <=> b, c <=> b) |- (c <=> a)
      )(
        RuleIntroductionLeftSubstIff(
          RuleParameters()
            .withConnector(Notations.f, c <=> _)
        ),
        RuleHypothesis()
      )
    )
  }

  test("right subst iff") {
    checkProof(
      Proof(
        (a <=> b, c <=> a) |- (c <=> b)
      )(
        RuleIntroductionRightSubstIff(
          RuleParameters()
            .withConnector(Notations.f, c <=> _)
        ),
        RuleHypothesis()
      )
    )
  }

  test("elimination left subst iff") {
    checkProof(
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
        RuleHypothesis()
      )
    )
  }

  test("elimination right subst iff") {
    checkProof(
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
        RuleHypothesis()
      )
    )
  }

  test("elimination left subst =") {
    checkProof(
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
        RuleHypothesis()
      )
    )
  }

  test("elimination right subst =") {
    checkProof(
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
        RuleHypothesis()
      )
    )
  }

}
