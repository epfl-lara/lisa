package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.TypingHelpers.*
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.core.InstantiateForallSeq
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.altEqualityTransitivity
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.utils.prooflib.ProofTacticLib.Arity

import ApproxPropShared.substitutedCaseBody

private[recursion] object WitnessCaseExtensionality {

  private def instantiateWitnessAtPattern[N <: Arity](using proof: lisa.SetTheoryLibrary.Proof)(
      spec: FunSpec[N],
      recWitness: Witness[N],
      pattern: Pattern[N],
      selfTerm: Expr[Ind],
      selfTyped: proof.Fact,
      patternPremise: proof.Fact,
      body: Expr[Ind]
  ): proof.Fact = {
    val witnessSchema = recWitness.witnessCase(pattern).of(spec.selfPlaceholder := selfTerm)
    val witnessBase = witnessSchema.statement.right.head match
      case _ ==> consequent =>
        have(consequent) by Tautology.from(witnessSchema, selfTyped)
      case _ => throw UnreachableException

    val witnessAtVars = have(
      pattern.freshBranchPremise ==> (recWitness(selfTerm) * pattern.freshInputTerm === body)
    ) by InstantiateForallSeq(pattern.variables2)(witnessBase)

    val witnessAtPattern = witnessAtVars.statement.right.head match
      case _ ==> consequent =>
        have(consequent) by Tautology.from(witnessAtVars, patternPremise)
      case _ => throw UnreachableException
    witnessAtPattern
  }

  def proveOnSelectedPattern[N <: Arity](using proof: lisa.SetTheoryLibrary.Proof)(
      spec: FunSpec[N],
      recWitness: Witness[N],
      pattern: Pattern[N],
      ambientTerm: Expr[Ind],
      leftSelf: Expr[Ind],
      rightSelf: Expr[Ind],
      leftSelfTyped: proof.Fact,
      rightSelfTyped: proof.Fact,
      patternPremise: proof.Fact,
      ambientEqInput: proof.Fact,
      selfArgEqualities: Seq[proof.Fact]
  ): proof.Fact = {
    val bodyLeft =
      substitutedCaseBody(pattern, spec.selfPlaceholder, leftSelf, pattern.variables2)
    val bodyRight =
      substitutedCaseBody(pattern, spec.selfPlaceholder, rightSelf, pattern.variables2)

    val bodyEq = LambdaBodyEquality.prove(bodyLeft, bodyRight, selfArgEqualities)

    val witnessAtLeft =
      instantiateWitnessAtPattern(spec, recWitness, pattern, leftSelf, leftSelfTyped, patternPremise, bodyLeft)
    val witnessAtRight =
      instantiateWitnessAtPattern(spec, recWitness, pattern, rightSelf, rightSelfTyped, patternPremise, bodyRight)

    val ambientLeftToInput = have(
      app(recWitness(leftSelf))(ambientTerm) === app(recWitness(leftSelf))(pattern.freshInputTerm)
    ) by Congruence.from(ambientEqInput)

    val leftAtAmbient = have(app(recWitness(leftSelf))(ambientTerm) === bodyLeft) by Tautology.from(
      altEqualityTransitivity of (
        x := app(recWitness(leftSelf))(ambientTerm),
        y := app(recWitness(leftSelf))(pattern.freshInputTerm),
        z := bodyLeft
      ),
      ambientLeftToInput,
      witnessAtLeft
    )

    val rightAtInputRev = have(bodyRight === app(recWitness(rightSelf))(pattern.freshInputTerm)) by
      Congruence.from(witnessAtRight)

    have(bodyLeft === app(recWitness(rightSelf))(pattern.freshInputTerm)) by Tautology.from(
      altEqualityTransitivity of (
        x := bodyLeft,
        y := bodyRight,
        z := app(recWitness(rightSelf))(pattern.freshInputTerm)
      ),
      bodyEq,
      rightAtInputRev
    )
    val leftToRightAtInput = have(app(recWitness(leftSelf))(ambientTerm) === app(recWitness(rightSelf))(pattern.freshInputTerm)) by
      Tautology.from(
        altEqualityTransitivity of (
          x := app(recWitness(leftSelf))(ambientTerm),
          y := bodyLeft,
          z := app(recWitness(rightSelf))(pattern.freshInputTerm)
        ),
        leftAtAmbient,
        lastStep
      )

    val inputRightToAmbient = have(
      app(recWitness(rightSelf))(pattern.freshInputTerm) === app(recWitness(rightSelf))(ambientTerm)
    ) by Congruence.from(ambientEqInput)

    have(app(recWitness(leftSelf))(ambientTerm) === app(recWitness(rightSelf))(ambientTerm)) by
      Tautology.from(
        altEqualityTransitivity of (
          x := app(recWitness(leftSelf))(ambientTerm),
          y := app(recWitness(rightSelf))(pattern.freshInputTerm),
          z := app(recWitness(rightSelf))(ambientTerm)
        ),
        leftToRightAtInput,
        inputRightToAmbient
      )
  }
}
