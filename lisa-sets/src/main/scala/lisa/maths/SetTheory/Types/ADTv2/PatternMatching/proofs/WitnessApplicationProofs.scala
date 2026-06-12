package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.proofs

import lisa.maths.SetTheory.Functions.BasicTheorems
import lisa.maths.SetTheory.Functions.Function
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.support.InstantiateForallSeq
import lisa.maths.SetTheory.Types.ADTv2.support.QuantifiersIntro
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.ProofTacticLib.Arity

private[proofs] trait WitnessApplicationProofs[N <: Arity] extends WitnessFunctionProofs[N] {

  val witnessCaseByPattern: Map[Pattern[N], THM] =
    patternMatching.patterns.map(pattern =>
      val vars = pattern.binders
      val body = pattern.body
      pattern -> (Lemma(contextualize(
        forallSeq(
          vars,
          pattern.branchPremiseAt(vars) ==> (witness * pattern.inputTermAt(vars) === body)
        )
      )) {
        val contextHyp =
          if contextPremises.isEmpty then None else Some(assume(contextPremise))
        val wellTypedArgs = pattern.branchPremiseAt(vars)
        val pairTerm = pair(pattern.inputTermAt(vars), body)

        val membershipSchema =
          if contextPremises.isEmpty then
            have(witnessMembership(pattern).statement.right.head) by
              Tautology.from(witnessMembership(pattern))
            lastStep
          else
            witnessMembership(pattern).statement.right.head match
              case _ ==> consequent =>
                have(consequent) by Tautology.from(witnessMembership(pattern), contextHyp.get)
                lastStep
              case _ => throw UnreachableException
        val instantiatedMembership = have(
          wellTypedArgs ==> pairTerm ∈ witness
        ) by InstantiateForallSeq(vars)(membershipSchema)
        val pairInWitness = have(wellTypedArgs |- pairTerm ∈ witness) by
          Tautology.from(instantiatedMembership)

        val witnessBetween =
          if contextPremises.isEmpty then
            have(Function.functionBetween(witness)(argType)(returnType)) by Tautology.from(
              BasicTheorems.funcBetweenEqInFuncSpace of (
                f := witness,
                A := argType,
                B := returnType
              ),
              witnessHasType
            )
          else
            have(witness :: typ) by Tautology.from(witnessHasType, contextHyp.get)
            have(Function.functionBetween(witness)(argType)(returnType)) by Tautology.from(
              BasicTheorems.funcBetweenEqInFuncSpace of (
                f := witness,
                A := argType,
                B := returnType
              ),
              lastStep
            )
        val witnessIsFunction = have(Function.function(witness)) by Tautology.from(
          BasicTheorems.functionBetweenIsFunction of (
            f := witness,
            A := argType,
            B := returnType
          ),
          witnessBetween
        )
        val witnessDomain = have(Function.dom(witness) === argType) by Tautology.from(
          BasicTheorems.functionBetweenDomain of (
            f := witness,
            A := argType,
            B := returnType
          ),
          witnessBetween
        )

        val inputTyping = have(wellTypedArgs |- pattern.inputTermAt(vars) :: argType) by
          Tautology.from(pattern.inputTypingAt(vars, argType))
        val inputInDomain = have(wellTypedArgs |- pattern.inputTermAt(vars) ∈ Function.dom(witness)) by
          Congruence.from(inputTyping, witnessDomain)

        val appEq = have(
          wellTypedArgs |- (witness * pattern.inputTermAt(vars) === body) <=> (pairTerm ∈ witness)
        ) by Tautology.from(
          BasicTheorems.appDefinition of (
            f := witness,
            x := pattern.inputTermAt(vars),
            y := body
          ),
          witnessIsFunction,
          inputInDomain
        )

        have(wellTypedArgs |- (witness * pattern.inputTermAt(vars) === body)) by
          Tautology.from(appEq, pairInWitness)
        thenHave(wellTypedArgs ==> (witness * pattern.inputTermAt(vars) === body)) by RightImplies
        val core = thenHave(
          forallSeq(
            vars,
            pattern.branchPremiseAt(vars) ==> (witness * pattern.inputTermAt(vars) === body)
          )
        ) by QuantifiersIntro(vars)

        if contextPremises.isEmpty then have(thesis) by Restate.from(core)
        else have(thesis) by Tautology.from(contextHyp.get, core)
      })
    ).toMap

  def witnessCase(pattern: Pattern[N]): THM =
    witnessCaseByPattern(pattern)
}
