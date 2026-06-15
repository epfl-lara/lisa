package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.proofs

import lisa.maths.SetTheory.Base.CartesianProduct
import lisa.maths.SetTheory.Base.Comprehension
import lisa.maths.SetTheory.Base.Symbols.φ
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.support.QuantifiersIntro
import lisa.maths.SetTheory.Types.ADTv2.support.Time
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.ProofTacticLib.Arity

private[proofs] trait WitnessBranchMembership[N <: Arity] extends WitnessProofContext[N] {

  val witnessMembershipByPattern: Map[Pattern[N], THM] =
    patternMatching.patterns
      .map(pattern =>
        Time.measure("witness/MembershipByPattern") {
          val vars = pattern.binders
          val body = pattern.body
          pattern -> (Lemma(
            contextualize(
              forallSeq(
                vars,
                pattern.branchPremiseAt(vars) ==> pair(pattern.inputTermAt(vars), body) ∈ witness
              )
            )
          ) {
            val contextHyp =
              if contextPremises.isEmpty then None else Some(assume(contextPremise))
            val wellTypedArgs = pattern.branchPremiseAt(vars)
            val wellTypedPremises = pattern.typingPremisesAt(vars)
            val pairTerm = pair(pattern.inputTermAt(vars), body)

            def proveAvailablePremise(required: Expr[Prop]) =
              if required == wellTypedArgs then have(wellTypedArgs |- required) by Hypothesis
              else if wellTypedPremises.contains(required) then
                have(wellTypedArgs |- required) by Tautology.from(
                  have(wellTypedArgs |- wellTypedArgs) by Hypothesis
                )
              else
                contextPremises.find(_ == required) match
                  case Some(_) =>
                    contextHyp match
                      case Some(hyp) =>
                        have(wellTypedArgs |- required) by Tautology.from(
                          hyp,
                          have(wellTypedArgs |- wellTypedArgs) by Hypothesis
                        )
                      case None =>
                        throw IllegalArgumentException(
                          s"Premise $required requires a non-empty contextual assumption."
                        )
                  case None =>
                    throw IllegalArgumentException(
                      s"Unsupported typing premise in CaseDefinedWitness: $required"
                    )

            val inputTyping = have(wellTypedArgs |- pattern.inputTermAt(vars) :: argType) by
              Tautology.from(pattern.inputTypingAt(vars, argType))

            val outputTypingPremises =
              checkReturnType(pattern).statement.left.toSeq.map(_.asInstanceOf[Expr[Prop]])
            val outputTypingFacts = outputTypingPremises.map(proveAvailablePremise)
            val outputTyping = have(wellTypedArgs |- body :: returnType) by Tautology.from(
              (checkReturnType(pattern) +: outputTypingFacts)*
            )

            val pairInBound = have(wellTypedArgs |- pairTerm ∈ witnessBound) by Tautology.from(
              CartesianProduct.pairMembership of (
                A := argType,
                B := returnType,
                x := pattern.inputTermAt(vars),
                y := body
              ),
              inputTyping,
              outputTyping
            )

            val baseCaseBody =
              pattern.freshBranchPremise /\ (pairTerm === pair(pattern.freshInputTerm, pattern.bodyAtFreshVars2))
            val ownCaseBranch = simplify(existsSeq(pattern.variables2, baseCaseBody))

            val fullyInstantiatedCaseBody = baseCaseBody
              .substitute(pattern.variables2.zip(vars).map((from, to) => from := to)*)
              .asInstanceOf[Expr[Prop]]

            val ownBranchAtCurrentVars = have(
              wellTypedArgs |- fullyInstantiatedCaseBody
            ) by Tautology.from(
              have(wellTypedArgs |- wellTypedArgs) by Hypothesis,
              have(wellTypedArgs |- pairTerm === pair(pattern.inputTermAt(vars), body)) by RightRefl
            )

            val inOwnCaseBranchRaw =
              pattern.variables2.indices.reverse.foldLeft(ownBranchAtCurrentVars)((fact, idx) =>
                val quantifiedVar = pattern.variables2(idx)
                val witnessVar = vars(idx)
                val priorSubst =
                  pattern.variables2.take(idx).zip(vars.take(idx)).map((from, to) => from := to)
                val phi = existsSeq(
                  pattern.variables2.drop(idx + 1),
                  baseCaseBody.substitute(priorSubst*).asInstanceOf[Expr[Prop]]
                )
                have(wellTypedArgs |- ∃(quantifiedVar, phi)) by
                  RightExists.withParameters(phi, quantifiedVar, witnessVar)(fact)
              )

            val inOwnCaseBranch = have(wellTypedArgs |- ownCaseBranch) by
              Tautology.from(inOwnCaseBranchRaw)
            val rawCaseMembership = have(wellTypedArgs |- caseMembership(pairTerm)) by
              Tautology.from(inOwnCaseBranch)

            have(
              pairTerm ∈ witnessBody <=> (pairTerm ∈ witnessBound /\ caseMembership(pairTerm))
            ) by Tautology.from(
              Comprehension.membership of (
                x := pairTerm,
                y := witnessBound,
                φ := λ(pairWitness, caseMembership(pairWitness))
              )
            )

            val witnessMembershipEq = have(
              wellTypedArgs |- pairTerm ∈ witness <=>
                (pairTerm ∈ witnessBound /\ caseMembership(pairTerm))
            ) by Congruence.from(witnessDef, lastStep)

            val pairInBoundAndCase =
              have(wellTypedArgs |- pairTerm ∈ witnessBound /\ caseMembership(pairTerm)) by
                Tautology.from(pairInBound, rawCaseMembership)

            have(wellTypedArgs |- pairTerm ∈ witness) by
              Tautology.from(witnessMembershipEq, pairInBoundAndCase)
            thenHave(wellTypedArgs ==> (pairTerm ∈ witness)) by
              RightImplies.withParameters(wellTypedArgs, pairTerm ∈ witness)
            val core = thenHave(
              forallSeq(
                vars,
                pattern.branchPremiseAt(vars) ==> pair(pattern.inputTermAt(vars), body) ∈ witness
              )
            ) by QuantifiersIntro(vars)

            if contextPremises.isEmpty then have(thesis) by Restate.from(core)
            else have(thesis) by Tautology.from(contextHyp.get, core)
          })
        }
      )
      .toMap

  def witnessMembership(pattern: Pattern[N]): THM =
    witnessMembershipByPattern(pattern)
}
