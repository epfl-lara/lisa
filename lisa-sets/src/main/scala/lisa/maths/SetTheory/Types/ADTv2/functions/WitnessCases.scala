package lisa.maths.SetTheory.Types.ADTv2.functions

import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.*
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.QuantifiersIntro
import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.TypingHelpers.*

import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.{BasicTheorems, Function}
import lisa.utils.prooflib.BasicStepTactic.Restate

private[functions] final class WitnessCases[N <: Arity](
    adt: SemanticADT[N],
    cases: Map[SemanticConstructor[N], (Seq[Variable[Ind]], Expr[Ind])],
    returnType: Expr[Ind],
    witness: Expr[Ind],
    witnessHasType: JUSTIFICATION,
    witnessMembershipByConstructor: Map[SemanticConstructor[N], JUSTIFICATION],
    constructorApplicationTyping: (SemanticConstructor[N], Seq[Variable[Ind]]) => THM
) {

  lazy val witnessCaseByConstructor: Map[SemanticConstructor[N], THM] =
    (for c <- cases.keys yield
      val (vars, body) = cases(c)
      c -> Lemma(
        forallSeq(
          vars,
          wellTypedFormula(c.semanticSignature(vars)) ==> (witness * c.appliedTerm(vars) === body)
        )
      ) {
        val wellTypedArgs = wellTypedFormula(c.semanticSignature(vars))
        val pairTerm = pair(c.appliedTerm(vars), body)

        have(forallSeq(vars, wellTypedArgs ==> pairTerm ∈ witness)) by
          Restate.from(witnessMembershipByConstructor(c))
        vars.foldLeft(lastStep)((fact, v) =>
          fact.statement.right.head match
            case forall(_, phi) => thenHave(phi) by InstantiateForall(v)
            case _ => throw UnreachableException
        )
        val pairInWitness = thenHave(wellTypedArgs |- pairTerm ∈ witness) by Restate

        val witnessBetween = have(Function.functionBetween(witness)(adt.term)(returnType)) by Tautology.from(
          BasicTheorems.funcBetweenEqInFuncSpace of (
            f := witness,
            A := adt.term,
            B := returnType
          ),
          witnessHasType
        )
        val witnessIsFunction = have(Function.function(witness)) by Tautology.from(
          BasicTheorems.functionBetweenIsFunction of (
            f := witness,
            A := adt.term,
            B := returnType
          ),
          witnessBetween
        )
        val witnessDomain = have(Function.dom(witness) === adt.term) by Tautology.from(
          BasicTheorems.functionBetweenDomain of (
            f := witness,
            A := adt.term,
            B := returnType
          ),
          witnessBetween
        )

        val inputTyping = have(wellTypedArgs |- c.appliedTerm(vars) :: adt.term) by
          Restate.from(constructorApplicationTyping(c, vars))
        val inputInDomain = have(wellTypedArgs |- c.appliedTerm(vars) ∈ Function.dom(witness)) by
          Congruence.from(inputTyping, witnessDomain)

        val appEq = have(
          wellTypedArgs |- (witness * c.appliedTerm(vars) === body) <=> (pairTerm ∈ witness)
        ) by Tautology.from(
          BasicTheorems.appDefinition of (
            f := witness,
            x := c.appliedTerm(vars),
            y := body
          ),
          witnessIsFunction,
          inputInDomain
        )

        have(wellTypedArgs |- (witness * c.appliedTerm(vars) === body)) by
          Tautology.from(appEq, pairInWitness)
        thenHave(wellTypedArgs ==> (witness * c.appliedTerm(vars) === body)) by RightImplies
        thenHave(thesis) by QuantifiersIntro(vars)
      }
    ).toMap
}
