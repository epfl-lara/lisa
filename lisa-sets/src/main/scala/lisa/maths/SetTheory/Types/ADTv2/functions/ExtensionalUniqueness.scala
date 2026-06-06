package lisa.maths.SetTheory.Types.ADTv2.functions

import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.FunctionAbstractions
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.InstantiateForallSeq
import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.TypingHelpers.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.{BasicTheorems, Function}
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.BasicStepTactic.Restate

private[functions] final class ExtensionalUniqueness[N <: Arity](
    adt: SemanticADT[N],
    patternMatching: PatternSystem[N],
    returnType: Expr[Ind],
    typ: Expr[Ind],
    untypedDefinition: Expr[Prop]
) {

  private def definitionFormula(v: Variable[Ind]): Expr[Prop] =
    untypedDefinition.substitute(f := v)

  lazy val nonRecursivePointwise: THM =
    Lemma(definitionFormula(x) /\ definitionFormula(y) ==> (x === y)) {
      assume(definitionFormula(x) /\ definitionFormula(y))
      val xDefinition = have(definitionFormula(x)) by Tautology
      val yDefinition = have(definitionFormula(y)) by Tautology

      val xTyped = have(x :: typ) by Tautology.from(xDefinition)
      val yTyped = have(y :: typ) by Tautology.from(yDefinition)

      val xBetween = have(Function.functionBetween(x)(adt.term)(returnType)) by Tautology.from(
        BasicTheorems.funcBetweenEqInFuncSpace of (
          f := x,
          A := adt.term,
          B := returnType
        ),
        xTyped
      )
      val yBetween = have(Function.functionBetween(y)(adt.term)(returnType)) by Tautology.from(
        BasicTheorems.funcBetweenEqInFuncSpace of (
          f := y,
          A := adt.term,
          B := returnType
        ),
        yTyped
      )

      val xOnDomain = have(Function.functionOn(x)(adt.term)) by Tautology.from(
        BasicTheorems.functionBetweenIsFunctionOn of (
          f := x,
          A := adt.term,
          B := returnType
        ),
        xBetween
      )
      val yOnDomain = have(Function.functionOn(y)(adt.term)) by Tautology.from(
        BasicTheorems.functionBetweenIsFunctionOn of (
          f := y,
          A := adt.term,
          B := returnType
        ),
        yBetween
      )

      val pointInput = variable[Ind]
      val constructorDisjunction = simplify(patternMatching.caseCoverage(pointInput))

      val decompositionAtInput = have(pointInput ∈ adt.term |- constructorDisjunction) subproof {
        have(pointInput ∈ adt.term ==> constructorDisjunction) by
          InstantiateForall(pointInput)(patternMatching.coverage(adt))
        thenHave(thesis) by Restate
      }

      // Pattern-based (handles split constructors: several patterns per constructor).
      val branchEqualities = patternMatching.patterns.map(pattern =>
        val caseVars = pattern.binders
        val caseBody = pattern.body
        val branchCase =
          existsSeq(pattern.variables2, pattern.freshBranchPremise /\ (pointInput === pattern.freshInputTerm))

        val directBranch = have(
          pattern.freshBranchPremise /\ (pointInput === pattern.freshInputTerm) |- (x * pointInput === y * pointInput)
        ) subproof {
          assume(pattern.freshBranchPremise /\ (pointInput === pattern.freshInputTerm))
          val premise = have(pattern.freshBranchPremise) by Tautology
          val pointEq = have(pointInput === pattern.freshInputTerm) by Tautology

          val xCaseSchema = have(
            forallSeq(caseVars, pattern.branchPremise ==> (x * pattern.inputTerm === caseBody))
          ) by Tautology.from(xDefinition)
          val yCaseSchema = have(
            forallSeq(caseVars, pattern.branchPremise ==> (y * pattern.inputTerm === caseBody))
          ) by Tautology.from(yDefinition)

          val xAt = have(
            pattern.freshBranchPremise ==> (x * pattern.freshInputTerm === pattern.bodyAtFreshVars2)
          ) by InstantiateForallSeq(pattern.variables2)(xCaseSchema)
          val xBody = have(x * pattern.freshInputTerm === pattern.bodyAtFreshVars2) by Tautology.from(xAt, premise)

          val yAt = have(
            pattern.freshBranchPremise ==> (y * pattern.freshInputTerm === pattern.bodyAtFreshVars2)
          ) by InstantiateForallSeq(pattern.variables2)(yCaseSchema)
          val yBody = have(y * pattern.freshInputTerm === pattern.bodyAtFreshVars2) by Tautology.from(yAt, premise)

          val xAtPoint = have(x * pointInput === pattern.bodyAtFreshVars2) by Congruence.from(pointEq, xBody)
          val yAtPoint = have(y * pointInput === pattern.bodyAtFreshVars2) by Congruence.from(pointEq, yBody)
          have(x * pointInput === y * pointInput) by Congruence.from(xAtPoint, yAtPoint)
        }

        val rawBranch = pattern.variables2.reverse.foldLeft(directBranch)((fact, v) =>
          thenHave(∃(v, fact.statement.left.head) |- (x * pointInput === y * pointInput)) by LeftExists
        )

        have(branchCase |- (x * pointInput === y * pointInput)) by Tautology.from(rawBranch)
      )

      val equalityFromCases =
        if branchEqualities.size == 1 then
          have(constructorDisjunction |- (x * pointInput === y * pointInput)) by
            Restate.from(branchEqualities.head)
        else
          have(constructorDisjunction |- (x * pointInput === y * pointInput)) by
            LeftOr(branchEqualities*)

      have(pointInput ∈ adt.term |- (x * pointInput === y * pointInput)) by
        Cut(decompositionAtInput, equalityFromCases)
      thenHave(pointInput ∈ adt.term ==> (x * pointInput === y * pointInput)) by RightImplies
      val pointwiseOnDomain = thenHave(
        ∀(pointInput, pointInput ∈ adt.term ==> (x * pointInput === y * pointInput))
      ) by RightForall

      have(x === y) by Tautology.from(
        BasicTheorems.extensionality of (
          f := x,
          g := y,
          A := adt.term,
          x := pointInput
        ),
        xOnDomain,
        yOnDomain,
        pointwiseOnDomain
      )
      thenHave(thesis) by Tautology
    }

}
