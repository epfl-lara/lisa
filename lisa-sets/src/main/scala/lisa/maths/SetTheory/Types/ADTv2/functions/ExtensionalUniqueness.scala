package lisa.maths.SetTheory.Types.ADTv2.functions

import lisa.maths.SetTheory.Functions.BasicTheorems
import lisa.maths.SetTheory.Functions.Function
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.support.InstantiateForallSeq
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.ProofTacticLib.Arity

private[functions] final class ExtensionalUniqueness[N <: Arity](
    argType: Expr[Ind],
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

      val xBetween = have(Function.functionBetween(x)(argType)(returnType)) by Tautology.from(
        BasicTheorems.funcBetweenEqInFuncSpace of (
          f := x,
          A := argType,
          B := returnType
        ),
        xTyped
      )
      val yBetween = have(Function.functionBetween(y)(argType)(returnType)) by Tautology.from(
        BasicTheorems.funcBetweenEqInFuncSpace of (
          f := y,
          A := argType,
          B := returnType
        ),
        yTyped
      )

      val xOnDomain = have(Function.functionOn(x)(argType)) by Tautology.from(
        BasicTheorems.functionBetweenIsFunctionOn of (
          f := x,
          A := argType,
          B := returnType
        ),
        xBetween
      )
      val yOnDomain = have(Function.functionOn(y)(argType)) by Tautology.from(
        BasicTheorems.functionBetweenIsFunctionOn of (
          f := y,
          A := argType,
          B := returnType
        ),
        yBetween
      )

      val pointInput = variable[Ind]
      val constructorDisjunction = simplify(patternMatching.caseCoverage(pointInput))

      val decompositionAtInput = have(pointInput ∈ argType |- constructorDisjunction) subproof {
        have(pointInput ∈ argType ==> constructorDisjunction) by
          InstantiateForall(pointInput)(patternMatching.coverage)
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

      have(pointInput ∈ argType |- (x * pointInput === y * pointInput)) by
        Cut(decompositionAtInput, equalityFromCases)
      thenHave(pointInput ∈ argType ==> (x * pointInput === y * pointInput)) by RightImplies
      val pointwiseOnDomain = thenHave(
        ∀(pointInput, pointInput ∈ argType ==> (x * pointInput === y * pointInput))
      ) by RightForall

      have(x === y) by Tautology.from(
        BasicTheorems.extensionality of (
          f := x,
          g := y,
          A := argType,
          x := pointInput
        ),
        xOnDomain,
        yOnDomain,
        pointwiseOnDomain
      )
      thenHave(thesis) by Tautology
    }

}
