package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.TypingHelpers.*
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.{BasicTheorems, Function}
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.maths.SetTheory.Types.ADTv2.recursion.helpers.RecFunctionInduction
import lisa.maths.SetTheory.Types.ADTv2.recursion.helpers.{PatternSchemas, extractPatternCaseSchema}

private[recursion] final class Uniqueness[N <: Arity](
  spec: FunSpec[N]
) {

  private val adt = spec.adt
  private val argType = spec.argType
  private val returnType = spec.returnType
  private val typ = spec.typ

  private def extractPatternSchemas(
      definition: Expr[Prop],
      functionHead: Expr[Ind]
  ): PatternSchemas[N] =
    spec.patternMatching.patterns.map(pattern =>
      pattern -> extractPatternCaseSchema(definition, functionHead, pattern)
    ).toMap

  private def definitionFormula(v: Variable[Ind]): Expr[Prop] =
    spec.untypedDefinition(v)

  val recursivePointwisePlan: THM =
    Lemma(definitionFormula(x) /\ definitionFormula(y) ==> (x === y)) {
      assume(definitionFormula(x) /\ definitionFormula(y))

      val xOnDomain = have(Function.functionOn(x)(argType)) by Tautology.from(
        BasicTheorems.funcBetweenEqInFuncSpace of (
          f := x,
          A := argType,
          B := returnType
        ),
        BasicTheorems.functionBetweenIsFunctionOn of (
          f := x,
          A := argType,
          B := returnType
        )
      )
      val yOnDomain = have(Function.functionOn(y)(argType)) by Tautology.from(
        BasicTheorems.funcBetweenEqInFuncSpace of (
          f := y,
          A := argType,
          B := returnType
        ),
        BasicTheorems.functionBetweenIsFunctionOn of (
          f := y,
          A := argType,
          B := returnType
        )
      )

      val pointInput = variable[Ind]
      val xDefFormula = definitionFormula(x)
      val yDefFormula = definitionFormula(y)
      val xPatternSchemas = extractPatternSchemas(xDefFormula, x)
      val yPatternSchemas = extractPatternSchemas(yDefFormula, y)

      val pointwiseCoreLemma = RecFunctionInduction.pointwiseUniquenessAt(
        adt = adt,
        patternMatching = spec.patternMatching,
        argType = argType,
        typeSubstitutions = spec.typeSubstitutions,
        inductionVariable = pointInput,
        assumptions = Set(definitionFormula(x), definitionFormula(y)),
        propertyAt = t => x * t === y * t,
        xFun = x,
        yFun = y,
        xDefinitionFormula = xDefFormula,
        yDefinitionFormula = yDefFormula,
        xPatternSchemas = xPatternSchemas,
        yPatternSchemas = yPatternSchemas
      )

      val pointwiseByHeight = have(
        ∀(pointInput ∈ argType, (x * pointInput === y * pointInput))
      ) by Restate.from(pointwiseCoreLemma)

      have(x === y) by Tautology.from(
        BasicTheorems.extensionality of (
          f := x,
          g := y,
          A := argType,
          x := pointInput
        ),
        xOnDomain,
        yOnDomain,
        pointwiseByHeight
      )
      thenHave(thesis) by Restate
    }
}
