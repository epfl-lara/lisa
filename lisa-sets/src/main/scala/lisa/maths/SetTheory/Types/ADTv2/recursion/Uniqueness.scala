package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.TypingHelpers.*
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.{BasicTheorems, Function}
import lisa.utils.prooflib.ProofTacticLib.Arity

private[recursion] final class Uniqueness[N <: Arity](
  spec: FunSpec[N]
) {

  private val adt = spec.adt
  private val returnType = spec.returnType
  private val typ = spec.typ

  private def extractConstructorSchemas(
      definition: Expr[Prop],
      functionHead: Expr[Ind]
  ): ConstructorSchemas[N] =
    adt.constructors.map(c => c -> extractConstructorCaseSchema(definition, functionHead, c)).toMap

  private def definitionFormula(v: Variable[Ind]): Expr[Prop] =
    spec.untypedDefinition(v)

  val recursivePointwisePlan: THM =
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
      val xDefFormula = definitionFormula(x)
      val yDefFormula = definitionFormula(y)
      val xConstructorSchemas = extractConstructorSchemas(xDefFormula, x)
      val yConstructorSchemas = extractConstructorSchemas(yDefFormula, y)

      val pointwiseCoreLemma = RecFunctionInduction.pointwiseUniquenessAt(
        adt = adt,
        inductionVariable = pointInput,
        assumptions = Set(definitionFormula(x), definitionFormula(y)),
        propertyAt = t => x * t === y * t,
        xFun = x,
        yFun = y,
        xDefinitionFormula = xDefFormula,
        yDefinitionFormula = yDefFormula,
        xConstructorSchemas = xConstructorSchemas,
        yConstructorSchemas = yConstructorSchemas
      )

      val pointwiseByHeight = have(
        ∀(pointInput ∈ adt.term, (x * pointInput === y * pointInput))
      ) by Tautology.from(pointwiseCoreLemma, xDefinition, yDefinition)

      have(x === y) by Tautology.from(
        BasicTheorems.extensionality of (
          f := x,
          g := y,
          A := adt.term,
          x := pointInput
        ),
        xOnDomain,
        yOnDomain,
        pointwiseByHeight
      )
      thenHave(thesis) by Tautology
    }
}
