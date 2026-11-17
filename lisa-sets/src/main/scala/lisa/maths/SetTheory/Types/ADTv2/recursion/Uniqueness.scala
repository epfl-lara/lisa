package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Functions.BasicTheorems
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.recursion.helpers.PatternSchemas
import lisa.maths.SetTheory.Types.ADTv2.recursion.helpers.RecFunctionInduction
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.A
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.B
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.f
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.g
import lisa.maths.SetTheory.Types.ADTv2.support.semantics.DefinedProperty
import lisa.maths.SetTheory.Types.ADTv2.support.tactics.Cuts
import lisa.maths.SetTheory.Types.TypingHelpers._

private[recursion] final class Uniqueness(
    spec: FunSpec
) {

  private val adt = spec.adt
  private val argType = spec.argType

  /**
   * The fresh candidates compared by the uniqueness theorem.
   */
  val comparisonVariables: (Variable[Ind], Variable[Ind]) = (spec.proofVariable("x"), spec.proofVariable("y"))
  private val (x, y) = comparisonVariables

  private def patternSchemas(functionHead: Expr[Ind]): PatternSchemas =
    spec.cases.map(pattern => pattern -> (pattern.binders, spec.patternConstraint(pattern, functionHead))).toMap

  // Keep the defining predicate opaque in ambient assumptions; unfold it only
  // when deriving a clause equation.
  private val defVar = spec.proofVariable("defVar")
  private val defSym = DefinedProperty(
    s"${spec.functionName}/def",
    spec.typeVariablesSeq,
    defVar,
    spec.definitionAt
  )
  private def Def(v: Expr[Ind]): Expr[Prop] = defSym.term #@ v

  private val pointwiseAgreement: THM =
    val xDefFormula = spec.definitionAt(x)
    val yDefFormula = spec.definitionAt(y)
    val pointInput = spec.proofVariable("pointInput")
    Lemma(
      xDefFormula /\ yDefFormula |- ∀(pointInput, pointInput ∈ argType ==> (x * pointInput === y * pointInput))
    ) {

      val pointwiseCoreLemma = RecFunctionInduction.pointwiseUniquenessAt(
        adt = adt,
        patternMatching = spec.patternMatching,
        argType = argType,
        typeSubstitutions = spec.typeSubstitutions,
        inductionVariable = pointInput,
        assumptions = Set(Def(x), Def(y)),
        propertyAt = t => x * t === y * t,
        xFun = x,
        yFun = y,
        xDefinitionFormula = xDefFormula,
        yDefinitionFormula = yDefFormula,
        xPatternSchemas = patternSchemas(x),
        yPatternSchemas = patternSchemas(y),
        definitionProperty = defSym
      )

      // Fold the two defining formulas to discharge the opaque hypotheses.
      val hyp = assume(xDefFormula /\ yDefFormula)

      val xDefinition = have(xDefFormula) by Weakening(hyp)
      val defX = have(Def(x)) by Cut(xDefinition, defSym.foldAt(x))
      val yDefinition = have(yDefFormula) by Weakening(hyp)
      val defY = have(Def(y)) by Cut(yDefinition, defSym.foldAt(y))

      have(thesis) by Cuts(pointwiseCoreLemma)(defX, defY)
    }

  /**
   * Any two solutions of the defining predicate are equal.
   */
  lazy val pointwiseUniqueness: THM =
    val xDef = spec.definitionAt(x)
    val yDef = spec.definitionAt(y)
    Lemma(xDef /\ yDef ==> (x === y)) {

      have(thesis) by Tautology.from(
        BasicTheorems.functionalExtentionality of (
          f := x,
          g := y,
          A := spec.argType,
          B := spec.returnType
        ),
        BasicTheorems.funcBetweenEqInFuncSpace of (
          f := x,
          A := spec.argType,
          B := spec.returnType
        ),
        BasicTheorems.funcBetweenEqInFuncSpace of (
          f := y,
          A := spec.argType,
          B := spec.returnType
        ),
        pointwiseAgreement
      )
    }
}
