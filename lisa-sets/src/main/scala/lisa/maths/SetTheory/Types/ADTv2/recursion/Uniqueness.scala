package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.FunctionCore.UniquenessProof
import lisa.maths.SetTheory.Types.ADTv2.recursion.helpers.PatternSchemas
import lisa.maths.SetTheory.Types.ADTv2.recursion.helpers.RecFunctionInduction
import lisa.maths.SetTheory.Types.ADTv2.recursion.helpers.extractPatternCaseSchema
import lisa.maths.SetTheory.Types.ADTv2.support.Time
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.semantics.DefinedProperty
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.prooflib.ProofTacticLib.Arity

private[recursion] final class Uniqueness[N <: Arity](
    override protected val spec: FunSpec[N]
) extends UniquenessProof[N] {

  private val adt = spec.adt
  private val argType = spec.argType

  private def extractPatternSchemas(
      definition: Expr[Prop],
      functionHead: Expr[Ind]
  ): PatternSchemas[N] =
    spec.patternMatching.patterns.map(pattern => pattern -> extractPatternCaseSchema(definition, functionHead, pattern)).toMap

  private def definitionFormula(v: Variable[Ind]): Expr[Prop] =
    spec.untypedDefinition(v)

  // Opaque view of the (~1.5k-char) function-definition formula. Used as the ambient
  // assumption inside `pointwiseUniquenessAt`, so every sequent there carries a small
  // atom instead of the full `untypedDefinition`; we unfold only where the per-case
  // schema is extracted (`instantiateCaseFromDefinition`). `definition` shape from `DEF`
  // is `Def(v) <=> untypedDefinition(v)`.
  private val defVar = variable[Ind]
  private val defSym = DefinedProperty(
    s"${spec.functionName}/def",
    spec.typeVariablesSeq,
    defVar,
    spec.untypedDefinition
  )
  private def Def(v: Expr[Ind]): Expr[Prop] = defSym.term #@ v


  protected val pointwiseAgreement: THM =
    val xDefFormula = definitionFormula(x)
    val yDefFormula = definitionFormula(y)
    val pointInput = variable[Ind]
    Lemma(
      xDefFormula /\ yDefFormula |- ∀(pointInput, pointInput ∈ argType ==> (x * pointInput === y * pointInput))
    ) {

      val pointwiseCoreLemma = Time.measure("Pointwise uniqueness") {
        RecFunctionInduction.pointwiseUniquenessAt(
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
          xPatternSchemas = extractPatternSchemas(xDefFormula, x),
          yPatternSchemas = extractPatternSchemas(yDefFormula, y),
          xDefUnfold = defSym.unfoldAt(x),
          yDefUnfold = defSym.unfoldAt(y)
        )
      }

      // `pointwiseCoreLemma` is stated over the opaque `Def(x)`, `Def(y)`; discharge them
      // by folding the ambient `untypedDefinition(x)`, `untypedDefinition(y)`.
      val hyp = assume(xDefFormula /\ yDefFormula)

      val xDefinition = have(xDefFormula) by Weakening(hyp)
      val defX = have(Def(x)) by Cut(xDefinition, defSym.foldAt(x))
      val yDefinition = have(yDefFormula) by Weakening(hyp)
      val defY = have(Def(y)) by Cut(yDefinition, defSym.foldAt(y))

      val pointwiseWithY = have(
        Def(y) |- ∀(pointInput, pointInput ∈ argType ==> (x * pointInput === y * pointInput))
      ) by Cut(defX, pointwiseCoreLemma)

      have(
        ∀(pointInput, pointInput ∈ argType ==> (x * pointInput === y * pointInput))
      ) by Cut(defY, pointwiseWithY)
      thenHave(thesis) by Restate
    }
}
