package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Functions.BasicTheorems
import lisa.maths.SetTheory.Functions.Function
import lisa.maths.SetTheory.Functions.Pi.->:
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.FunctionCore.UniquenessProof
import lisa.maths.SetTheory.Types.ADTv2.recursion.helpers.PatternSchemas
import lisa.maths.SetTheory.Types.ADTv2.recursion.helpers.RecFunctionInduction
import lisa.maths.SetTheory.Types.ADTv2.recursion.helpers.extractPatternCaseSchema
import lisa.maths.SetTheory.Types.ADTv2.support.Time
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.PropositionalFacts.equivalenceRevApply
import lisa.maths.SetTheory.Types.ADTv2.support.semantics.DefinedProperty
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.prooflib.ProofTacticLib.Arity

private[recursion] final class Uniqueness[N <: Arity](
    spec: FunSpec[N]
) extends UniquenessProof[N] {

  private val adt = spec.adt
  private val argType = spec.argType
  private val returnType = spec.returnType

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
    // λ(defVar, spec.untypedDefinition(defVar))
    spec.untypedDefinition
  )
  private def Def(v: Expr[Ind]): Expr[Prop] = defSym.term #@ v

  val pointwiseUniqueness: THM =
    val xDefFormula = definitionFormula(x)
    val yDefFormula = definitionFormula(y)
    Lemma(xDefFormula /\ yDefFormula ==> (x === y)) {

      val hyp = assume(xDefFormula /\ yDefFormula)
      val pointInput = variable[Ind]

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

      val t0 = Time.get()

      val xTyped = have(x :: (argType ->: returnType)) by Weakening(hyp)
      val xInFuncSpaceToBetween = have(x ∈ (argType ->: returnType) |- Function.functionBetween(x)(argType)(returnType)) by Cut(
        BasicTheorems.funcBetweenEqInFuncSpace of (
          f := x,
          A := argType,
          B := returnType
        ),
        equivalenceRevApply of (
          p2 := Function.functionBetween(x)(argType)(returnType),
          p1 := x ∈ (argType ->: returnType)
        )
      )
      val xBetween = have(Function.functionBetween(x)(argType)(returnType)) by Cut(xTyped, xInFuncSpaceToBetween)
      val xOnDomain = have(Function.functionOn(x)(argType)) by Cut(
        xBetween,
        BasicTheorems.functionBetweenIsFunctionOn of (
          f := x,
          A := argType,
          B := returnType
        )
      )
      
      val yTyped = have(y :: (argType ->: returnType)) by Weakening(hyp)
      val yInFuncSpaceToBetween = have(y ∈ (argType ->: returnType) |- Function.functionBetween(y)(argType)(returnType)) by Cut(
        BasicTheorems.funcBetweenEqInFuncSpace of (
          f := y,
          A := argType,
          B := returnType
        ),
        equivalenceRevApply of (
          p2 := Function.functionBetween(y)(argType)(returnType),
          p1 := y ∈ (argType ->: returnType)
        )
      )
      val yBetween = have(Function.functionBetween(y)(argType)(returnType)) by Cut(yTyped, yInFuncSpaceToBetween)
      val yOnDomain = have(Function.functionOn(y)(argType)) by Cut(
        yBetween,
        BasicTheorems.functionBetweenIsFunctionOn of (
          f := y,
          A := argType,
          B := returnType
        )
      )

      // `pointwiseCoreLemma` is stated over the opaque `Def(x)`, `Def(y)`; discharge them
      // by folding the ambient `untypedDefinition(x)`, `untypedDefinition(y)`.

      val xDefinition = have(xDefFormula) by Weakening(hyp)
      val defX = have(Def(x)) by Cut(xDefinition, defSym.foldAt(x))
      val yDefinition = have(yDefFormula) by Weakening(hyp)
      val defY = have(Def(y)) by Cut(yDefinition, defSym.foldAt(y))

      val pointwiseWithY = have(
        Def(y) |- ∀(pointInput, pointInput ∈ argType ==> (x * pointInput === y * pointInput))
      ) by Cut(defX, pointwiseCoreLemma)

      val pointwiseByHeight = have(
        ∀(pointInput, pointInput ∈ argType ==> (x * pointInput === y * pointInput))
      ) by Cut(defY, pointwiseWithY)

      val pointwiseByHeightBounded = have(
        ∀(pointInput ∈ argType, (x * pointInput === y * pointInput))
      ) by Restate.from(pointwiseByHeight)

      val ext0 = BasicTheorems.extensionality of (
        f := x,
        g := y,
        A := argType,
        x := pointInput
      )
      val ext0AtPointInput = have(
        (
          Function.functionOn(x)(argType),
          Function.functionOn(y)(argType),
          ∀(pointInput ∈ argType, (x * pointInput === y * pointInput))
        ) |- x === y
      ) by Tautology.from(ext0)

      val ext1 = have(
        (Function.functionOn(y)(argType), ∀(pointInput ∈ argType, (x * pointInput === y * pointInput))) |- x === y
      ) by Cut.withParameters(Function.functionOn(x)(argType))(xOnDomain, ext0AtPointInput)
      val ext2 = have(
        ∀(pointInput ∈ argType, (x * pointInput === y * pointInput)) |- x === y
      ) by Cut.withParameters(Function.functionOn(y)(argType))(yOnDomain, ext1)

      have(x === y) by Cut.withParameters(
        ∀(pointInput ∈ argType, (x * pointInput === y * pointInput))
      )(pointwiseByHeightBounded, ext2)
      thenHave(thesis) by Restate

      val t1 = Time.get()
      Time.register("part", t1 - t0)
    }
}
