package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.Time
import lisa.maths.SetTheory.Types.TypingHelpers.*
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.{BasicTheorems, Function}
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.maths.SetTheory.Types.ADTv2.recursion.helpers.RecFunctionInduction
import lisa.maths.SetTheory.Types.ADTv2.recursion.helpers.{PatternSchemas, extractPatternCaseSchema}
import lisa.maths.SetTheory.Types.ADTv2.support.DefinedProperty

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

  // `defSym.unfold`/`fold` are stated at the canonical bound var; instantiate at `x`/`y`
  // (the `.of` needs a proof context, hence the thin `Lemma` wrappers).
  private val xDefUnfold: THM = Lemma(Def(x) |- spec.untypedDefinition(x)) {
    have(thesis) by Restate.from(defSym.unfold of (defVar := x))
  }
  private val yDefUnfold: THM = Lemma(Def(y) |- spec.untypedDefinition(y)) {
    have(thesis) by Restate.from(defSym.unfold of (defVar := y))
  }
  private val xDefFold: THM = Lemma(spec.untypedDefinition(x) |- Def(x)) {
    have(thesis) by Restate.from(defSym.fold of (defVar := x))
  }
  private val yDefFold: THM = Lemma(spec.untypedDefinition(y) |- Def(y)) {
    have(thesis) by Restate.from(defSym.fold of (defVar := y))
  }

  val recursivePointwisePlan: THM =
    val xDefFormula = definitionFormula(x)
    val yDefFormula = definitionFormula(y)
    Lemma(xDefFormula /\ yDefFormula ==> (x === y)) {
      assume(xDefFormula /\ yDefFormula)

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
      
      val xPatternSchemas = extractPatternSchemas(xDefFormula, x)
      val yPatternSchemas = extractPatternSchemas(yDefFormula, y)

      val pointwiseCoreLemma = Time.measure("Uniqueness/Pointwise uniqueness"){RecFunctionInduction.pointwiseUniquenessAt(
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
        xPatternSchemas = xPatternSchemas,
        yPatternSchemas = yPatternSchemas,
        xDefUnfold = defSym.unfoldAt(x),
        yDefUnfold = defSym.unfoldAt(y)
      )}

      // `pointwiseCoreLemma` is stated over the opaque `Def(x)`, `Def(y)`; discharge them
      // by folding the ambient `untypedDefinition(x)`, `untypedDefinition(y)`.
      val defX = have(Def(x)) by Tautology.from(defSym.foldAt(x))
      val defY = have(Def(y)) by Tautology.from(defSym.foldAt(y))
      val pointwiseByHeight = have(
        ∀(pointInput ∈ argType, (x * pointInput === y * pointInput))
      ) by Tautology.from(pointwiseCoreLemma, defX, defY)

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
