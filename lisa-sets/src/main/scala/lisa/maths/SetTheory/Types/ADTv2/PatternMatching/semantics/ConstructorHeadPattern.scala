package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.ADTv2.encoding.{SemanticADT, SemanticConstructor}
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 * Constructor-headed patterns expose extra proof data coming from the semantic
 * constructor encoding.
 */
trait ConstructorHeadPattern[N <: Arity] extends Pattern[N] {

  def variables1: Seq[Variable[Ind]] = semanticConstructor.variables1

  def inputTerm1: Expr[Ind] = inputTermAt(variables1)

  def inputTerm2: Expr[Ind] = inputTermAt(variables2)

  def typingFormula1: Expr[Prop] = typingFormulaAt(variables1)

  def typingFormula2: Expr[Prop] = typingFormulaAt(variables2)

  def branchPremise1: Expr[Prop] = branchPremiseAt(variables1)

  def structuralTerm1: Expr[Ind] = semanticConstructor.structuralTerm1

  def structuralTerm2: Expr[Ind] = semanticConstructor.structuralTerm2

  def tagTerm1: Expr[Ind] = semanticConstructor.underlying.tagTerm

  def tagTerm2: Expr[Ind] = semanticConstructor.underlying.tagTerm

  def subterm1: Expr[Ind] = semanticConstructor.underlying.subterm1

  def subterm2: Expr[Ind] = semanticConstructor.underlying.subterm2

  def injectivity: THM = semanticConstructor.injectivity

  def shortDefinition: THM = semanticConstructor.shortDefinition
}