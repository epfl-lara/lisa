package lisa.maths.SetTheory.Types.ADTv2.FunctionCore

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern

/**
 * The case-specific parts that [[FunctionSemanticsBase]] needs in order to
 * assemble the shared semantic layer: the spec, the existence and uniqueness
 * proofs, and how to build the (possibly self-referential) pattern bodies once
 * the defined term is known.
 */
trait SemanticFunctionInputs {
  def name: String
  def spec: FunSpecBase
  def existence: ExistenceProof
  def uniqueness: UniquenessProof
  def buildPatterns(term: Expr[Ind]): Seq[Pattern]
}
