package lisa.maths.SetTheory.Types.ADTv2.height

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.pair
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.ConstructorArg

/**
 * Height-local constructor view shared by `HeightConstructors` and `HeightTerms`.
 *
 * It carries only one canonical family of variables together with the corresponding
 * typing signature and constructor term.
 */
final case class HeightConstructorData(
    variables: Seq[Variable[Ind]],
    signature: Seq[(Variable[Ind], ConstructorArg)],
    term: Expr[Ind]
) {
  val arity: Int = variables.length
}

/**
 * Richer height-local constructor view used by `HeightStageSet`.
 *
 * This keeps the concrete encoded constructor pieces needed to build the stage-set
 * universe bound, while staying local to the height development.
 */
final case class HeightStageConstructorData(
    variables: Seq[Variable[Ind]],
    signature: Seq[(Variable[Ind], ConstructorArg)],
    subterm: Expr[Ind],
    tagTerm: Expr[Ind]
) {
  val arity: Int = signature.length
  val term = pair(tagTerm, subterm)
}
