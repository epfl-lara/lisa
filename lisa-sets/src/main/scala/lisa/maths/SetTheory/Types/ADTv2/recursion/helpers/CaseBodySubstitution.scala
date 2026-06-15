package lisa.maths.SetTheory.Types.ADTv2.recursion.helpers

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.recursion.FunSpec
import lisa.utils.prooflib.ProofTacticLib.Arity

private[recursion] object CaseBodySubstitution {

  def substitutedCaseBody[N <: Arity](
      spec: FunSpec[N],
      c: lisa.maths.SetTheory.Types.ADTv2.encoding.SemanticConstructor[N],
      selfTerm: Expr[Ind]
  ): Expr[Ind] = {
    val pattern = spec.patternMatching.patternFor(c)
    pattern.body
      .substitute(spec.selfPlaceholder := selfTerm)
      .substitute(pattern.binders.zip(c.variables2).map((from, to) => from := to)*)
      .asInstanceOf[Expr[Ind]]
  }

  def substitutedCaseBody[N <: Arity](
      pattern: Pattern[N],
      selfPlaceholder: Variable[Ind],
      selfTerm: Expr[Ind],
      vars: Seq[Variable[Ind]]
  ): Expr[Ind] =
    pattern.body
      .substitute(selfPlaceholder := selfTerm)
      .substitute(pattern.binders.zip(vars).map((from, to) => from := to)*)
      .asInstanceOf[Expr[Ind]]
}
