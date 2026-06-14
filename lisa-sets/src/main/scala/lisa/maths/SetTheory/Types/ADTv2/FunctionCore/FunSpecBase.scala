package lisa.maths.SetTheory.Types.ADTv2.FunctionCore

import lisa.maths.SetTheory.Functions.Pi.->:
import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.encoding._
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.prooflib.ProofTacticLib.Arity

private[ADTv2] abstract class FunSpecBase[N <: Arity](
    val functionName: String,
    val adt: SemanticADT[N],
    val argType: Expr[Ind],
    val patternMatching: PatternSystem[N],
    val returnType: Expr[Ind]
) {
  val cases: Seq[Pattern[N]] = patternMatching.patterns
  val typeVariablesSeq: Seq[Variable[Ind]] = adt.typeVariablesSeq
  val typ: Expr[Ind] = argType ->: returnType
  val typeArity: N = adt.typeArity

  protected def bodyFor(pattern: Pattern[N], fVar: Expr[Ind]): Expr[Ind]

  def untypedDefinition(fVar: Expr[Ind]): Expr[Prop] =
    (fVar :: typ) /\ simplify(seqAnd(cases.map(pattern =>
      forallSeq(
        pattern.binders,
        pattern.branchPremise ==> (fVar * pattern.inputTerm === bodyFor(pattern, fVar))
      )
    )))
}
