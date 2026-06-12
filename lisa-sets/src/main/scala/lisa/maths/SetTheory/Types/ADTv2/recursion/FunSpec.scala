package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Functions.Pi.->:
import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.encoding._
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.TypeSubstitution
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.prooflib.ProofTacticLib.Arity

class FunSpec[N <: Arity](
    val functionName: String,
    val adt: SemanticADT[N],
    val argType: Expr[Ind],
    val typeSubstitutions: Seq[TypeSubstitution],
    val selfPlaceholder: Variable[Ind],
    val patternMatching: PatternSystem[N],
    val returnType: Expr[Ind]
) {
  val cases: Seq[Pattern[N]] = patternMatching.patterns
  val typeVariablesSeq: Seq[Variable[Ind]] = adt.typeVariablesSeq
  val typeArity: N = adt.typeArity
  val typ: Expr[Ind] = argType ->: returnType

  def untypedDefinition(fVar: Expr[Ind]): Expr[Prop] =
    (fVar :: typ) /\ simplify(seqAnd(cases.map(pattern =>
      val bodyWithSelf = pattern.body.substitute(selfPlaceholder := fVar)
      forallSeq(
        pattern.binders,
        pattern.branchPremise ==> (fVar * pattern.inputTerm === bodyWithSelf)
      )
    )))
}
