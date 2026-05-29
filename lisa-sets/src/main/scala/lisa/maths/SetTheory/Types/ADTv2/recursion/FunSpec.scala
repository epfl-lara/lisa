package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.{Pattern, PatternSystem}
import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.Pi.->:
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.maths.SetTheory.Types.TypingHelpers.*

class FunSpec[N <: Arity](
    val functionName: String,
    val adt: SemanticADT[N],
    val selfPlaceholder: Variable[Ind],
    val patternMatching: PatternSystem[N],
    val returnType: Expr[Ind]
) {
  val cases: Seq[Pattern[N]] = patternMatching.patterns
  val typeVariablesSeq: Seq[Variable[Ind]] = adt.typeVariablesSeq
  val typeArity: N = adt.typeArity
  val argType: Expr[Ind] = adt.term
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
