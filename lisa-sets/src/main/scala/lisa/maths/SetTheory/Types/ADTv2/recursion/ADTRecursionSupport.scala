package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Types.ADTv2.encoding.SemanticADT
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.*
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.Quantifiers
import lisa.utils.prooflib.ProofTacticLib.Arity

private[recursion] final class ADTRecursionSupport[N <: Arity] private (
    val adt: SemanticADT[N]
) {
  private val heightFunVar = Variable[Ind](s"${adt.name}HeightFun")

  def isHeightPred(hh: Expr[Ind]): Expr[Prop] = adt.externalHeight(hh)

  lazy val heightFun: Expr[Ind] = ε(heightFunVar, isHeightPred(heightFunVar))

  lazy val heightFunValid: THM = Lemma(isHeightPred(heightFun)) {
    val epsStep = have(
      ∃(heightFunVar, isHeightPred(heightFunVar)) |- isHeightPred(heightFun)
    ) by Restate.from(
      Quantifiers.existsEpsilon of (
        x := heightFunVar,
        P := λ(heightFunVar, isHeightPred(heightFunVar))
      )
    )
    have(thesis) by Cut(adt.externalHeightExists, epsStep)
  }

  val heightSuccStrong: THM = adt.externalHeightSuccessorStrong
  val heightMonotonic: THM = adt.externalHeightMonotonic
  val termHasHeight: THM = adt.externalTermHasHeight
}

private[recursion] object ADTRecursionSupport {
  private val cache =
    scala.collection.mutable.WeakHashMap.empty[SemanticADT[?], ADTRecursionSupport[?]]

  def apply[N <: Arity](adt: SemanticADT[N]): ADTRecursionSupport[N] =
    cache.getOrElseUpdate(adt, new ADTRecursionSupport[N](adt)).asInstanceOf[ADTRecursionSupport[N]]
}
