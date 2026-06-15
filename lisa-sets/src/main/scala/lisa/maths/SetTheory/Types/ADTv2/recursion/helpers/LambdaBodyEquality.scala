package lisa.maths.SetTheory.Types.ADTv2.recursion.helpers

import lisa.maths.SetTheory.Functions.BasicTheorems
import lisa.maths.SetTheory.Functions.Function.Sabs
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.utils.prooflib.BasicStepTactic.Cut
import lisa.utils.prooflib.BasicStepTactic.RightForall
import lisa.utils.prooflib.BasicStepTactic.RightImplies
import lisa.utils.prooflib.BasicStepTactic.Weakening

private[recursion] object LambdaBodyEquality {

  private val A = variable[Ind]
  private val Gf, Hf = variable[Ind >>: Ind]

  
  def proveUnder(using proof: lisa.SetTheoryLibrary.Proof)(
      assumptions: Set[Expr[Prop]],
      leftBody: Expr[Ind],
      rightBody: Expr[Ind],
      equalityFacts: Seq[proof.Fact]
  ): proof.Fact =
    if leftBody == rightBody then
      val refl = have(leftBody === rightBody) by RightRefl
      have(assumptions |- leftBody === rightBody) by Weakening(refl)
    else if equalityFacts.nonEmpty then
      (leftBody, rightBody) match
        case (
              Sabs(domain1, Abs(boundVar1: Variable[Ind], innerBody1: Expr[Ind])),
              Sabs(domain2, Abs(boundVar2: Variable[Ind], innerBody2: Expr[Ind]))
            ) if domain1 == domain2 && boundVar1 == boundVar2 =>
          val innerBodyEq = have(assumptions |- innerBody1 === innerBody2) by
            Congruence.from(equalityFacts*)
          val pointwiseEq = have(
            assumptions |- forall(boundVar1, (boundVar1 ∈ domain1) ==> (innerBody1 === innerBody2))
          ) subproof {
            // Add the `boundVar ∈ domain` antecedent with Weakening + RightImplies instead
            // of Tautology: `assumptions` carries the deep ~1.5k-char branchSelectionBody,
            // and Tautology would decompose it (≈13s). Weakening/RightImplies leave it atomic.
            have((assumptions + (boundVar1 ∈ domain1)) |- (innerBody1 === innerBody2)) by Weakening(innerBodyEq)
            thenHave(assumptions |- (boundVar1 ∈ domain1) ==> (innerBody1 === innerBody2)) by RightImplies
            thenHave(thesis) by RightForall
          }
          have(assumptions |- leftBody === rightBody) by Cut(
            pointwiseEq,
            BasicTheorems.absBodyEq of (
              A := domain1,
              Gf := λ(boundVar1, innerBody1),
              Hf := λ(boundVar1, innerBody2)
            )
          )
        case _ =>
          have(assumptions |- leftBody === rightBody) by Congruence.from(equalityFacts*)
    else
      throw IllegalArgumentException(
        s"Cannot prove body equality without recursive equalities: $leftBody vs $rightBody."
      )

  def prove(using proof: lisa.SetTheoryLibrary.Proof)(
      leftBody: Expr[Ind],
      rightBody: Expr[Ind],
      equalityFacts: Seq[proof.Fact]
  ): proof.Fact =
    proveUnder(Set.empty, leftBody, rightBody, equalityFacts)
}
