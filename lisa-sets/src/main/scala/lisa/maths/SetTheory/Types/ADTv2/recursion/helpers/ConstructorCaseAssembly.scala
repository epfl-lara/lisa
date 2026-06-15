package lisa.maths.SetTheory.Types.ADTv2.recursion.helpers

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.ConstructorSemanticFacts.SpecializedConstructorFacts
import lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.ConstructorSemanticFacts.constructorBranchAtHeight
import lisa.utils.prooflib.BasicStepTactic.Cut
import lisa.utils.prooflib.BasicStepTactic.LeftExists

private[recursion] object ConstructorCaseAssembly {

  def liftConstructorCase[N <: lisa.utils.prooflib.ProofTacticLib.Arity](using
      proof: lisa.SetTheoryLibrary.Proof
  )(
      sc: SpecializedConstructorFacts[N],
      heightSet: Expr[Ind],
      ambientTerm: Expr[Ind],
      branchPremise: Expr[Prop],
      goal: Expr[Prop],
      directBranch: proof.Fact
  ): proof.Fact = {
    val rawBranch = sc.underlying.variables2.reverse.foldLeft(directBranch -> branchPremise) { case ((fact, premise), v) =>
      val wrappedPremise = ∃(v, premise)
      val lifted = have(fact.statement -<? premise +<? wrappedPremise) by
        LeftExists.withParameters(premise, v)(fact)
      (lifted, wrappedPremise)
    }

    have(constructorBranchAtHeight(sc, heightSet, ambientTerm) |- goal) by Tautology.from(rawBranch._1)
  }

  def assemblePointwiseFromConstructors(using
      proof: lisa.SetTheoryLibrary.Proof
  )(
      constructorDisjunction: Expr[Prop],
      decomposeFact: proof.Fact,
      constructorFacts: Seq[proof.Fact],
      antecedent: Expr[Prop],
      goal: Expr[Prop]
  ): proof.Fact = {
    val branchesToGoal =
      if constructorFacts.size == 1 then have(constructorDisjunction |- goal) by Restate.from(constructorFacts.head)
      else have(constructorDisjunction |- goal) by LeftOr(constructorFacts*)

    have(goal) by Cut(decomposeFact, branchesToGoal)
    thenHave(antecedent ==> goal) by RightImplies.withParameters(antecedent, goal)
  }
}
