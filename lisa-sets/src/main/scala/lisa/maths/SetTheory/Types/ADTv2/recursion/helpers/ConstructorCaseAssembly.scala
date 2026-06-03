package lisa.maths.SetTheory.Types.ADTv2.recursion.helpers

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.BasicStepTactic.{Cut, LeftExists}

import lisa.maths.SetTheory.Types.ADTv2.recursion.proofs.ConstructorSemanticFacts.{constructorBranchAtHeight, SpecializedConstructorFacts}

private[recursion] object ConstructorCaseAssembly {

  def liftConstructorCase[N <: lisa.utils.prooflib.ProofTacticLib.Arity](using proof: lisa.SetTheoryLibrary.Proof)(
      sc: SpecializedConstructorFacts[N],
      heightSet: Expr[Ind],
      ambientTerm: Expr[Ind],
      goal: Expr[Prop],
      directBranch: proof.Fact
  ): proof.Fact = {
    val rawBranch = sc.underlying.variables2.reverse.foldLeft(directBranch)((fact, v) =>
      thenHave(∃(v, fact.statement.left.head) |- goal) by LeftExists
    )

    have(constructorBranchAtHeight(sc, heightSet, ambientTerm) |- goal) by Tautology.from(rawBranch)
  }

  def assemblePointwiseFromConstructors(using proof: lisa.SetTheoryLibrary.Proof)(
      constructorDisjunction: Expr[Prop],
      decomposeFact: proof.Fact,
      constructorFacts: Seq[proof.Fact],
      antecedent: Expr[Prop],
      goal: Expr[Prop]
  ): proof.Fact = {
    val branchesToGoal =
      if constructorFacts.size == 1 then
        have(constructorDisjunction |- goal) by Restate.from(constructorFacts.head)
      else
        have(constructorDisjunction |- goal) by LeftOr(constructorFacts*)

    have(goal) by Cut(decomposeFact, branchesToGoal)
    thenHave(antecedent ==> goal) by RightImplies.withParameters(antecedent, goal)
  }
}
