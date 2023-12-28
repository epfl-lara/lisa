package lisa.utils

object K {
  export lisa.kernel.fol.FOL.*
  export lisa.kernel.proof.RunningTheory
  export lisa.kernel.proof.SCProofChecker
  export lisa.kernel.proof.SCProof
  export lisa.kernel.proof.SCProofCheckerJudgement
  export lisa.kernel.proof.SequentCalculus.* //{LeftSubstEq => _, RightSubstEq => _, LeftSubstIff => _, RightSubstIff => _, *}
  export lisa.kernel.proof.SequentCalculus as SC
  export lisa.kernel.proof.RunningTheoryJudgement as Judgement
  export lisa.kernel.proof.RunningTheoryJudgement.*
  export lisa.utils.KernelHelpers.{*, given}
  export lisa.utils.parsing.FOLPrinter.*
/*
  def LeftSubstEq(bot: Sequent, t1: Int, equals: List[(Term, Term)], lambdaPhi: LambdaTermFormula): LeftSubstEq2 =
    LeftSubstEq2(bot, t1, equals.map { case (a, b) => (LambdaTermTerm(Seq(), a), LambdaTermTerm(Seq(), b)) }, (lambdaPhi.vars, lambdaPhi.body))

  def RightSubstEq(bot: Sequent, t1: Int, equals: List[(Term, Term)], lambdaPhi: LambdaTermFormula): RightSubstEq2 =
    RightSubstEq2(bot, t1, equals.map { case (a, b) => (LambdaTermTerm(Seq(), a), LambdaTermTerm(Seq(), b)) }, (lambdaPhi.vars, lambdaPhi.body))

  def LeftSubstIff(bot: Sequent, t1: Int, equals: List[(Formula, Formula)], lambdaPhi: LambdaFormulaFormula): LeftSubstIff2 =
    LeftSubstIff2(bot, t1, equals.map { case (a, b) => (LambdaTermFormula(Seq(), a), LambdaTermFormula(Seq(), b)) }, (lambdaPhi.vars, lambdaPhi.body))

  def RightSubstIff(bot: Sequent, t1: Int, equals: List[(Formula, Formula)], lambdaPhi: LambdaFormulaFormula): RightSubstIff2 =
    RightSubstIff2(bot, t1, equals.map { case (a, b) => (LambdaTermFormula(Seq(), a), LambdaTermFormula(Seq(), b)) }, (lambdaPhi.vars, lambdaPhi.body))
    */
}
