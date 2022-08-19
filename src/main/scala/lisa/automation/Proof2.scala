package lisa.automation

/**
 * The proof package.
 */
object Proof2 {
  export lisa.front.proof.Proof.*
  export lisa.automation.front.predef.Predef.*
  val introHypo: RuleHypothesis.type = RuleHypothesis
  val introLAnd: RuleIntroductionLeftAnd.type = RuleIntroductionLeftAnd
  val introRAnd: RuleIntroductionRightAnd.type = RuleIntroductionRightAnd
  val introLOr: RuleIntroductionLeftOr.type = RuleIntroductionLeftOr
  val introROr: RuleIntroductionRightOr.type = RuleIntroductionRightOr
  val introLImp: RuleIntroductionLeftImplies.type = RuleIntroductionLeftImplies
  val introRImp: RuleIntroductionRightImplies.type = RuleIntroductionRightImplies
  val introLIff: RuleIntroductionLeftIff.type = RuleIntroductionLeftIff
  val introRIff: RuleIntroductionRightIff.type = RuleIntroductionRightIff
  val introLNot: RuleIntroductionLeftNot.type = RuleIntroductionLeftNot
  val introRNot: RuleIntroductionRightNot.type = RuleIntroductionRightNot
  val introRRefl: RuleIntroductionRightRefl.type = RuleIntroductionRightRefl
  val introLForall: RuleIntroductionLeftForall.type = RuleIntroductionLeftForall
  val introRForall: RuleIntroductionRightForall.type = RuleIntroductionRightForall
  val introLExists: RuleIntroductionLeftExists.type = RuleIntroductionLeftExists
  val introRExists: RuleIntroductionRightExists.type = RuleIntroductionRightExists
  val introLSubstEq: RuleIntroductionLeftSubstEq.type = RuleIntroductionLeftSubstEq
  val introRSubstEq: RuleIntroductionRightSubstEq.type = RuleIntroductionRightSubstEq
  val introLSubstIff: RuleIntroductionLeftSubstIff.type = RuleIntroductionLeftSubstIff
  val introRSubstIff: RuleIntroductionRightSubstIff.type = RuleIntroductionRightSubstIff
  // RuleIntroductionLeftExistsOne & RuleIntroductionRightExistsOne
  val introRForallS: RuleIntroductionRightForallSchema.type = RuleIntroductionRightForallSchema
  val introLExistsS: RuleIntroductionLeftExistsSchema.type = RuleIntroductionLeftExistsSchema

  val elimCut: RuleCut.type = RuleCut
  val elimLRefl: RuleEliminationLeftRefl.type = RuleEliminationLeftRefl
  val elimRForallS: RuleEliminationRightForallSchema.type = RuleEliminationRightForallSchema
  val elimLSubstIff: RuleEliminationLeftSubstIff.type = RuleEliminationLeftSubstIff
  val elimRSubstIff: RuleEliminationRightSubstIff.type = RuleEliminationRightSubstIff
  val elimLSubstEq: RuleEliminationLeftSubstEq.type = RuleEliminationLeftSubstEq
  val elimRSubstEq: RuleEliminationRightSubstEq.type = RuleEliminationRightSubstEq
  val elimRNot: RuleEliminationRightNot.type = RuleEliminationRightNot

  val instFunS: TacticInstantiateFunctionSchema.type = TacticInstantiateFunctionSchema

  val solvePropFast: TacticSolverNative.type = TacticSolverNative
  val solveProp: TacticPropositionalSolver.type = TacticPropositionalSolver
  val rewrite: TacticalRewrite.type = TacticalRewrite
  val weaken: TacticalWeaken.type = TacticalWeaken

  val justificationInst: TacticInstantiateApplyJustification.type = TacticInstantiateApplyJustification


}
