package lisa.automation.front.predef

import lisa.front.proof.Proof.*

trait PredefCombinedDefinitions extends PredefRulesDefinitions {

  val TacticPropositionalSolver: Tactic = TacticRepeat(TacticFallback(Seq(
    RuleHypothesis,
    RuleIntroductionLeftAnd, RuleIntroductionRightAnd,
    RuleIntroductionLeftOr, RuleIntroductionRightOr,
    RuleIntroductionLeftImplies, RuleIntroductionRightImplies,
    RuleIntroductionLeftIff, RuleIntroductionRightIff,
    RuleIntroductionLeftNot, RuleIntroductionRightNot,
  )))

}
