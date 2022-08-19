package lisa.front.proof

import lisa.front.printer.FrontPositionedPrinter
import lisa.front.proof.state.*

/**
 * The proof package.
 */
object Proof
  extends ProofInterfaceDefinitions with RuleDefinitions {

  override protected def pretty(sequent: Sequent): String = FrontPositionedPrinter.prettySequent(sequent)
  override protected def pretty(sequent: PartialSequent): String = FrontPositionedPrinter.prettyPartialSequent(sequent)

  val fallback: TacticFallback.type = TacticFallback
  val combine: TacticCombine.type = TacticCombine

  val justification: TacticApplyJustification.type = TacticApplyJustification

  extension (tactic: Tactic) {
    infix def + : TacticRepeat = TacticRepeat(tactic)
    infix def |(other: Tactic): TacticFallback = TacticFallback(Seq(tactic, other))
    infix def ~(other: Tactic): TacticCombine = tactic match {
      case TacticCombine(tactics) => TacticCombine(tactics :+ other)
      case _ => TacticCombine(Seq(tactic, other))
    }
  }

}
