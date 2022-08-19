package lisa.front.parser

import lisa.kernel.proof.SequentCalculus.SCProofStep
import lisa.kernel.proof.SequentCalculus as SC

private[front] case class KernelRuleIdentifiers(symbols: FrontSymbols) {

  private val isLatex: Boolean = symbols.isInstanceOf[FrontSymbols.FrontLatexSymbols.type]

  private val Left: String = "Left"
  private val Right: String = "Right"
  private val Subst: String = "Subst."
  private val Refl: String = "Refl."
  private val Instantiation: String = "Instantiation"
  private val Subproof: String = "Subproof"

  private def symbol(s: String): String = if(isLatex) s"{$s}" else s
  private def text(s: String): String = if(isLatex) raw"\text{$s}" else s
  private def space: String = if(isLatex) "~" else " "
  private def left(s: String): String = s"${text(Left)}$space${symbol(s)}"
  private def right(s: String): String = s"${text(Right)}$space${symbol(s)}"
  private def leftSubst(s: String): String = s"${text(s"$Left $Subst")}$space${symbol(s)}"
  private def rightSubst(s: String): String = s"${text(s"$Right $Subst")}$space${symbol(s)}"

  val Hypothesis: String = text("Hypo.")
  val Cut: String = text("Cut")
  val Rewrite: String = text("Rewrite")
  val Weakening: String = text("Weakening")
  val LeftAnd: String = left(symbols.And)
  val RightAnd: String = right(symbols.And)
  val LeftOr: String = left(symbols.Or)
  val RightOr: String = right(symbols.Or)
  val LeftImplies: String = left(symbols.Implies)
  val RightImplies: String = right(symbols.Implies)
  val LeftIff: String = left(symbols.Iff)
  val RightIff: String = right(symbols.Iff)
  val LeftNot: String = left(symbols.Exclamation)
  val RightNot: String = right(symbols.Exclamation)
  val LeftForall: String = left(symbols.Forall)
  val RightForall: String = right(symbols.Forall)
  val LeftExists: String = left(symbols.Exists)
  val RightExists: String = right(symbols.Exists)
  val LeftExistsOne: String = left(symbols.ExistsOne)
  val RightExistsOne: String = right(symbols.ExistsOne)
  val LeftRefl: String = left(Refl)
  val RightRefl: String = right(Refl)
  val LeftSubstEq: String = leftSubst(symbols.Equal)
  val RightSubstEq: String = rightSubst(symbols.Equal)
  val LeftSubstIff: String = leftSubst(symbols.Iff)
  val RightSubstIff: String = rightSubst(symbols.Iff)
  val FunInstantiation: String = text(s"?Fun. $Instantiation")
  val PredInstantiation: String = text(s"?Pred. $Instantiation")
  val SubproofShown: String = text(Subproof)
  val SubproofHidden: String = text(s"$Subproof (hidden)")
  val Import: String = text("Import")

  def identify(step: SCProofStep): String = step match {
    case _: SC.Hypothesis => Hypothesis
    case _: SC.Cut => Cut
    case _: SC.Rewrite => Rewrite
    case _: SC.Weakening => Weakening
    case _: SC.LeftAnd => LeftAnd
    case _: SC.RightAnd => RightAnd
    case _: SC.LeftOr => LeftOr
    case _: SC.RightOr => RightOr
    case _: SC.LeftImplies => LeftImplies
    case _: SC.RightImplies => RightImplies
    case _: SC.LeftIff => LeftIff
    case _: SC.RightIff => RightIff
    case _: SC.LeftNot => LeftNot
    case _: SC.RightNot => RightNot
    case _: SC.LeftForall => LeftForall
    case _: SC.RightForall => RightForall
    case _: SC.LeftExists => LeftExists
    case _: SC.RightExists => RightExists
    case _: SC.LeftExistsOne => LeftExistsOne
    case _: SC.RightExistsOne => RightExistsOne
    case _: SC.LeftRefl => LeftRefl
    case _: SC.RightRefl => RightRefl
    case _: SC.LeftSubstEq => LeftSubstEq
    case _: SC.RightSubstEq => RightSubstEq
    case _: SC.LeftSubstIff => LeftSubstIff
    case _: SC.RightSubstIff => RightSubstIff
    case _: SC.InstFunSchema => FunInstantiation
    case _: SC.InstPredSchema => PredInstantiation
    case SC.SCSubproof(_, _, true) => SubproofShown
    case SC.SCSubproof(_, _, false) => SubproofHidden
  }

}
