package lisa.fol

import lisa.kernel.fol.FOL
import lisa.kernel.fol.FOL.{bot, equality, top}

trait Predef extends Common{

  val equality: ConstantPredicateLabel[2] = ConstantPredicateLabel[2](FOL.Identifier("="))
  val === = equality
  val ＝ = equality

  extension (t: Term) {
    infix def ===(u: Term): Formula = equality(t, u)
    infix def ＝(u: Term): Formula = equality(t, u)
  }


  val top: ConstantFormula = ConstantFormula(FOL.Identifier("⊤"))
  val ⊤  = top
  val True = top

  val bot: ConstantFormula = ConstantFormula(FOL.Identifier("⊥"))
  val ⊥ = bot
  val False = bot

  case object Neg extends ConstantConnectorLabel[1] {val underlyingLabel = FOL.Neg}
  val neg = Neg
  val ¬ = Neg
  val ! = Neg

  case object And extends ConstantConnectorLabel[-1]{val underlyingLabel = FOL.And}
  val and = And
  val /\ = And

  case object Or extends ConstantConnectorLabel[-1]{val underlyingLabel = FOL.Or}
  val or = Or
  val \/ = Or

  case object Implies extends ConstantConnectorLabel[2]{val underlyingLabel = FOL.Implies}
  val implies = Implies
  val ==> = Implies

  case object Iff extends ConstantConnectorLabel[2]{val underlyingLabel = FOL.Iff}
  val iff = Iff
  val <=> = Iff

  case object Forall extends BaseBinderLabel {
    val id = FOL.Identifier("∀")
    val underlyingLabel: FOL.Forall.type = FOL.Forall
  }
  val forall = Forall
  val ∀ = forall

  case object Exists extends BaseBinderLabel {
    val id = FOL.Identifier("∃")
    val underlyingLabel: FOL.Exists.type = FOL.Exists
  }
  val exists = Exists
  val ∃ = exists

  case object ExistsOne extends BaseBinderLabel {
    val id = FOL.Identifier("∃!")
    val underlyingLabel: FOL.ExistsOne.type = FOL.ExistsOne
  }
  val existsOne = ExistsOne
  val ∃! = existsOne


  extension (f: Formula) {
    def unary_! = Neg(f*:EmptyTuple)
    infix inline def ==>(g: Formula): Formula = Implies(f, g)
    infix inline def <=>(g: Formula): Formula = Iff(f, g)
    infix inline def /\(g: Formula): Formula = And(List(f, g))
    infix inline def \/(g: Formula): Formula = Or(List(f, g))
  }


}
