package lisa.fol

import lisa.utils.K

trait Predef extends Common{

  val equality: ConstantPredicateLabel[2] = ConstantPredicateLabel[2](K.Identifier("="), 2)
  val === = equality
  val ＝ = equality

  extension (t: Term) {
    infix def ===(u: Term): Formula = equality(t, u)
    infix def ＝(u: Term): Formula = equality(t, u)
  }


  val top: ConstantFormula = ConstantFormula(K.Identifier("⊤"))
  val ⊤  = top
  val True = top

  val bot: ConstantFormula = ConstantFormula(K.Identifier("⊥"))
  val ⊥ = bot
  val False = bot

  case object Neg extends ConstantConnectorLabel[1] {val underlyingLabel = K.Neg; val arity = 1}
  val neg = Neg
  val ¬ = Neg
  val ! = Neg

  case object And extends ConstantConnectorLabel[-1]{val underlyingLabel = K.And; val arity = -1}
  val and = And
  val /\ = And

  case object Or extends ConstantConnectorLabel[-1]{val underlyingLabel = K.Or; val arity = -1}
  val or = Or
  val \/ = Or

  case object Implies extends ConstantConnectorLabel[2]{val underlyingLabel = K.Implies; val arity = 2}
  val implies = Implies
  val ==> = Implies

  case object Iff extends ConstantConnectorLabel[2]{val underlyingLabel = K.Iff; val arity = 2}
  val iff = Iff
  val <=> = Iff

  case object Forall extends BaseBinderLabel {
    val id = K.Identifier("∀")
    val underlyingLabel: K.Forall.type = K.Forall
  }
  val forall = Forall
  val ∀ = forall

  case object Exists extends BaseBinderLabel {
    val id = K.Identifier("∃")
    val underlyingLabel: K.Exists.type = K.Exists
  }
  val exists = Exists
  val ∃ = exists

  case object ExistsOne extends BaseBinderLabel {
    val id = K.Identifier("∃!")
    val underlyingLabel: K.ExistsOne.type = K.ExistsOne
  }
  val existsOne = ExistsOne
  val ∃! = existsOne


  extension (f: Formula) {
    def unary_! = Neg(f *: EmptyTuple)
    infix inline def ==>(g: Formula): Formula = Implies(f, g)
    infix inline def <=>(g: Formula): Formula = Iff(f, g)
    infix inline def /\(g: Formula): Formula = And(List(f, g))
    infix inline def \/(g: Formula): Formula = Or(List(f, g))
  }


}
