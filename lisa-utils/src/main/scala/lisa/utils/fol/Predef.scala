package lisa.fol

import lisa.utils.K
import K.given

trait Predef extends Syntax {


  def variable[S](using IsSort[SortOf[S]])(id: K.Identifier): Variable[SortOf[S]] = new Variable(id)
  def constant[S](using IsSort[SortOf[S]])(id: K.Identifier): Constant[SortOf[S]] = new Constant(id)
  def binder[S1, S2, S3](using IsSort[SortOf[S1]], IsSort[SortOf[S2]], IsSort[SortOf[S3]])
            (id: K.Identifier): Binder[SortOf[S1], SortOf[S2], SortOf[S3]] = new Binder(id)

  def variable[S](using name: sourcecode.Name, is: IsSort[SortOf[S]]): Variable[SortOf[S]] = new Variable(name.value)
  def constant[S](using name: sourcecode.Name, is: IsSort[SortOf[S]]): Constant[SortOf[S]] = new Constant(name.value)
  def binder[S1, S2, S3](using name: sourcecode.Name)
            (using IsSort[SortOf[S1]], IsSort[SortOf[S2]], IsSort[SortOf[S3]]): Binder[SortOf[S1], SortOf[S2], SortOf[S3]] = new Binder(name.value)

  val equality = constant[Term >>: Term >>: Formula]("===")
  val === = equality
  val ＝ = equality

  extension (t: Term) {
    infix def ===(u: Term): Formula = equality(t)(u)
    infix def ＝(u: Term): Formula = equality(t)(u)
  }

  val top = constant[Formula]("⊤")
  val ⊤ : top.type = top
  val True: top.type = top

  val bot = constant[Formula]("⊥")
  val ⊥ : bot.type = bot
  val False: bot.type = bot

  val neg = constant[Formula >>: Formula]("¬")
  val ¬ : neg.type = neg
  val ! : neg.type = neg

  val and = constant[Formula >>: Formula >>: Formula]("∧")
  val /\ : and.type = and
  val ∧ : and.type = and

  val or = constant[Formula >>: Formula >>: Formula]("∨")
  val \/ : or.type = or
  val ∨ : or.type = or

  val implies = constant[Formula >>: Formula >>: Formula]("⇒")
  val ==> : implies.type = implies

  val iff = constant[Formula >>: Formula >>: Formula]("⇔")
  val <=> : iff.type = iff
  val ⇔ : iff.type = iff

  val forall = binder[Term, Formula, Formula]("∀")
  val ∀ : forall.type = forall

  val exists = binder[Term, Formula, Formula]("∃")
  val ∃ : exists.type = exists

  val epsilon = binder[Term, Formula, Term]("ε")
  val ε : epsilon.type = epsilon

  val existsOne = binder[Term, Formula, Formula]("∃!")
  val ∃! : existsOne.type = existsOne



  extension (f: Formula) {
    def unary_! = neg(f)
    infix inline def ==>(g: Formula): Formula = implies(f)(g)
    infix inline def <=>(g: Formula): Formula = iff(f)(g)
    infix inline def /\(g: Formula): Formula = and(f)(g)
    infix inline def ∧(g: Formula): Formula = and(f)(g)
    infix inline def \/(g: Formula): Formula = or(f)(g)
    infix inline def ∨(g: Formula): Formula = or(f)(g)
  }

  def asFrontExpression(e: K.Expression): Expr[?] = e match
    case c: K.Constant => asFrontConstant(c)
    case v: K.Variable => asFrontVariable(v)
    case a: K.Application => asFrontApplication(a)
    case l: K.Lambda => asFrontLambda(l)

  def asFrontConstant(c: K.Constant): Constant[?] = 
    new Constant[T](c.id)(using new Sort { type Self = T; val underlying = c.sort })

  def asFrontVariable(v: K.Variable): Variable[?] =
    new Variable[T](v.id)(using new Sort { type Self = T; val underlying = v.sort })
  
  def asFrontApplication(a: K.Application): App[?, ?] = 
    new App[T, T](asFrontExpression(a.f).asInstanceOf, asFrontExpression(a.arg).asInstanceOf)(
      using new Sort { type Self = T; val underlying = a.sort })
  
  def asFrontLambda(l: K.Lambda): Abs[?, ?] =
    new Abs[T, T](asFrontVariable(l.v).asInstanceOf, asFrontExpression(l.body).asInstanceOf)(
      using new Sort { type Self = T; val underlying = l.sort })

}