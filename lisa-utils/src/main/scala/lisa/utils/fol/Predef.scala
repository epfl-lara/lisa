package lisa.fol

import lisa.utils.K
import K.given

trait Predef extends Syntax {

  export K.{given_Conversion_String_Identifier, given_Conversion_Identifier_String}
  
  def variable[S](using IsSort[SortOf[S]])(id: K.Identifier): Variable[SortOf[S]] = new Variable(id)
  def constant[S](using IsSort[SortOf[S]])(id: K.Identifier): Constant[SortOf[S]] = new Constant(id)
  def binder[S1, S2, S3](using IsSort[SortOf[S1]], IsSort[SortOf[S2]], IsSort[SortOf[S3]])
            (id: K.Identifier): Binder[SortOf[S1], SortOf[S2], SortOf[S3]] = new Binder(id)

  def variable[S](using name: sourcecode.Name, is: IsSort[SortOf[S]]): Variable[SortOf[S]] = new Variable(name.value)
  def constant[S](using name: sourcecode.Name, is: IsSort[SortOf[S]]): Constant[SortOf[S]] = new Constant(name.value)
  def binder[S1, S2, S3](using name: sourcecode.Name)
            (using IsSort[SortOf[S1]], IsSort[SortOf[S2]], IsSort[SortOf[S3]]): Binder[SortOf[S1], SortOf[S2], SortOf[S3]] = new Binder(name.value)

  def variable(id: K.Identifier, s: K.Sort): Variable[?] = Variable.unsafe(id, s)
  def constant(id: K.Identifier, s: K.Sort): Constant[?] = Constant.unsafe(id, s)

  def variable(using name: sourcecode.Name)(s: K.Sort): Variable[?] = Variable.unsafe(name.value, s)
  def constant(using name: sourcecode.Name)(s: K.Sort): Constant[?] = Constant.unsafe(name.value, s)
  

  val equality = constant[Term >>: Term >>: Formula]("=")
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

  val and = constant[Formula >>: Formula >>: Formula]("∧").setInfix()
  val /\ : and.type = and
  val ∧ : and.type = and

  val or = constant[Formula >>: Formula >>: Formula]("∨").setInfix()
  val \/ : or.type = or
  val ∨ : or.type = or

  val implies = constant[Formula >>: Formula >>: Formula]("⇒").setInfix()
  val ==> : implies.type = implies

  val iff = constant[Formula >>: Formula >>: Formula]("⇔").setInfix()
  val <=> : iff.type = iff
  val ⇔ : iff.type = iff

  val forall = binder[Term, Formula, Formula]("∀")
  val ∀ : forall.type = forall

  val exists = binder[Term, Formula, Formula]("∃")
  val ∃ : exists.type = exists

  val epsilon = binder[Term, Formula, Term]("ε")
  val ε : epsilon.type = epsilon

  extension (f: Formula) {
    def unary_! = neg(f)
    infix inline def ==>(g: Formula): Formula = implies(f)(g)
    infix inline def <=>(g: Formula): Formula = iff(f)(g)
    infix inline def /\(g: Formula): Formula = and(f)(g)
    infix inline def ∧(g: Formula): Formula = and(f)(g)
    infix inline def \/(g: Formula): Formula = or(f)(g)
    infix inline def ∨(g: Formula): Formula = or(f)(g)
  }

  inline def andAll(forms: IterableOnce[Formula]): Formula =
    forms.iterator.reduce(_ /\ _)

  inline def orAll(forms: IterableOnce[Formula]): Formula =
    forms.iterator.reduce(_ \/ _)

  def asFrontExpression(e: K.Expression): Expr[?] = e match
    case c: K.Constant => asFrontConstant(c)
    case v: K.Variable => asFrontVariable(v)
    case a: K.Application => asFrontApplication(a)
    case l: K.Lambda => asFrontLambda(l)

  def asFrontConstant(c: K.Constant): Constant[?] = 
    new Constant[T](c.id)(using unsafeSortEvidence(c.sort))

  def asFrontVariable(v: K.Variable): Variable[?] =
    new Variable[T](v.id)(using unsafeSortEvidence(v.sort))
  
  def asFrontApplication(a: K.Application): App[?, ?] = 
    new App(asFrontExpression(a.f).asInstanceOf, asFrontExpression(a.arg))
  
  def asFrontLambda(l: K.Lambda): Abs[?, ?] =
    new Abs(asFrontVariable(l.v).asInstanceOf, asFrontExpression(l.body))

  def greatestId(exprs: Seq[K.Expression | Expr[?] | K.Identifier ]): Int = 
    exprs.view.flatMap({
      case e: K.Expression => e.freeVariables.map(_.id)
      case e: Expr[?] => e.freeVars.map(_.id)
      case id: K.Identifier => Seq(id)
    }).map(_.no).max

  def freshId(exprs: Iterable[K.Expression | Expr[?] | K.Identifier ], base: String = "x"): K.Identifier = {
    val i = exprs.view.flatMap({
      case e: K.Expression => e.freeVariables.map(_.id)
      case e: Expr[?] => e.freeVars.map(_.id)
      case id: K.Identifier => Seq(id)
    }).filter(_.name == base).map(_.no).max
    K.Identifier(base, i + 1)
  }

  def nFreshIds(n: Int, exprs: Seq[K.Expression | Expr[?] | K.Identifier ], base: String = "x"): Seq[K.Identifier] = {
    val i = exprs.view.flatMap({
      case e: K.Expression => e.freeVariables.map(_.id)
      case e: Expr[?] => e.freeVars.map(_.id)
      case id: K.Identifier => Seq(id)
    }).filter(_.name == base).map(_.no).max
    (i + 1 to i + n).map(K.Identifier(base, _))
  }


  object Functional :
    def unapply(e: Expr[?]): Option[Seq[K.Sort]] = 
      if e.sort.isFunctional then Some(K.flatTypeParameters(e.sort)) else None
    
    def unapply(s: K.Sort): Option[Seq[K.Sort]] = 
      if s.isFunctional then Some(K.flatTypeParameters(s)) else None
      
  object Predicate:
    def unapply(e: Expr[?]): Option[Seq[K.Sort]] = 
      if e.sort.isPredicate then Some(K.flatTypeParameters(e.sort)) else None
    
    def unapply(s: K.Sort): Option[Seq[K.Sort]] = 
      if s.isPredicate then Some(K.flatTypeParameters(s)) else None

  
  def makeEq(s: Expr[?], t: Expr[?]): Formula = 
    if s.sort != t.sort || !(s.sort.isFunctional || s.sort.isPredicate) then throw new IllegalArgumentException("Can only make equality between predicate and functional expressions")
    val no = ((s.freeVars ++ t.freeVars).view.map(_.id.no) ++ Seq(-1)).max+1
    val vars = (no until no+s.sort.depth).map(i => variable[Term](K.Identifier("x", i)))
    val inner1 = vars.foldLeft(s)(_ #@ _)
    val inner2 = vars.foldLeft(t)(_ #@ _)
    val base = if (inner1.sort == K.Formula) iff #@ inner1 #@ inner2 else equality #@ inner1 #@ inner2
    vars.foldRight(base : Formula) { case (s_arg, acc) => forall(s_arg, acc) }



}