package lisa.utils.fol

import lisa.utils.K
import lisa.utils.fol.ExprOps
import K.given

trait Predef extends ExprOps {

  export K.{given_Conversion_String_Identifier, given_Conversion_Identifier_String}
  /** Creates a variable with the given identifier and sort. */
  def variable[S](using IsSort[S])(id: K.Identifier): Variable[S] = new Variable(id)
  /**  Creates a constant with the given identifier and sort. */
  def constant[S](using IsSort[S])(id: K.Identifier): Constant[S] = new Constant(id)
  /** Creates a binder with the given identifier and sorts. */
  def binder[S1, S2, S3](using IsSort[S1], IsSort[S2], IsSort[S3])
            (id: K.Identifier): Binder[S1, S2, S3] = new Binder(id)

  /**  Creates a variable with name equal to the scala identifier. Usage:
   * {{{val x = variable[Ind]}}}
   */
  def variable[S](using name: sourcecode.Name, is: IsSort[S]): Variable[S] = new Variable(name.value)
  /**  Creates a constant with name equal to the scala identifier. Usage:
   * {{{val c = constant[Ind]}}}
   */
  def constant[S](using name: sourcecode.Name, is: IsSort[S]): Constant[S] = new Constant(name.value)
  /**  Creates a binder with name equal to the scala identifier. Usage:
   * {{{val B = binder[Ind, Prop, Prop]}}}
   */
  def binder[S1, S2, S3](using name: sourcecode.Name)
            (using IsSort[S1], IsSort[S2], IsSort[S3]): Binder[S1, S2, S3] = new Binder(name.value)

  /**  Creates a variable with a runtime sort. */
  def variable(id: K.Identifier, s: K.Sort): Variable[?] = Variable.unsafe(id, s)
  /**  Creates a constant with a runtime sort. */
  def constant(id: K.Identifier, s: K.Sort): Constant[?] = Constant.unsafe(id, s)

  /**  Creates a variable with name equal to the scala identifier and a runtime sort. Usage:
   * {{{val x = variable(K.Ind))}}}
   */
  def variable(using name: sourcecode.Name)(s: K.Sort): Variable[?] = Variable.unsafe(name.value, s)
  /**  Creates a constant with name equal to the scala identifier and a runtime sort. Usage:
   * {{{val c = constant(K.Ind))}}}
   */
  def constant(using name: sourcecode.Name)(s: K.Sort): Constant[?] = Constant.unsafe(name.value, s)
  

  val equality = constant[Ind >>: Ind >>: Prop]("=")
  val === = equality
  val ＝ = equality

  extension (t: Expr[Ind]) {
    infix def ===(u: Expr[Ind]): Expr[Prop] = equality(t)(u)
    infix def ＝(u: Expr[Ind]): Expr[Prop] = equality(t)(u)
  }

  val top = constant[Prop]("⊤")
  val ⊤ : top.type = top
  val True: top.type = top

  val bot = constant[Prop]("⊥")
  val ⊥ : bot.type = bot
  val False: bot.type = bot

  val neg = constant[Prop >>: Prop]("¬")
  val ¬ : neg.type = neg
  val ! : neg.type = neg

  val and = constant[Prop >>: Prop >>: Prop]("∧").printInfix()
  val /\ : and.type = and
  val ∧ : and.type = and

  val or = constant[Prop >>: Prop >>: Prop]("∨").printInfix()
  val \/ : or.type = or
  val ∨ : or.type = or

  val implies = constant[Prop >>: Prop >>: Prop]("⇒").printInfix()
  val ==> : implies.type = implies

  val iff = constant[Prop >>: Prop >>: Prop]("⇔").printInfix()
  val <=> : iff.type = iff
  val ⇔ : iff.type = iff

  val forall = binder[Ind, Prop, Prop]("∀")
  val ∀ : forall.type = forall

  val exists = binder[Ind, Prop, Prop]("∃")
  val ∃ : exists.type = exists

  val epsilon = binder[Ind, Prop, Ind]("ε")
  val ε : epsilon.type = epsilon

  extension (f: Expr[Prop]) {
    def unary_! = neg(f)
    infix inline def ==>(g: Expr[Prop]): Expr[Prop] = implies(f)(g)
    infix inline def <=>(g: Expr[Prop]): Expr[Prop] = iff(f)(g)
    infix inline def /\(g: Expr[Prop]): Expr[Prop] = and(f)(g)
    infix inline def ∧(g: Expr[Prop]): Expr[Prop] = and(f)(g)
    infix inline def \/(g: Expr[Prop]): Expr[Prop] = or(f)(g)
    infix inline def ∨(g: Expr[Prop]): Expr[Prop] = or(f)(g)
  }

  /** Conjunction of all the formulas in the iterable. Must be non-empty */
  def andAll(forms: IterableOnce[Expr[Prop]]): Expr[Prop] =
    forms.iterator.reduce(_ /\ _)

  /** Conjunction of all the formulas in the iterable, or True if the iterable is empty. */
  def andAllOrTrue(forms: IterableOnce[Expr[Prop]]): Expr[Prop] =
    forms.iterator.reduceOption(_ /\ _).getOrElse(top)

  /** Disjunction of all the formulas in the iterable. Must be non-empty */
  def orAll(forms: IterableOnce[Expr[Prop]]): Expr[Prop] =
    forms.iterator.reduce(_ \/ _)

  /** Disjunction of all the formulas in the iterable, or False if the iterable is empty. */
  def orAllOrFalse(forms: IterableOnce[Expr[Prop]]): Expr[Prop] =
    forms.iterator.reduceOption(_ \/ _).getOrElse(bot)

  /** Maps a kernel expression to a corresponding front-end expression. */
  def asFrontExpression(e: K.Expression): Expr[?] = e match
    case c: K.Constant => asFrontConstant(c)
    case v: K.Variable => asFrontVariable(v)
    case a: K.Application => asFrontApplication(a)
    case l: K.Lambda => asFrontLambda(l)

  /** Maps a kernel constant to a corresponding front-end constant. */
  def asFrontConstant(c: K.Constant): Constant[?] = 
    new Constant[Ind](c.id)(using unsafeSortEvidence(c.sort))

  /** Maps a kernel variable to a corresponding front-end variable. */
  def asFrontVariable(v: K.Variable): Variable[?] =
    new Variable[Ind](v.id)(using unsafeSortEvidence(v.sort))
  
  /** Maps a kernel application to a corresponding front-end application. */
  def asFrontApplication(a: K.Application): App[?, ?] = 
    new App(asFrontExpression(a.f).asInstanceOf, asFrontExpression(a.arg))
  
  /** Maps a kernel lambda to a corresponding front-end lambda. */
  def asFrontLambda(l: K.Lambda): Abs[?, ?] =
    new Abs(asFrontVariable(l.v).asInstanceOf, asFrontExpression(l.body))

  /** Computes the greatest identifier in a sequence of expressions. */
  def greatestId(exprs: Seq[K.Expression | Expr[?] | K.Identifier ]): Int = 
    exprs.view.flatMap({
      case e: K.Expression => e.freeVariables.map(_.id)
      case e: Expr[?] => e.freeVars.map(_.id)
      case id: K.Identifier => Seq(id)
    }).map(_.no).max

  /** Returns a fresh identifier based on the greatest identifier in a sequence of expressions. */
  def freshId(exprs: Iterable[K.Expression | Expr[?] | K.Identifier ], base: String = "x"): K.Identifier = {
    val i = exprs.view.flatMap({
      case e: K.Expression => e.freeVariables.map(_.id)
      case e: Expr[?] => e.freeVars.map(_.id)
      case id: K.Identifier => Seq(id)
    }).filter(_.name == base).map(_.no).max
    K.Identifier(base, i + 1)
  }

  /** Returns `n`` fresh identifiers based on the greatest identifier in a sequence of expressions. */
  def nFreshIds(n: Int, exprs: Seq[K.Expression | Expr[?] | K.Identifier ], base: String = "x"): Seq[K.Identifier] = {
    val i = exprs.view.flatMap({
      case e: K.Expression => e.freeVariables.map(_.id)
      case e: Expr[?] => e.freeVars.map(_.id)
      case id: K.Identifier => Seq(id)
    }).filter(_.name == base).map(_.no).max
    (i + 1 to i + n).map(K.Identifier(base, _))
  }


  /** Extractor object for functional expressions and types. */
  object Functional :
    /** Usage: 
      * {{{
      * (e: Expr[Ind >>: Ind >>: Ind]) match 
      *   case Functional(l) => ...// l = Seq(K.Ind, K.Ind)
      * }}}
      */
    def unapply(e: Expr[?]): Option[Seq[K.Sort]] = 
      if e.sort.isFunctional then Some(K.flatTypeParameters(e.sort)) else None
    
    /** Usage:
      * {{{
      * (K.Ind -> K.Ind -> K.Ind) match 
      *   case Functional(l) => ...// l = Seq(K.Ind, K.Ind)
      * }}}
      */
    def unapply(s: K.Sort): Option[Seq[K.Sort]] = 
      if s.isFunctional then Some(K.flatTypeParameters(s)) else None
      
  /** Extractor object for predicate expressions and types. */
  object Predicate:
    /**  Usage: 
      * {{{
      * (e: Expr[Ind >>: Ind >>: Prop]) match 
      *   case Predicate(l) => ...// l = Seq(K.Ind, K.Ind)
      * }}}
      */
    def unapply(e: Expr[?]): Option[Seq[K.Sort]] = 
      if e.sort.isPredicate then Some(K.flatTypeParameters(e.sort)) else None
    
    /** Usage:
      * {{{
      * (K.Ind -> K.Ind -> Prop) match 
      *   case Predicate(l) => ...// l = Seq(K.Ind, K.Ind)
      * }}}
      */
    def unapply(s: K.Sort): Option[Seq[K.Sort]] = 
      if s.isPredicate then Some(K.flatTypeParameters(s)) else None

  
  /** Creates pseudo-equality between two expressions, depending on their types, and based on extentionality. For example:
    * {{{
    * makeEq(s, t) // s === t
    * makeEq(ϕ, ψ) // ϕ <=> ψ
    * makeEq(f, g) // ∀(x, f(x) === g(x))
    * makeEq(P, Q) // ∀(x, ∀(y,  P(x)(y) <=> Q(x)(y))
    * }}}
    */
  def makeEq(s: Expr[?], t: Expr[?]): Expr[Prop] = 
    if s.sort != t.sort || !(s.sort.isFunctional || s.sort.isPredicate) then throw new IllegalArgumentException("Can only make equality between predicate and functional expressions")
    val no = ((s.freeVars ++ t.freeVars).view.map(_.id.no) ++ Seq(-1)).max+1
    val vars = (no until no+s.sort.depth).map(i => variable[Ind](K.Identifier("x", i)))
    val inner1 = vars.foldLeft(s)(_ #@ _)
    val inner2 = vars.foldLeft(t)(_ #@ _)
    val base = if (inner1.sort == K.Prop) iff #@ inner1 #@ inner2 else equality #@ inner1 #@ inner2
    vars.foldRight(base : Expr[Prop]) { case (s_arg, acc) => forall(s_arg, acc) }



}