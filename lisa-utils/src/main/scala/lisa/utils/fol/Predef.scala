package lisa.utils.fol

import lisa.utils.K
import lisa.utils.fol.ExprOps

import scala.annotation.showAsInfix

import K.given

trait Predef extends ExprOps {

  export K.{given_Conversion_String_Identifier, given_Conversion_Identifier_String}

  /**
   * Creates a variable with the given identifier and sort.
   */
  def variable[S](using IsSort[S])(id: K.Identifier): Variable[S] = new Variable(id)

  /**
   *  Creates a constant with the given identifier and sort.
   */
  def constant[S](using IsSort[S])(id: K.Identifier): Constant[S] = new Constant(id)

  /**
   * Creates a binder with the given identifier and sorts.
   */
  def binder[S1, S2, S3](using IsSort[S1], IsSort[S2], IsSort[S3])(id: K.Identifier): Binder[S1, S2, S3] = new Binder(id)

  /**
   *  Creates a variable with name equal to the scala identifier. Usage:
   * {{{val x = variable[Ind]}}}
   */
  def variable[S](using name: sourcecode.Name, is: IsSort[S]): Variable[S] = new Variable(name.value)

  /**
   *  Creates a constant with name equal to the scala identifier. Usage:
   * {{{val c = constant[Ind]}}}
   */
  def constant[S](using name: sourcecode.Name, is: IsSort[S]): Constant[S] = new Constant(name.value)

  /**
   *  Creates a binder with name equal to the scala identifier. Usage:
   * {{{val B = binder[Ind, Prop, Prop]}}}
   */
  def binder[S1, S2, S3](using name: sourcecode.Name)(using IsSort[S1], IsSort[S2], IsSort[S3]): Binder[S1, S2, S3] = new Binder(name.value)

  /**
   *  Creates a variable with a runtime sort.
   */
  def variable(id: K.Identifier, s: K.Sort): Variable[?] = Variable.unsafe(id, s)

  /**
   *  Creates a constant with a runtime sort.
   */
  def constant(id: K.Identifier, s: K.Sort): Constant[?] = Constant.unsafe(id, s)

  /**
   *  Creates a variable with name equal to the scala identifier and a runtime sort. Usage:
   * {{{val x = variable(K.Ind))}}}
   */
  def variable(using name: sourcecode.Name)(s: K.Sort): Variable[?] = Variable.unsafe(name.value, s)

  /**
   *  Creates a constant with name equal to the scala identifier and a runtime sort. Usage:
   * {{{val c = constant(K.Ind))}}}
   */
  def constant(using name: sourcecode.Name)(s: K.Sort): Constant[?] = Constant.unsafe(name.value, s)

  object equality extends Constant[Ind >>: Ind >>: Prop]("=") {
    this.printInfix()

    def unapply(e: Expr[Prop]): Option[(Expr[Ind], Expr[Ind])] = {
      val === = this
      e match {
        case App(App(`===`, x), y) => Some(x, y)
        case _ => None
      }
    }
  }
  val === = equality
  val ＝ = equality

  extension (t: Expr[Ind]) {
    infix def ===(u: Expr[Ind]): Expr[Prop] = equality(t)(u)
    infix def ＝(u: Expr[Ind]): Expr[Prop] = equality(t)(u)
    infix def =/=(u: Expr[Ind]): Expr[Prop] = ¬(t === u)
    infix def ≠(u: Expr[Ind]): Expr[Prop] = ¬(t === u)
  }

  val top = constant[Prop]("⊤")
  val ⊤ : top.type = top
  val True: top.type = top

  val bot = constant[Prop]("⊥")
  val ⊥ : bot.type = bot
  val False: bot.type = bot

  object neg extends Constant[Prop >>: Prop]("¬") {
    def unapply(e: Expr[Prop]): Option[Expr[Prop]] = {
      val ¬ = this
      e match {
        case App(`¬`, f) => Some(f)
        case _ => None
      }
    }
  }

  val ¬ : neg.type = neg
  val ! : neg.type = neg
  type ¬ = neg.type

  object and extends Constant[Prop >>: Prop >>: Prop]("∧") {
    this.printInfix()

    def unapply(e: Expr[Prop]): Option[(Expr[Prop], Expr[Prop])] = {
      val conjunction = this
      e match {
        case App(App(`conjunction`, x), y) => Some((x, y))
        case _ => None
      }
    }
  }
  val /\ : and.type = and
  val ∧ : and.type = and
  @showAsInfix
  type /\ = and.type

  object or extends Constant[Prop >>: Prop >>: Prop]("∨") {
    this.printInfix()

    def unapply(e: Expr[Prop]): Option[(Expr[Prop], Expr[Prop])] = {
      val disjunction = this
      e match {
        case App(App(`disjunction`, x), y) => Some((x, y))
        case _ => None
      }
    }
  }
  val \/ : or.type = or
  val ∨ : or.type = or
  @showAsInfix
  type \/ = or.type

  object implies extends Constant[Prop >>: Prop >>: Prop]("⇒") {
    this.printInfix()

    def unapply(e: Expr[Prop]): Option[(Expr[Prop], Expr[Prop])] = {
      val ==> = this
      e match {
        case App(App(`==>`, x), y) => Some((x, y))
        case _ => None
      }
    }
  }
  val ==> : implies.type = implies
  @showAsInfix
  type ==> = implies.type

  object iff extends Constant[Prop >>: Prop >>: Prop]("⇔") {
    this.printInfix()

    def unapply(e: Expr[Prop]): Option[(Expr[Prop], Expr[Prop])] = {
      val <=> = this
      e match {
        case App(App(`<=>`, x), y) => Some((x, y))
        case _ => None
      }
    }
  }
  val <=> : iff.type = iff
  val ⇔ : iff.type = iff
  @showAsInfix
  type <=> = iff.type

  object forall extends Binder[Ind, Prop, Prop]("∀") {
    this.printInfix()

    def unapply(e: Expr[Prop]): Option[(Variable[Ind], Expr[Prop])] = {
      val ∀ = this
      e match {
        case App(`∀`, λ(x, body)) => Some((x, body))
        case _ => None
      }
    }
  }
  val ∀ : forall.type = forall
  type ∀ = forall.type

  object exists extends Binder[Ind, Prop, Prop]("∃") {
    this.printInfix()

    def unapply(e: Expr[Prop]): Option[(Variable[Ind], Expr[Prop])] = {
      val ∃ = this
      e match {
        case App(`∃`, λ(x, body)) => Some((x, body))
        case _ => None
      }
    }
  }
  val ∃ : exists.type = exists
  type ∃ = exists.type

  object epsilon extends Binder[Ind, Prop, Ind]("ε") {
    this.printInfix()

    def unapply(e: Expr[Ind]): Option[(Variable[Ind], Expr[Prop])] = {
      val ε = this
      e match {
        case App(`ε`, λ(x, body)) => Some((x, body))
        case _ => None
      }
    }
  }
  val ε: epsilon.type = epsilon
  type ε = epsilon.type

  val lambda: Abs.type = Abs
  val λ: Abs.type = Abs
  type λ = Abs

  extension (f: Expr[Prop]) {
    def unary_! = neg(f)
    infix inline def ==>(g: Expr[Prop]): Expr[Prop] = implies(f)(g)
    infix inline def <=>(g: Expr[Prop]): Expr[Prop] = iff(f)(g)
    infix inline def /\(g: Expr[Prop]): Expr[Prop] = and(f)(g)
    infix inline def ∧(g: Expr[Prop]): Expr[Prop] = and(f)(g)
    infix inline def \/(g: Expr[Prop]): Expr[Prop] = or(f)(g)
    infix inline def ∨(g: Expr[Prop]): Expr[Prop] = or(f)(g)
  }

  /**
   * Conjunction of all the formulas in the iterable. Must be non-empty
   */
  def andAll(forms: IterableOnce[Expr[Prop]]): Expr[Prop] =
    forms.iterator.reduce(_ /\ _)

  /**
   * Conjunction of all the formulas in the iterable, or True if the iterable is empty.
   */
  def andAllOrTrue(forms: IterableOnce[Expr[Prop]]): Expr[Prop] =
    forms.iterator.reduceOption(_ /\ _).getOrElse(top)

  /**
   * Disjunction of all the formulas in the iterable. Must be non-empty
   */
  def orAll(forms: IterableOnce[Expr[Prop]]): Expr[Prop] =
    forms.iterator.reduce(_ \/ _)

  /**
   * Disjunction of all the formulas in the iterable, or False if the iterable is empty.
   */
  def orAllOrFalse(forms: IterableOnce[Expr[Prop]]): Expr[Prop] =
    forms.iterator.reduceOption(_ \/ _).getOrElse(bot)

  /**
   * Beta-reduces the given expression.
   */
  def betaReduce[T](e: Expr[T]): Expr[T] = e match {
    case App(f, arg) =>
      val reducedArg = betaReduce(arg)
      betaReduce(f) match {
        case Abs(v, body) => body.substituteUnsafe(Map(v -> reducedArg))
        case reducedF => App(reducedF, reducedArg)
      }
    case Abs(v, body) => Abs(v, betaReduce(body))
    case _ => e
  }

  /**
   * Maps a kernel expression to a corresponding front-end expression.
   */
  def asFrontExpression(e: K.Expression): Expr[?] = e match
    case c: K.Constant => asFrontConstant(c)
    case v: K.Variable => asFrontVariable(v)
    case a: K.Application => asFrontApplication(a)
    case l: K.Lambda => asFrontLambda(l)

  /**
   * Maps a kernel constant to a corresponding front-end constant.
   */
  def asFrontConstant(c: K.Constant): Constant[?] =
    new Constant[Ind](c.id)(using unsafeSortEvidence(c.sort))

  /**
   * Maps a kernel variable to a corresponding front-end variable.
   */
  def asFrontVariable(v: K.Variable): Variable[?] =
    new Variable[Ind](v.id)(using unsafeSortEvidence(v.sort))

  /**
   * Maps a kernel application to a corresponding front-end application.
   */
  def asFrontApplication(a: K.Application): App[?, ?] =
    new App(asFrontExpression(a.f).asInstanceOf, asFrontExpression(a.arg))

  /**
   * Maps a kernel lambda to a corresponding front-end lambda.
   */
  def asFrontLambda(l: K.Lambda): Abs[?, ?] =
    new Abs(asFrontVariable(l.v).asInstanceOf, asFrontExpression(l.body))

  /**
   * Computes the greatest identifier in a sequence of expressions.
   */
  def greatestId(exprs: Seq[K.Expression | Expr[?] | K.Identifier]): Int =
    exprs.view
      .flatMap({
        case e: K.Expression => e.freeVariables.map(_.id)
        case e: Expr[?] => e.freeVars.map(_.id)
        case id: K.Identifier => Seq(id)
      })
      .map(_.no)
      .max

  /**
   * Returns a fresh identifier based on the greatest identifier in a sequence of expressions.
   */
  def freshId(exprs: Iterable[K.Expression | Expr[?] | K.Identifier], base: String = "x"): K.Identifier = {
    val i = exprs.view
      .flatMap({
        case e: K.Expression => e.freeVariables.map(_.id)
        case e: Expr[?] => e.freeVars.map(_.id)
        case id: K.Identifier => Seq(id)
      })
      .filter(_.name == base)
      .map(_.no)
      .maxOption
      .getOrElse(-1)
    K.Identifier(base, i + 1)
  }

  /**
   * Returns `n`` fresh identifiers based on the greatest identifier in a sequence of expressions.
   */
  def nFreshIds(n: Int, exprs: Seq[K.Expression | Expr[?] | K.Identifier], base: String = "x"): Seq[K.Identifier] = {
    val i = exprs.view
      .flatMap({
        case e: K.Expression => e.freeVariables.map(_.id)
        case e: Expr[?] => e.freeVars.map(_.id)
        case id: K.Identifier => Seq(id)
      })
      .filter(_.name == base)
      .map(_.no)
      .max
    (i + 1 to i + n).map(K.Identifier(base, _))
  }

  /**
   * Extractor object for functional expressions and types.
   */
  object Functional:
    /**
     * Usage:
     * {{{
     * (e: Expr[Ind >>: Ind >>: Ind]) match
     *   case Functional(l) => ...// l = Seq(K.Ind, K.Ind)
     * }}}
     */
    def unapply(e: Expr[?]): Option[Seq[K.Sort]] =
      if e.sort.isFunctional then Some(K.flatTypeParameters(e.sort)) else None

    /**
     * Usage:
     * {{{
     * (K.Ind -> K.Ind -> K.Ind) match
     *   case Functional(l) => ...// l = Seq(K.Ind, K.Ind)
     * }}}
     */
    def unapply(s: K.Sort): Option[Seq[K.Sort]] =
      if s.isFunctional then Some(K.flatTypeParameters(s)) else None

  /**
   * Extractor object for predicate expressions and types.
   */
  object Predicate:
    /**
     *  Usage:
     * {{{
     * (e: Expr[Ind >>: Ind >>: Prop]) match
     *   case Predicate(l) => ...// l = Seq(K.Ind, K.Ind)
     * }}}
     */
    def unapply(e: Expr[?]): Option[Seq[K.Sort]] =
      if e.sort.isPredicate then Some(K.flatTypeParameters(e.sort)) else None

    /**
     * Usage:
     * {{{
     * (K.Ind -> K.Ind -> Prop) match
     *   case Predicate(l) => ...// l = Seq(K.Ind, K.Ind)
     * }}}
     */
    def unapply(s: K.Sort): Option[Seq[K.Sort]] =
      if s.isPredicate then Some(K.flatTypeParameters(s)) else None

  /**
   * Creates pseudo-equality between two expressions, depending on their types, and based on extentionality. For example:
   * {{{
   * makeEq(s, t) // s === t
   * makeEq(ϕ, ψ) // ϕ <=> ψ
   * makeEq(f, g) // ∀(x, f(x) === g(x))
   * makeEq(P, Q) // ∀(x, ∀(y,  P(x)(y) <=> Q(x)(y))
   * }}}
   */
  def makeEq(s: Expr[?], t: Expr[?]): Expr[Prop] =
    require(s.sort == t.sort, s"$s and $t must have the same sort to be compared for equality")
    require(s.sort.isPredicate || s.sort.isFunctional, s"Can only make equality between predicate or functional expressions\n\tFound: $s and $t")

    val no = ((s.freeVars ++ t.freeVars).view.map(_.id.no) ++ Seq(-1)).max + 1
    val vars = (no until no + s.sort.depth).map(i => variable[Ind](K.Identifier("x", i)))
    val inner1 = s #@@ vars
    val inner2 = t #@@ vars
    val base =
      if (inner1.sort == K.Prop)
        inner1.asInstanceOf[Expr[Prop]] <=> inner2.asInstanceOf[Expr[Prop]]
      else inner1.asInstanceOf[Expr[Ind]] === inner2.asInstanceOf[Expr[Ind]]
    vars.foldRight(base: Expr[Prop]) { case (s_arg, acc) => ∀(s_arg, acc) }

}
