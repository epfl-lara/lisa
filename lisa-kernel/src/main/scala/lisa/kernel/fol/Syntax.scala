package lisa.kernel.fol

/** Defines the syntax of statements Lisa's kernel
  * 
  * This syntax is a (conservative) extension of first-order logic with higher order expressions.
  * An expression in Lisa is a term of the simply typed lambda calculus with base types (called [[Sort]]) [[Term]] and [[Formula]].
  * 
  */
private[fol] trait Syntax {

  /** An abstract type, later instantiated  in [[OLEquivalenceChecker]] to be the type of expressions in normal form modulo OL.
    */
  type SimpleExpression

  /** An identifier for a variable or constant symbol.
    *
    * An identifier must not contain one of the following characters: {{{()[]{}?,;_`}}} and must not contain whitespace.
    * 
    * Idiomatic representation is as follows:
    * - Identifier("x", 0) ~ "x"
    * - Identifier("x", 1) ~ "x_1"
    * - Identifier("myvariable", 227) ~ "myvariable_227"
    * 
    * @param name The name of the identifier
    * @param no The index of the identifier. Used to easily compute fresh names.
    */
  sealed case class Identifier(val name: String, val no: Int) {
    require(no >= 0, "Variable index must be positive")
    require(Identifier.isValidIdentifier(name), "Variable name " + name + "is not valid.")
    override def toString: String = if (no == 0) name else name + Identifier.counterSeparator + no
  }

  /** Factory for [[Identifier]] instances.
    * 
    */
  object Identifier {
    /** Extractor for identifiers. */
    def unapply(i: Identifier): Option[(String, Int)] = Some((i.name, i.no))

    /** Creates a new identifier with the given name and index = 0. */
    def apply(name: String): Identifier = new Identifier(name, 0)

    /** Creates a new identifier with the given name and index. */
    def apply(name: String, no: Int): Identifier = new Identifier(name, no)

    val counterSeparator: Char = '_'
    val delimiter: Char = '`'
    val forbiddenChars: Set[Char] = ("()[]{}?,;" + delimiter + counterSeparator).toSet

    /** Checks if a string is a valid identifier. */
    def isValidIdentifier(s: String): Boolean = s.forall(c => !forbiddenChars.contains(c) && !c.isWhitespace)
  }

  /** Creates a fresh identifier based on a base identifier and a set of taken identifiers. 
    * Find the largest index in the set of taken identifiers and increment it by one.
    */
  private[kernel] def freshId(taken: Iterable[Identifier], base: Identifier): Identifier = {
    new Identifier(
      base.name,
      (Iterable(base.no) ++ taken.collect({ case Identifier(base.name, no) =>
        no
      })).max + 1
    )
  }




  /**
    * A `Sort` is a base type in the simply typed lambda calculus of Lisa expressions.
    * 
    * There are two sorts: `Term` and `Formula`.
    */
  sealed trait Sort {
    /** shortcut for `Assow(this, to)` */
    def ->(to: Sort): Arrow = Arrow(this, to)

    /** @return true if the sort is of the form `Term -> ... -> Term -> Term` */
    val isFunctional: Boolean

    /** @return true if the sort is of the form `Term -> ... -> Term -> Formula` */
    val isPredicate: Boolean

    /** @return the number of arguments of the type.
      * 
      * For example, `Term` has depth 0, `Formula -> Term` has depth 1, `Term -> (Formula -> Term) -> Term` has depth 2, etc.
      */
    val depth: Int 
  }

  /** The sort of terms in the simply typed lambda calculus.
    * Expressions of this type correspond to terms of first-order logic.
    * Semantically they are interpreted as elements of the universe, i.e. sets in ZFC.
    */
  case object Term extends Sort {
    val isFunctional = true
    val isPredicate = false
    val depth = 0
  }

  /** The sort of formulas in the simply typed lambda calculus.
    * Expressions of this type correspond to formulas of first-order logic.
    */
  case object Formula extends Sort {
    val isFunctional = false
    val isPredicate = true
    val depth = 0
  }

  /** An arrow sort, representing a function type in the simply typed lambda calculus.
    * The arrow sort is of the form `from -> to`, where `from` and `to` are sorts.
    * 
    * Expressions of type `Term -> ... -> Term -> Term` correspond to function symbols of first-order logic.
    * Expressions of type `Term -> ... -> Term -> Formula` correspond to predicate symbols of first-order logic.
    * Expressions of type `(Term -> Formula) -> Formula` correspond to quantifiers (∀ and ∃) in first-order logic.
    */
  sealed case class Arrow(from: Sort, to: Sort) extends Sort {
    val isFunctional = from == Term && to.isFunctional
    val isPredicate = from == Term && to.isPredicate
    val depth = 1+to.depth
  }

  /** If `typ1` is of the form `typ2 -> to`, returns `Some(to)`, otherwise returns `None`. 
    * 
    * This means, it check that an application of a term of type `typ1` to a term of type `typ2` is legal, and if so returns the resulting type.
    */
  def legalApplication(typ1: Sort, typ2: Sort): Option[Sort] = {
    typ1 match {
      case Arrow(`typ2`, to) => Some(to)
      case _ => None
    }
  }

  /** Store global counters used for distinguishing expressions. 
    * Useful for efficient reference-based equality checking.
    */
  private object ExpressionCounters {
    var totalNumberOfExpressions: Long = 0
    def getNewId: Long = {
      totalNumberOfExpressions += 1
      totalNumberOfExpressions
    }
  }


  /** Expressions are lambda-terms in the simply typed lambda calculus with base types `Term` and `Formula`.
    * 
    * Expressions are the core part of Lisa's kernel and correspond to standard terms and formulas in first-order logic.
    * They are built from constants, variables, applications and abstractions though the following grammar:
    * V ::= x | y | z | ...
    * C ::= a | b | c | f | g | h | ...
    * E ::= V | C | E E | λV.E
    * 
    * Expressions must be well-typed, i.e. the types of the argument in an application must match the type of the function.
    */
  sealed trait Expression {
    /** Cached normal form of the expression by [[OLEquivalenceChecker]]. */
    private[fol] var polarExpr: Option[SimpleExpression] = None
    /** Cached normal form of the expression by [[OLEquivalenceChecker]]. */
    def getPolarExpr : Option[SimpleExpression] = polarExpr
    /** Sort of the expression. */
    val sort: Sort
    /** Unique number of the expression assigned by [[ExpressionCounters]]. Used for efficient reference equality. */
    val uniqueNumber: Long = ExpressionCounters.getNewId
    /** True if the expression contains subexpressions of type `Formula`. */
    val containsFormulas : Boolean
    /** Creates an application of this expression to an argument. */
    def apply(arg: Expression): Application = Application(this, arg)
    /** Extractor for the arguments of the expression.
      * Usage: 
      * {{{
      * Application(Application(f, x), y) match 
      *   case f(x, y) => println("This case is matched")
      * }}}
      */ 
    def unapplySeq(arg: Expression): Option[Seq[Expression]] = arg match {
      case Application(f, arg) if f == this => Some(arg :: Nil)
      case Application(f, arg) => unapplySeq(f).map(fargs => fargs :+ arg)
      case _ => None
    }

    /** The beta-normal form of the expression and if it is in beta-normal form. */
    val (betaNormalForm: Expression, isBetaNormal: Boolean) = this match {
        case Application(f, arg) => {
          val f1 = f.betaNormalForm
          val a2 = arg.betaNormalForm
          f1 match {
            case Lambda(v, body) => (substituteVariables(body, Map(v -> a2)).betaNormalForm, false)
            case _ if f.isBetaNormal && arg.isBetaNormal => (this, true) 
            case _ => (Application(f1, a2), false)
          }
        }
        case Lambda(v, Application(f, arg)) if v == arg => (f.betaNormalForm, false)
        case Lambda(v, inner) if inner.isBetaNormal => (this, true)
        case Lambda(v, inner) => (Lambda(v, inner.betaNormalForm), false)
        case _ => (this, true)
    }
    
    /**
     * @return The list of free variables in the expression.
     */
    def freeVariables: Set[Variable]

    /**
     * @return The list of constant symbols in the expression.
     */
    def constants: Set[Constant]

    /**
     * @return The list of all variables in the expression.
     */
    def allVariables: Set[Variable]
  }

  /**
    * A variable symbol, which is a special case of [[Expression]].
    * 
    * Logically, variables can be bound by lambda abstractions (and quantifiers) or free.
    * Free variables in theorems can be instantiated by valules of the same sort.
    */
  case class Variable(id: Identifier, sort:Sort) extends Expression {
    val containsFormulas = sort == Formula
    def freeVariables: Set[Variable] = Set(this)
    def constants: Set[Constant] = Set()
    def allVariables: Set[Variable] = Set(this)
  }

  /**
    * A constant symbol, which is a special case of [[Expression]].
    * 
    * Constants generalize function and predicate symbols of any arity in strict first-order logic.
    */
  case class Constant(id: Identifier, sort: Sort) extends Expression {
    val containsFormulas = sort == Formula
    def freeVariables: Set[Variable] = Set()
    def constants: Set[Constant] = Set(this)
    def allVariables: Set[Variable] = Set()
  }

  /**
    * An application of an expression to an argument, which is a special case of [[Expression]].
    * `f.sort` must be of the form `arg.sort -> _`.
    */
  case class Application(f: Expression, arg: Expression) extends Expression {
    private val legalapp = legalApplication(f.sort, arg.sort)
    require(legalapp.isDefined, s"Application of $f to $arg is not legal")
    val sort = legalapp.get
    val containsFormulas = sort == Formula || f.containsFormulas || arg.containsFormulas
    def freeVariables: Set[Variable] = f.freeVariables union arg.freeVariables
    def constants: Set[Constant] = f.constants union arg.constants
    def allVariables: Set[Variable] = f.allVariables union arg.allVariables
  }

  /**
    * A lambda abstraction, which is a special case of [[Expression]].
    * 
    * In `Lambda(v, body)`, `v` is a called "bound" in `body`.
    * Every expression that bind a variable uses a Lambda abstraction.
    * 
    * Example: {{{Application(∀, Lambda(x, Application(P, x)))}}} 
    * corresponds to the formula in strict first-order logic ∀x.P(x).
    */
  case class Lambda(v: Variable, body: Expression) extends Expression {
    val containsFormulas = body.containsFormulas
    val sort = (v.sort -> body.sort)

    def freeVariables: Set[Variable] = body.freeVariables - v
    def constants: Set[Constant] = body.constants
    def allVariables: Set[Variable] = body.allVariables
  }
  

  /** The constant symbol for the equality predicate.
    * 
    * Type: `Term -> (Term -> Formula)`. 
    * 
    * Symbol: `=`
    */
  val equality = Constant(Identifier("="),  Term -> (Term -> Formula))

  /** The constant symbol for the true formula. <br>
   * Type: `Formula`.
   * 
   * Symbol: `⊤`
   */
  val top = Constant(Identifier("⊤"), Formula)

  /** The constant symbol for the false formula.
   * 
   * Type: `Formula`.
   * 
   * Symbol: `⊥`
   */
  val bot = Constant(Identifier("⊥"), Formula)

  /** The constant symbol for the negation connector.
   * 
   * Type: `Formula -> Formula`.
   * 
   * Symbol: `¬`
   */
  val neg = Constant(Identifier("¬"), Formula -> Formula)

  /** The constant symbol for the implication connector.
   * 
   * Type: `Formula -> (Formula -> Formula)`.
   * 
   * Symbol: `⇒`
   */
  val implies = Constant(Identifier("⇒"), Formula -> (Formula -> Formula))

  /** The constant symbol for the equivalence connector.
   * 
   * Type: `Formula -> (Formula -> Formula)`.
   * 
   * Symbol: `⇔`
   */

  val iff = Constant(Identifier("⇔"), Formula -> (Formula -> Formula))

  /** The constant symbol for the conjunction connector.
   * 
   * Type: `Formula -> (Formula -> Formula)`.
   * 
   * Symbol: `∧`
   */
  val and = Constant(Identifier("∧"), Formula -> (Formula -> Formula))

  /** The constant symbol for the disjunction connector.
   * 
   * Type: `Formula -> (Formula -> Formula)`.
   * 
   * Symbol: `∨`
   */
  val or = Constant(Identifier("∨"), Formula -> (Formula -> Formula))

  /** The constant symbol for the universal quantifier.
   * 
   * Type: `(Term -> Formula) -> Formula`.
   * 
   * Symbol: `∀`
   * 
   * Usage: `forall(Lambda(x, P(x)))` corresponds to the formula in strict first-order logic ∀x.P(x).
   */
  val forall = Constant(Identifier("∀"), (Term -> Formula) -> Formula)

  /** The constant symbol for the existential quantifier.
   * 
   * Type: `(Term -> Formula) -> Formula`.
   * 
   * Symbol: `∃`
   * 
   * Usage: `exists(Lambda(x, P(x)))` corresponds to the formula in strict first-order logic ∃x.P(x).
   */
  val exists = Constant(Identifier("∃"), (Term -> Formula) -> Formula)

  /** The constant symbol for the epsilon quantifier.
   * 
   * Type: `(Term -> Formula) -> Term`.
   * 
   * Symbol: `ε`
   * 
   * Usage: `epsilon(Lambda(x, P(x)))` corresponds to the term in strict first-order logic εx.P(x).
   * 
   * Denotes Hilbert's epsilon operator. `epsilon(Lambda(x, P(x)))` is some element x such that P(x) holds, or an unknown element if no such x exists.
   */
  val epsilon = Constant(Identifier("ε"), (Term -> Formula) -> Term)


  /**
   * Performs simultaneous substitution of multiple variables by multiple [[Expression]]s of matching [[Sort]] in an [[Expression]].
   * @param t The base term
   * @param m A map from variables to terms.
   * @return `t[m]`, the substitution of `t` under `m`
   */
  def substituteVariables(e: Expression, m: Map[Variable, Expression]): Expression = e match {
    case v: Variable => 
      m.get(v) match {
        case Some(r) => 
          if (r.sort == v.sort) r 
          else throw new IllegalArgumentException("Sort mismatch in substitution: " + v + " -> " + r)
        case None => v
      }
    case c: Constant => c
    case Application(f, arg) => Application(substituteVariables(f, m), substituteVariables(arg, m))
    case Lambda(v, t) => 
      val newSubst = m - v
      val fv = m.values.flatMap(_.freeVariables).toSet
      if (fv.contains(v)) {
        val newBound = Variable(freshId(fv.view.map(_.id) ++ m.keys.view.map(_.id), v.id), v.sort)
        Lambda(newBound, substituteVariables(t, newSubst + (v -> newBound)))
      }
      else Lambda(v, substituteVariables(t, m - v))
  }

  def flatTypeParameters(t: Sort): List[Sort] = t match {
    case Arrow(a, b) => a :: flatTypeParameters(b)
    case _ => List()
  }

}
