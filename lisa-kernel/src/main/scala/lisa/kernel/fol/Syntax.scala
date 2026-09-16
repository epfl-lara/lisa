package lisa.kernel.fol


/**
 * Defines the syntax of statements Lisa's kernel
 *
 * This syntax is a (conservative) extension of first-order logic with higher order expressions.
 * An expression in Lisa is a term of the simply typed lambda calculus with base types (called [[Sort]]) [[Ind]] and [[Prop]].
 */
private[fol] trait Syntax {

  /**
   * An abstract type, later instantiated  in [[OLEquivalenceChecker]] to be the type of expressions in normal form modulo OL.
   */
  type SimpleExpression

  /**
   * An identifier for a variable or constant symbol.
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
    // require(Identifier.isValidIdentifier(name), "Variable name " + name + " is not valid.")
    override def toString: String = if (no == 0) name else name + Identifier.counterSeparator + no
  }

  /**
   * Factory for [[Identifier]] instances.
   */
  object Identifier {

    /**
     * Extractor for identifiers.
     */
    def unapply(i: Identifier): Option[(String, Int)] = Some((i.name, i.no))

    /**
     * Creates a new identifier with the given name and index = 0.
     */
    def apply(name: String): Identifier = new Identifier(name, 0)

    /**
     * Creates a new identifier with the given name and index.
     */
    def apply(name: String, no: Int): Identifier = new Identifier(name, no)

    val counterSeparator: Char = '_'
    val delimiter: Char = '`'
    val forbiddenChars: Set[Char] = ("()[]{}?,;" + delimiter + counterSeparator).toSet

    /**
     * Checks if a string is a valid identifier.
     */
    def isValidIdentifier(s: String): Boolean = s.forall(c => !forbiddenChars.contains(c) && !c.isWhitespace)
  }

  /**
   * Creates a fresh identifier based on a base identifier and a set of taken identifiers.
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
   * There are two sorts: `Ind` and `Prop`.
   */
  sealed trait Sort {

    /**
     * shortcut for `Arrow(this, to)`
     */
    def ->(to: Sort): Arrow = Arrow(this, to)

    /**
     * @return true if the sort is of the form `Ind -> ... -> Ind -> Ind`
     */
    val isFunctional: Boolean

    /**
     * @return true if the sort is of the form `Ind -> ... -> Ind -> Prop`
     */
    val isPredicate: Boolean

    /**
     * @return the number of arguments of the type.
     *
     * For example, `Ind` has depth 0, `Prop -> Ind` has depth 1, `Ind -> (Prop -> Ind) -> Ind` has depth 2, etc.
     */
    val depth: Int
  }

  /**
   * The sort of terms in the simply typed lambda calculus.
   * Expressions of this type correspond to terms of first-order logic.
   * Semantically they are interpreted as elements of the universe, i.e. sets in ZFC.
   */
  case object Ind extends Sort {
    val isFunctional = true
    val isPredicate = false
    val depth = 0
  }

  /**
   * The sort of formulas in the simply typed lambda calculus.
   * Expressions of this type correspond to formulas of first-order logic.
   */
  case object Prop extends Sort {
    val isFunctional = false
    val isPredicate = true
    val depth = 0
  }

  /**
   * An arrow sort, representing a function type in the simply typed lambda calculus.
   * The arrow sort is of the form `from -> to`, where `from` and `to` are sorts.
   *
   * Expressions of type `Ind -> ... -> Ind -> Ind` correspond to function symbols of first-order logic.
   * Expressions of type `Ind -> ... -> Ind -> Prop` correspond to predicate symbols of first-order logic.
   * Expressions of type `(Ind -> Prop) -> Prop` correspond to quantifiers (∀ and ∃) in first-order logic.
   */
  sealed case class Arrow(from: Sort, to: Sort) extends Sort {
    val isFunctional = from == Ind && to.isFunctional
    val isPredicate = from == Ind && to.isPredicate
    val depth = 1 + to.depth
  }

  /**
   * If `typ1` is of the form `typ2 -> to`, returns `Some(to)`, otherwise returns `None`.
   *
   * This means, it check that an application of a term of type `typ1` to a term of type `typ2` is legal, and if so returns the resulting type.
   */
  def legalApplication(typ1: Sort, typ2: Sort): Option[Sort] = {
    typ1 match {
      case Arrow(`typ2`, to) => Some(to)
      case _ => None
    }
  }

  /**
   * Store global counters used for distinguishing expressions.
   * Useful for efficient reference-based equality checking.
   */
  private object ExpressionCounters {
    var totalNumberOfExpressions: Long = 0
    def getNewId: Long = {
      totalNumberOfExpressions += 1
      totalNumberOfExpressions
    }
  }

  private object ExpressionCache {
    import scala.collection.mutable

    private val mode = sys.props.getOrElse("lisa.hashcons.mode", "hybrid")
    require(Set("bounded", "ids", "hybrid").contains(mode), s"Unknown hashcons mode '$mode'")
    val enabled: Boolean =
      !sys.props.get("lisa.hashcons").exists(Set("false", "0")) &&
      !sys.env.get("LISA_HASHCONS").exists(Set("false", "0"))
    val usesCanonicalIds: Boolean = enabled && mode != "bounded"

    private case class VariableKey(id: Identifier, sort: Sort)
    private case class ConstantKey(id: Identifier, sort: Sort)
    private val variables = mutable.Map.empty[VariableKey, Variable]
    private val constants = mutable.Map.empty[ConstantKey, Constant]
    private val applicationIds = mutable.LongMap.empty[mutable.LongMap[Long]]
    private val lambdaIds = mutable.LongMap.empty[mutable.LongMap[Long]]

    private final class Generation {
      val applications = mutable.LongMap.empty[mutable.LongMap[Application]]
      val lambdas = mutable.LongMap.empty[mutable.LongMap[Lambda]]
      var size = 0
      def clear(): Unit = {
        applications.clear()
        lambdas.clear()
        size = 0
      }
    }

    private val maxEntries = sys.props.get("lisa.hashcons.max").flatMap(_.toIntOption).filter(_ > 0).getOrElse(1 << 20)
    private val generationCount = sys.props.getOrElse("lisa.hashcons.generations", "2").toInt
    require(generationCount == 1 || generationCount == 2, "Expected one or two hashcons generations")
    private val generations = Array.fill(generationCount)(new Generation)
    private var activeGeneration = 0

    // Keep the previous generation alive while filling the current one.
    private def insertionGeneration(): Generation = {
      if (generations(activeGeneration).size >= maxEntries) {
        activeGeneration = (activeGeneration + 1) % generationCount
        generations(activeGeneration).clear()
      }
      generations(activeGeneration)
    }

    def applicationId(f: Expression, arg: Expression): Long =
      if (!usesCanonicalIds) ExpressionCounters.getNewId
      else applicationIds.getOrElseUpdate(f.uniqueNumber, mutable.LongMap.empty)
        .getOrElseUpdate(arg.uniqueNumber, ExpressionCounters.getNewId)

    def lambdaId(v: Variable, body: Expression): Long =
      if (!usesCanonicalIds) ExpressionCounters.getNewId
      else lambdaIds.getOrElseUpdate(v.uniqueNumber, mutable.LongMap.empty)
        .getOrElseUpdate(body.uniqueNumber, ExpressionCounters.getNewId)

    private def cachedApplication(f: Expression, arg: Expression): Application = {
      def lookup(generation: Int) = generations(generation).applications.get(f.uniqueNumber).flatMap(_.get(arg.uniqueNumber))
      lookup(activeGeneration).orElse(if (generationCount == 2) lookup(1 - activeGeneration) else None).getOrElse {
        val generation = insertionGeneration()
        val result = new Application(f, arg)
        generation.applications.getOrElseUpdate(f.uniqueNumber, mutable.LongMap.empty)(arg.uniqueNumber) = result
        generation.size += 1
        result
      }
    }

    private def cachedLambda(v: Variable, body: Expression): Lambda = {
      def lookup(generation: Int) = generations(generation).lambdas.get(v.uniqueNumber).flatMap(_.get(body.uniqueNumber))
      lookup(activeGeneration).orElse(if (generationCount == 2) lookup(1 - activeGeneration) else None).getOrElse {
        val generation = insertionGeneration()
        val result = new Lambda(v, body)
        generation.lambdas.getOrElseUpdate(v.uniqueNumber, mutable.LongMap.empty)(body.uniqueNumber) = result
        generation.size += 1
        result
      }
    }

    def variable(id: Identifier, sort: Sort): Variable =
      if (enabled) variables.getOrElseUpdate(VariableKey(id, sort), new Variable(id, sort))
      else new Variable(id, sort)

    def constant(id: Identifier, sort: Sort): Constant =
      if (enabled) constants.getOrElseUpdate(ConstantKey(id, sort), new Constant(id, sort))
      else new Constant(id, sort)

    def application(f: Expression, arg: Expression): Application =
      if (!enabled) new Application(f, arg)
      else mode match {
        case "bounded" => cachedApplication(f, arg)
        case "ids" => new Application(f, arg)
        case _ => cachedApplication(f, arg)
      }

    def lambda(v: Variable, body: Expression): Lambda =
      if (!enabled) new Lambda(v, body)
      else mode match {
        case "bounded" => cachedLambda(v, body)
        case "ids" => new Lambda(v, body)
        case _ => cachedLambda(v, body)
      }
  }

  /**
   * Expressions are lambda-terms in the simply typed lambda calculus with base types `Ind` and `Prop`.
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

    /**
     * Cached normal form of the expression by [[OLEquivalenceChecker]].
     */
    private[fol] var polarExpr: Option[SimpleExpression] = None

    /**
     * Cached normal form of the expression by [[OLEquivalenceChecker]].
     */
    def getPolarExpr: Option[SimpleExpression] = polarExpr

    /**
     * Sort of the expression.
     */
    val sort: Sort

    /**
     * Unique number of the expression assigned by [[ExpressionCounters]]. Used for efficient reference equality.
     */
    def uniqueNumber: Long

    private lazy val structuralHashCode: Int = scala.util.hashing.MurmurHash3.productHash(this.asInstanceOf[Product])

    protected final def expressionHashCode: Int =
      if (ExpressionCache.usesCanonicalIds) java.lang.Long.hashCode(uniqueNumber)
      else structuralHashCode

    /**
     * True if the expression contains subexpressions of type `Prop`.
     */
    val containsFormulas: Boolean

    /**
     * Creates an application of this expression to an argument.
     */
    def apply(arg: Expression): Application = Application(this, arg)

    /**
     * Extractor for the arguments of the expression.
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

    /**
     * The beta-eta normal form of the expression.
     * Which algorithm is used is controlled by [[BetaNormMode.useNbe]].
     */
    lazy val (betaNormalForm: Expression, isBetaNormal: Boolean) = this match {
      case Application(f, arg) =>
        f.betaNormalForm match {
          case Lambda(x, body) => (substituteVariables(body, Map(x -> arg)).betaNormalForm, false)
          case nf              => 
            if (f.isBetaNormal && arg.isBetaNormal) (this, true)
            else (Application(nf, arg.betaNormalForm), false)
        }
      case Lambda(x, body) =>
        val nb = body.betaNormalForm
        nb match {
          case Application(g, y: Variable) if y == x && !g.freeVariables.contains(x) => (g, false)
          case _ if body.isBetaNormal => (this, true)
          case _                                                                     => (Lambda(x, nb), false)
        }
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
  case class Variable private[fol] (id: Identifier, sort: Sort) extends Expression {
    def copy(id: Identifier = this.id, sort: Sort = this.sort): Variable = Variable(id, sort)
    val uniqueNumber: Long = ExpressionCounters.getNewId
    override def equals(other: Any): Boolean = other match {
      case that: Variable => (this eq that) || uniqueNumber == that.uniqueNumber || (id == that.id && sort == that.sort)
      case _ => false
    }
    override def hashCode(): Int = expressionHashCode

    val containsFormulas = sort == Prop
    lazy val freeVariables: Set[Variable] = Set(this)
    lazy val constants: Set[Constant] = Set()
    lazy val allVariables: Set[Variable] = Set(this)
  }

  object Variable {
    def apply(id: Identifier, sort: Sort): Variable = ExpressionCache.variable(id, sort)
  }

  /**
   * A constant symbol, which is a special case of [[Expression]].
   *
   * Constants generalize function and predicate symbols of any arity in strict first-order logic.
   */
  case class Constant private[fol] (id: Identifier, sort: Sort) extends Expression {
    def copy(id: Identifier = this.id, sort: Sort = this.sort): Constant = Constant(id, sort)
    val uniqueNumber: Long = ExpressionCounters.getNewId
    override def equals(other: Any): Boolean = other match {
      case that: Constant => (this eq that) || uniqueNumber == that.uniqueNumber || (id == that.id && sort == that.sort)
      case _ => false
    }
    override def hashCode(): Int = expressionHashCode

    val containsFormulas = sort == Prop
    lazy val freeVariables: Set[Variable] = Set()
    lazy val constants: Set[Constant] = Set(this)
    lazy val allVariables: Set[Variable] = Set()
  }

  object Constant {
    def apply(id: Identifier, sort: Sort): Constant = ExpressionCache.constant(id, sort)
  }

  /**
   * An application of an expression to an argument, which is a special case of [[Expression]].
   * `f.sort` must be of the form `arg.sort -> _`.
   */
  case class Application private[fol] (f: Expression, arg: Expression) extends Expression {
    val uniqueNumber: Long = ExpressionCache.applicationId(f, arg)
    def copy(f: Expression = this.f, arg: Expression = this.arg): Application = Application(f, arg)
    override def equals(other: Any): Boolean = other match {
      case that: Application => (this eq that) || uniqueNumber == that.uniqueNumber || (f == that.f && arg == that.arg)
      case _ => false
    }
    override def hashCode(): Int = expressionHashCode

    private val legalapp = legalApplication(f.sort, arg.sort)
    require(legalapp.isDefined, s"Application of $f to $arg is not legal")
    val sort = legalapp.get
    val containsFormulas = sort == Prop || f.containsFormulas || arg.containsFormulas
    lazy val freeVariables: Set[Variable] = f.freeVariables union arg.freeVariables
    lazy val constants: Set[Constant] = f.constants union arg.constants
    lazy val allVariables: Set[Variable] = f.allVariables union arg.allVariables
  }

  object Application {
    def apply(f: Expression, arg: Expression): Application = ExpressionCache.application(f, arg)
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
  case class Lambda private[fol] (v: Variable, body: Expression) extends Expression {
    val uniqueNumber: Long = ExpressionCache.lambdaId(v, body)
    def copy(v: Variable = this.v, body: Expression = this.body): Lambda = Lambda(v, body)
    override def equals(other: Any): Boolean = other match {
      case that: Lambda => (this eq that) || uniqueNumber == that.uniqueNumber || (v == that.v && body == that.body)
      case _ => false
    }
    override def hashCode(): Int = expressionHashCode

    val containsFormulas = body.containsFormulas
    val sort = (v.sort -> body.sort)

    lazy val freeVariables: Set[Variable] = body.freeVariables - v
    lazy val constants: Set[Constant] = body.constants
    lazy val allVariables: Set[Variable] = body.allVariables
  }

  object Lambda {
    def apply(v: Variable, body: Expression): Lambda = ExpressionCache.lambda(v, body)
  }

  /**
   * The constant symbol for the equality predicate.
   *
   * Type: `Ind -> (Ind -> Prop)`.
   *
   * Symbol: `=`
   */
  val equality = Constant(Identifier("="), Ind -> (Ind -> Prop))

  /**
   * The constant symbol for the true formula. <br>
   * Type: `Prop`.
   *
   * Symbol: `⊤`
   */
  val top = Constant(Identifier("⊤"), Prop)

  /**
   * The constant symbol for the false formula.
   *
   * Type: `Prop`.
   *
   * Symbol: `⊥`
   */
  val bot = Constant(Identifier("⊥"), Prop)

  /**
   * The constant symbol for the negation connector.
   *
   * Type: `Prop -> Prop`.
   *
   * Symbol: `¬`
   */
  val neg = Constant(Identifier("¬"), Prop -> Prop)

  /**
   * The constant symbol for the implication connector.
   *
   * Type: `Prop -> (Prop -> Prop)`.
   *
   * Symbol: `⇒`
   */
  val implies = Constant(Identifier("⇒"), Prop -> (Prop -> Prop))

  /**
   * The constant symbol for the equivalence connector.
   *
   * Type: `Prop -> (Prop -> Prop)`.
   *
   * Symbol: `⇔`
   */

  val iff = Constant(Identifier("⇔"), Prop -> (Prop -> Prop))

  /**
   * The constant symbol for the conjunction connector.
   *
   * Type: `Prop -> (Prop -> Prop)`.
   *
   * Symbol: `∧`
   */
  val and = Constant(Identifier("∧"), Prop -> (Prop -> Prop))

  /**
   * The constant symbol for the disjunction connector.
   *
   * Type: `Prop -> (Prop -> Prop)`.
   *
   * Symbol: `∨`
   */
  val or = Constant(Identifier("∨"), Prop -> (Prop -> Prop))

  /**
   * The constant symbol for the universal quantifier.
   *
   * Type: `(Ind -> Prop) -> Prop`.
   *
   * Symbol: `∀`
   *
   * Usage: `forall(Lambda(x, P(x)))` corresponds to the formula in strict first-order logic ∀x.P(x).
   */
  val forall = Constant(Identifier("∀"), (Ind -> Prop) -> Prop)

  /**
   * The constant symbol for the existential quantifier.
   *
   * Type: `(Ind -> Prop) -> Prop`.
   *
   * Symbol: `∃`
   *
   * Usage: `exists(Lambda(x, P(x)))` corresponds to the formula in strict first-order logic ∃x.P(x).
   */
  val exists = Constant(Identifier("∃"), (Ind -> Prop) -> Prop)

  /**
   * The constant symbol for the epsilon quantifier.
   *
   * Type: `(Ind -> Prop) -> Ind`.
   *
   * Symbol: `ε`
   *
   * Usage: `epsilon(Lambda(x, P(x)))` corresponds to the term in strict first-order logic εx.P(x).
   *
   * Denotes Hilbert's epsilon operator. `epsilon(Lambda(x, P(x)))` is some element x such that P(x) holds, or an unknown element if no such x exists.
   */
  val epsilon = Constant(Identifier("ε"), (Ind -> Prop) -> Ind)

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
        val taken = fv.view.map(_.id) ++ m.keys.view.map(_.id) ++ t.freeVariables.view.map(_.id)
        val newBound = Variable(freshId(taken, v.id), v.sort)
        Lambda(newBound, substituteVariables(t, newSubst + (v -> newBound)))
      } else Lambda(v, substituteVariables(t, m - v))
  }

  def flatTypeParameters(t: Sort): List[Sort] = t match {
    case Arrow(a, b) => a :: flatTypeParameters(b)
    case _ => List()
  }

}
