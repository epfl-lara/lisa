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
  private[kernel] type SimpleExpression

  /**
   * An identifier for a variable or constant symbol.
   *
   * An identifier must not contain one of the following characters: {{{()[]{}?,;$`}}} and must not contain whitespace.
   *
   * Idiomatic representation is as follows:
   * - `Identifier("x", 0)` ~ "x"
   * - `Identifier("x", 1)` ~ "x$1"
   * - `Identifier("myvariable", 227)` ~ "myvariable_227"
   *
   * @param name The name of the identifier
   * @param no The index of the identifier. Used to easily compute fresh names.
   */
  sealed case class Identifier(val name: String, val no: Int) {
    require(no >= 0, "Variable index must be non-negative")
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

    val counterSeparator: Char = '$'
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

    private enum CompositeMode:
      case BoundedTrees, IdsOnly, BoundedTreesAndIds

    private val compositeMode =
      sys.props.get("lisa.hashcons.mode").fold(CompositeMode.BoundedTreesAndIds) {
        case "bounded" => CompositeMode.BoundedTrees
        case "ids" => CompositeMode.IdsOnly
        case "hybrid" => CompositeMode.BoundedTreesAndIds
        case mode => throw new IllegalArgumentException(s"Unknown hashcons mode '$mode'. Expected bounded, ids, or hybrid.")
      }

    val enabled: Boolean =
      !sys.props.get("lisa.hashcons").contains("false") &&
      !sys.props.get("lisa.hashcons").contains("0") &&
      !sys.env.get("LISA_HASHCONS").contains("false") &&
      !sys.env.get("LISA_HASHCONS").contains("0")

    val usesCanonicalIds: Boolean =
      enabled && compositeMode != CompositeMode.BoundedTrees

    private case class VariableKey(id: Identifier, sort: Sort)
    private case class ConstantKey(id: Identifier, sort: Sort)

    private val variables = mutable.Map.empty[VariableKey, Variable]
    private val constants = mutable.Map.empty[ConstantKey, Constant]
    private val applicationIds = mutable.LongMap.empty[mutable.LongMap[Long]]
    private val lambdaIds = mutable.LongMap.empty[mutable.LongMap[Long]]

    private final class CompositeGeneration:
      val applications = mutable.LongMap.empty[mutable.LongMap[Application]]
      val lambdas = mutable.LongMap.empty[mutable.LongMap[Lambda]]
      var size = 0

      def clear(): Unit =
        applications.clear()
        lambdas.clear()
        size = 0

    // Retain one full generation while filling the other. This approximates
    // recent-use caching without per-entry bookkeeping or mutation on hits.
    private val maxCompositeEntries =
      sys.props.get("lisa.hashcons.max").flatMap(_.toIntOption).filter(_ > 0).getOrElse(1 << 20)
    private val compositeGenerationCount =
      sys.props.get("lisa.hashcons.generations").fold(2) {
        case "1" => 1
        case "2" => 2
        case count => throw new IllegalArgumentException(s"Unknown hashcons generation count '$count'. Expected 1 or 2.")
      }
    private val compositeGenerations = Array.fill(compositeGenerationCount)(new CompositeGeneration)
    private var activeGeneration = 0

    private def generationForInsertion(): CompositeGeneration =
      val active = compositeGenerations(activeGeneration)
      if active.size < maxCompositeEntries then active
      else
        activeGeneration = (activeGeneration + 1) % compositeGenerationCount
        val next = compositeGenerations(activeGeneration)
        next.clear()
        next

    private def findApplication(f: Expression, arg: Expression): Option[Application] =
      val active = compositeGenerations(activeGeneration).applications.get(f.uniqueNumber).flatMap(_.get(arg.uniqueNumber))
      if active.nonEmpty || compositeGenerationCount == 1 then active
      else compositeGenerations(1 - activeGeneration).applications.get(f.uniqueNumber).flatMap(_.get(arg.uniqueNumber))

    private def findLambda(v: Variable, body: Expression): Option[Lambda] =
      val active = compositeGenerations(activeGeneration).lambdas.get(v.uniqueNumber).flatMap(_.get(body.uniqueNumber))
      if active.nonEmpty || compositeGenerationCount == 1 then active
      else compositeGenerations(1 - activeGeneration).lambdas.get(v.uniqueNumber).flatMap(_.get(body.uniqueNumber))

    private def applicationId(f: Expression, arg: Expression): Long =
      applicationIds
        .getOrElseUpdate(f.uniqueNumber, mutable.LongMap.empty)
        .getOrElseUpdate(arg.uniqueNumber, ExpressionCounters.getNewId)

    private def lambdaId(v: Variable, body: Expression): Long =
      lambdaIds
        .getOrElseUpdate(v.uniqueNumber, mutable.LongMap.empty)
        .getOrElseUpdate(body.uniqueNumber, ExpressionCounters.getNewId)

    private def cacheApplication(f: Expression, arg: Expression, id: => Long): Application =
      findApplication(f, arg) match
        case Some(application) => application
        case None =>
          val generation = generationForInsertion()
          val application = new Application(f, arg)(id)
          generation.applications.getOrElseUpdate(f.uniqueNumber, mutable.LongMap.empty)(arg.uniqueNumber) = application
          generation.size += 1
          application

    private def cacheLambda(v: Variable, body: Expression, id: => Long): Lambda =
      findLambda(v, body) match
        case Some(lambda) => lambda
        case None =>
          val generation = generationForInsertion()
          val lambda = new Lambda(v, body)(id)
          generation.lambdas.getOrElseUpdate(v.uniqueNumber, mutable.LongMap.empty)(body.uniqueNumber) = lambda
          generation.size += 1
          lambda

    def variable(id: Identifier, sort: Sort): Variable =
      if enabled then variables.getOrElseUpdate(VariableKey(id, sort), new Variable(id, sort))
      else new Variable(id, sort)

    def constant(id: Identifier, sort: Sort): Constant =
      if enabled then constants.getOrElseUpdate(ConstantKey(id, sort), new Constant(id, sort))
      else new Constant(id, sort)

    def application(f: Expression, arg: Expression): Application =
      if !enabled then new Application(f, arg)(ExpressionCounters.getNewId)
      else compositeMode match
        case CompositeMode.BoundedTrees => cacheApplication(f, arg, ExpressionCounters.getNewId)
        case CompositeMode.IdsOnly => new Application(f, arg)(applicationId(f, arg))
        case CompositeMode.BoundedTreesAndIds => cacheApplication(f, arg, applicationId(f, arg))

    def lambda(v: Variable, body: Expression): Lambda =
      if !enabled then new Lambda(v, body)(ExpressionCounters.getNewId)
      else compositeMode match
        case CompositeMode.BoundedTrees => cacheLambda(v, body, ExpressionCounters.getNewId)
        case CompositeMode.IdsOnly => new Lambda(v, body)(lambdaId(v, body))
        case CompositeMode.BoundedTreesAndIds => cacheLambda(v, body, lambdaId(v, body))
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
  sealed trait Expression(val uniqueNumber: Long) {

    // Canonical IDs make hashing constant-time. Equality still checks structure
    // when IDs differ, so explicit comparisons do not depend on canonicalization.
    protected final def expressionHashCode: Int =
      if ExpressionCache.usesCanonicalIds then java.lang.Long.hashCode(uniqueNumber)
      else scala.util.hashing.MurmurHash3.productHash(this.asInstanceOf[Product])

    /**
     * Cached normal form of the expression by [[OLEquivalenceChecker]].
     */
    private[fol] var polarExpr: Option[SimpleExpression] = None

    /**
     * Sort of the expression.
     */
    val sort: Sort

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

    /** Test beta-eta normality from the syntax and cached child flags. */
    val isBetaNormal: Boolean = this match {
      case Application(_: Lambda, _) => false
      case Application(f, arg) => f.isBetaNormal && arg.isBetaNormal
      case Lambda(v, Application(f, arg)) if v == arg && !f.freeVariables.contains(v) => false
      case Lambda(_, inner) => inner.isBetaNormal
      case _ => true
    }

    /**
     * The beta-eta normal form of the expression. Retain this instance when already normal.
     */
    val betaNormalForm: Expression = this match {
      case Application(f, arg) => {
        val f1 = f.betaNormalForm
        val a2 = arg.betaNormalForm
        f1 match {
          case Lambda(v, body) => {
            substituteVariables(body, Map(v -> a2)).betaNormalForm
          }
          case _ if f.isBetaNormal && arg.isBetaNormal => this
          case _ => Application(f1, a2)
        }
      }
      case Lambda(v, Application(f, arg)) if v == arg && !f.freeVariables.contains(v) => f.betaNormalForm
      case Lambda(v, inner) if inner.isBetaNormal => this
      case Lambda(v, inner) => Lambda(v, inner.betaNormalForm)
      case _ => this
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
  case class Variable private[fol] (id: Identifier, sort: Sort) extends Expression(ExpressionCounters.getNewId) {
    override def equals(other: Any): Boolean = other match
      case that: Variable =>
        (this eq that) || uniqueNumber == that.uniqueNumber || (id == that.id && sort == that.sort)
      case _ => false
    override def hashCode(): Int = expressionHashCode

    val containsFormulas = sort == Prop
    val freeVariables: Set[Variable] = Set(this)
    val constants: Set[Constant] = Set.empty
    val allVariables: Set[Variable] = freeVariables
  }

  object Variable {
    def apply(id: Identifier, sort: Sort): Variable = ExpressionCache.variable(id, sort)
  }

  /**
   * A constant symbol, which is a special case of [[Expression]].
   *
   * Constants generalize function and predicate symbols of any arity in strict first-order logic.
   */
  case class Constant private[fol] (id: Identifier, sort: Sort) extends Expression(ExpressionCounters.getNewId) {
    override def equals(other: Any): Boolean = other match
      case that: Constant =>
        (this eq that) || uniqueNumber == that.uniqueNumber || (id == that.id && sort == that.sort)
      case _ => false
    override def hashCode(): Int = expressionHashCode

    val containsFormulas = sort == Prop
    val freeVariables: Set[Variable] = Set.empty
    val constants: Set[Constant] = Set(this)
    val allVariables: Set[Variable] = Set.empty
  }

  object Constant {
    def apply(id: Identifier, sort: Sort): Constant = ExpressionCache.constant(id, sort)
  }

  /**
   * An application of an expression to an argument, which is a special case of [[Expression]].
   * `f.sort` must be of the form `arg.sort -> _`.
   */
  case class Application private[fol] (f: Expression, arg: Expression)(assignedId: Long) extends Expression(assignedId) {
    override def equals(other: Any): Boolean = other match
      case that: Application =>
        (this eq that) || uniqueNumber == that.uniqueNumber || (f == that.f && arg == that.arg)
      case _ => false
    override def hashCode(): Int = expressionHashCode

    val sort = f.sort match
      case Arrow(from, to) if from == arg.sort => to
      case _ => throw new IllegalArgumentException(s"Application of $f to $arg is not legal")
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
  case class Lambda private[fol] (v: Variable, body: Expression)(assignedId: Long) extends Expression(assignedId) {
    override def equals(other: Any): Boolean = other match
      case that: Lambda =>
        (this eq that) || uniqueNumber == that.uniqueNumber || (v == that.v && body == that.body)
      case _ => false
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
        val taken = fv.view.map(_.id) ++ t.freeVariables.view.map(_.id) ++ m.keys.view.map(_.id)
        val newBound = Variable(freshId(taken, v.id), v.sort)
        Lambda(newBound, substituteVariables(t, newSubst + (v -> newBound)))
      } else Lambda(v, substituteVariables(t, m - v))
  }

  def flatTypeParameters(t: Sort): List[Sort] = t match {
    case Arrow(a, b) => a :: flatTypeParameters(b)
    case _ => List()
  }

}
