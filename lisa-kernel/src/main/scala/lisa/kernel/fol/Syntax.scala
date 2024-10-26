package lisa.kernel.fol

private[fol] trait Syntax {

  type SimpleExpression

  sealed case class Identifier(val name: String, val no: Int) {
    require(no >= 0, "Variable index must be positive")
    require(Identifier.isValidIdentifier(name), "Variable name " + name + "is not valid.")
    override def toString: String = if (no == 0) name else name + Identifier.counterSeparator + no
  }

  object Identifier {
    def unapply(i: Identifier): Option[(String, Int)] = Some((i.name, i.no))
    def apply(name: String): Identifier = new Identifier(name, 0)
    def apply(name: String, no: Int): Identifier = new Identifier(name, no)

    val counterSeparator: Char = '_'
    val delimiter: Char = '`'
    val forbiddenChars: Set[Char] = ("()[]{}?,;" + delimiter + counterSeparator).toSet
    def isValidIdentifier(s: String): Boolean = s.forall(c => !forbiddenChars.contains(c) && !c.isWhitespace)
  }

  private[kernel] def freshId(taken: Iterable[Identifier], base: Identifier): Identifier = {
    new Identifier(
      base.name,
      (Iterable(base.no) ++ taken.collect({ case Identifier(base.name, no) =>
        no
      })).max + 1
    )
  }




  sealed trait Sort {
    def ->(to: Sort): Arrow = Arrow(this, to)
    val isFunctional: Boolean
    val isPredicate: Boolean
    val depth: Int 
  }
  case object Term extends Sort {
    val isFunctional = true
    val isPredicate = false
    val depth = 0
  }
  case object Formula extends Sort {
    val isFunctional = false
    val isPredicate = true
    val depth = 0
  }
  sealed case class Arrow(from: Sort, to: Sort) extends Sort {
    val isFunctional = from == Term && to.isFunctional
    val isPredicate = from == Term && to.isPredicate
    val depth = 1+to.depth
  }

  def depth(t:Sort): Int = t.depth
  

  def legalApplication(typ1: Sort, typ2: Sort): Option[Sort] = {
    typ1 match {
      case Arrow(`typ2`, to) => Some(to)
      case _ => None
    }
  }

  private object ExpressionCounters {
    var totalNumberOfExpressions: Long = 0
    def getNewId: Long = {
      totalNumberOfExpressions += 1
      totalNumberOfExpressions
    }
  }

  sealed trait Expression {
    private[fol] var polarExpr: Option[SimpleExpression] = None
    def getPolarExpr : Option[SimpleExpression] = polarExpr
    val sort: Sort
    val uniqueNumber: Long = ExpressionCounters.getNewId
    val containsFormulas : Boolean
    def apply(arg: Expression): Application = Application(this, arg)
    def unapplySeq(arg: Expression): Option[Seq[Expression]] = arg match {
      case Application(f, arg) if f == this => Some(arg :: Nil)
      case Application(f, arg) => unapplySeq(f).map(fargs => fargs :+ arg)
      case _ => None
    }
    
    /**
     * @return The list of free variables in the tree.
     */
    def freeVariables: Set[Variable]

    /**
     * @return The list of constant symbols.
     */
    def constants: Set[Constant]

    /**
     * @return The list of variables in the tree.
     */
    def allVariables: Set[Variable]
    
  }

  case class Variable(id: Identifier, sort:Sort) extends Expression {
    val containsFormulas = sort == Formula
    def freeVariables: Set[Variable] = Set(this)
    def constants: Set[Constant] = Set()
    def allVariables: Set[Variable] = Set(this)
  }
  case class Constant(id: Identifier, sort: Sort) extends Expression {
    val containsFormulas = sort == Formula
    def freeVariables: Set[Variable] = Set()
    def constants: Set[Constant] = Set(this)
    def allVariables: Set[Variable] = Set()
  }
  case class Application(f: Expression, arg: Expression) extends Expression {
    private val legalapp = legalApplication(f.sort, arg.sort)
    require(legalapp.isDefined, s"Application of $f to $arg is not legal")
    val sort = legalapp.get
    val containsFormulas = sort == Formula || f.containsFormulas || arg.containsFormulas

    def freeVariables: Set[Variable] = f.freeVariables union arg.freeVariables
    def constants: Set[Constant] = f.constants union arg.constants
    def allVariables: Set[Variable] = f.allVariables union arg.allVariables
  }

  case class Lambda(v: Variable, body: Expression) extends Expression {
    val containsFormulas = body.containsFormulas
    val sort = (v.sort -> body.sort)

    def freeVariables: Set[Variable] = body.freeVariables - v
    def constants: Set[Constant] = body.constants
    def allVariables: Set[Variable] = body.allVariables
  }
  

  val equality = Constant(Identifier("="),  Term -> (Term -> Formula))
  val top = Constant(Identifier("⊤"), Formula)
  val bot = Constant(Identifier("⊥"), Formula)
  val neg = Constant(Identifier("¬"), Formula -> Formula)
  val implies = Constant(Identifier("⇒"), Formula -> (Formula -> Formula))
  val iff = Constant(Identifier("⇔"), Formula -> (Formula -> Formula))
  val and = Constant(Identifier("∧"), Formula -> (Formula -> Formula))
  val or = Constant(Identifier("∨"), Formula -> (Formula -> Formula))
  val forall = Constant(Identifier("∀"), (Term -> Formula) -> Formula)
  val exists = Constant(Identifier("∃"), (Term -> Formula) -> Formula)
  val epsilon = Constant(Identifier("ε"), (Term -> Formula) -> Term)


  /**
   * Performs simultaneous substitution of multiple variables by multiple terms in a term.
   * @param t The base term
   * @param m A map from variables to terms.
   * @return t[m]
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

  def betaReduce(e: Expression): Expression = e match {
    case Application(f, arg) => {
      val f1 = betaReduce(f)
      val a2 = betaReduce(arg)
      f1 match {
        case Lambda(v, body) => betaReduce(substituteVariables(body, Map(v -> a2)))
        case _ => Application(f1, betaReduce(a2))
      }
    }
    case Lambda(v, Application(f, arg)) if v == arg => f
    case Lambda(v, inner) => 
      Lambda(v, betaReduce(inner))
    case _ => e
  }

}
