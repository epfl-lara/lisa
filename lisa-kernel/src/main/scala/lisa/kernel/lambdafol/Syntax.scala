package lisa.kernel.lambdafol

private[lambdafol] trait Syntax {


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
      (taken.collect({ case Identifier(base.name, no) =>
        no
      }) ++ Iterable(base.no)).max + 1
    )
  }




  sealed trait Type {
    def ->(to: Type): Arrow = Arrow(this, to)
    val isFunctional: Boolean
    val isPredicate: Boolean
    val depth: Int 
  }
  case object Term extends Type {
    val isFunctional = true
    val isPredicate = false
    val depth = 0
  }
  case object Formula extends Type {
    val isFunctional = false
    val isPredicate = true
    val depth = 0
  }
  sealed case class Arrow(from: Type, to: Type) extends Type {
    val isFunctional = from == Term && to.isFunctional
    val isPredicate = from == Term && to.isPredicate
    val depth = 1+to.depth
  }

  def depth(t:Type): Int = t match {
    case Arrow(a, b) => 1 + depth(b)
    case _ => 0
  }
  

  def legalApplication(typ1: Type, typ2: Type): Option[Type] = {
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
    val typ: Type
    val uniqueNumber: Long = ExpressionCounters.getNewId
    val containsFormulas : Boolean
    def apply(arg: Expression): Application = Application(this, arg)
    
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

  case class Variable(id: Identifier, typ:Type) extends Expression {
    val containsFormulas = typ == Formula
    def freeVariables: Set[Variable] = Set(this)
    def constants: Set[Constant] = Set()
    def allVariables: Set[Variable] = Set(this)
  }
  case class Constant(id: Identifier, typ: Type) extends Expression {
    val containsFormulas = typ == Formula
    def freeVariables: Set[Variable] = Set()
    def constants: Set[Constant] = Set(this)
    def allVariables: Set[Variable] = Set()
  }
  case class Application(f: Expression, arg: Expression) extends Expression {
    private val legalapp = legalApplication(f.typ, arg.typ)
    require(legalapp.isDefined, s"Application of $f to $arg is not legal")
    val typ = legalapp.get
    val containsFormulas = typ == Formula || f.containsFormulas || arg.containsFormulas

    def freeVariables: Set[Variable] = f.freeVariables union arg.freeVariables
    def constants: Set[Constant] = f.constants union arg.constants
    def allVariables: Set[Variable] = f.allVariables union arg.allVariables
  }

  case class Lambda(v: Variable, body: Expression) extends Expression {
    val containsFormulas = body.containsFormulas
    val typ = (v.typ -> body.typ)

    def freeVariables: Set[Variable] = body.freeVariables - v
    def constants: Set[Constant] = body.constants
    def allVariables: Set[Variable] = body.allVariables
  }

  object Equality {
    def unapply (e: Expression): Option[(Expression, Expression)] = e match {
      case Application(Application(`equality`, arg1), arg2) => Some((arg1, arg2))
      case _ => None
    }
    def apply(arg1: Expression, arg2: Expression): Expression = equality(arg1)(arg2)
  }

  object Neg {
    def unapply (e: Expression): Option[Expression] = e match {
      case Application(`neg`, arg) => Some(arg)
      case _ => None
    }
    def apply(arg: Expression): Expression = neg(arg)
  }
  object Implies {
    def unapply (e: Expression): Option[(Expression, Expression)] = e match {
      case Application(Application(`implies`, arg1), arg2) => Some((arg1, arg2))
      case _ => None
    }
    def apply(arg1: Expression, arg2: Expression): Expression = implies(arg1)(arg2)
  }
  object Iff {
    def unapply (e: Expression): Option[(Expression, Expression)] = e match {
      case Application(Application(`iff`, arg1), arg2) => Some((arg1, arg2))
      case _ => None
    }
    def apply(arg1: Expression, arg2: Expression): Expression = iff(arg1)(arg2)
  }
  object And {
    def unapply (e: Expression): Option[(Expression, Expression)] = e match {
      case Application(Application(`and`, arg1), arg2) => Some((arg1, arg2))
      case _ => None
    }
    def apply(args: Iterable[Expression]): Expression = args.reduceLeft(and(_)(_))
  }
  object Or {
    def unapply (e: Expression): Option[(Expression, Expression)] = e match {
      case Application(Application(`or`, arg1), arg2) => Some((arg1, arg2))
      case _ => None
    }
    def apply(args: Iterable[Expression]): Expression = args.reduceLeft(and(_)(_))
  }
  object Forall {
    def unapply (e: Expression): Option[(Variable, Expression)] = e match {
      case Application(`forall`, Lambda(v, body)) => Some((v, body))
      case _ => None
    }
    def apply(v: Variable, body: Expression): Expression = forall(Lambda(v, body))
  }
  object Exists {
    def unapply (e: Expression): Option[(Variable, Expression)] = e match {
      case Application(`exists`, Lambda(v, body)) => Some((v, body))
      case _ => None
    }
    def apply(v: Variable, body: Expression): Expression = exists(Lambda(v, body))
  }
  object Epsilon {
    def unapply (e: Expression): Option[(Variable, Expression)] = e match {
      case Application(`epsilon`, Lambda(v, body)) => Some((v, body))
      case _ => None
    }
    def apply(v: Variable, body: Expression): Expression = epsilon(Lambda(v, body))
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
          if (r.typ == v.typ) r 
          else throw new IllegalArgumentException("Type mismatch in substitution: " + v + " -> " + r)
        case None => v
      }
    case c: Constant => c
    case Application(f, arg) => Application(substituteVariables(f, m), substituteVariables(arg, m))
    case Lambda(v, t) => 
      Lambda(v, substituteVariables(t, m - v))
  }

}
