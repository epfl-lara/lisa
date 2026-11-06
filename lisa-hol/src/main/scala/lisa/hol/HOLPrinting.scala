package lisa.hol

import lisa.hol.VarsAndFunctions.eqOne
import lisa.maths.SetTheory.Functions.Predef.Sabs
import lisa.maths.SetTheory.Types.TypingHelpers.{Sapp, TypeAssign}
import lisa.utils.fol.FOL.{*, given}

/** Identify logical constants without initializing their defining modules while printing. */
private[hol] object HOLLogicalSymbols:
  enum Symbol:
    case Truth, Falsehood, Bool, Equality, And, Or, Implies, Not, Forall, Exists

  import Symbol.*
  @volatile private var symbols = Map.empty[Identifier, Symbol]

  /** Record only the identifier; retain neither the constant nor its proofs. */
  def register[C <: Constant[?]](symbol: Symbol, constant: C): C = synchronized:
    require(symbols.get(constant.id).forall(_ == symbol), s"Conflicting HOL notation for ${constant.id}")
    symbols = symbols.updated(constant.id, symbol)
    constant

  def symbol(expression: Expr[?]): Option[Symbol] = expression match
    case constant: Constant[?] => symbols.get(constant.id)
    case _ => None

  object Logical:
    def unapply(expression: Expr[?]): Option[(Symbol, Seq[Expr[?]])] =
      val (head, arguments) = unfoldAllApp(expression)
      symbol(head).map(_ -> arguments)

/** Print the first-order spine of HOL formulas, leaving higher-order arguments as terms. */
object HOLPrinting:
  import HOLLogicalSymbols.{Logical, Symbol, symbol}
  import Symbol.*

  def term(expression: Expr[Ind]): String = expression match
    case variable: Variable[Ind] => variable.id.toString
    case Sapp(function, argument) => s"${term(function)}(${term(argument)})"
    case Sabs(domain, Abs(bound, body: Expr[Ind])) => s"λ(${bound.id}: ${term(domain)}. ${term(body)})"
    case _ => expression.toString

  /** Render a Boolean HOL term as a formula, not as an equality to One. */
  def boolean(expression: Expr[Ind]): String = expression match
    case Logical(Truth, Seq()) => "⊤"
    case Logical(Falsehood, Seq()) => "⊥"
    case Sapp(Sapp(Logical(And, Seq()), left), right) => s"(${boolean(left)} ∧ ${boolean(right)})"
    case Sapp(Sapp(Logical(Or, Seq()), left), right) => s"(${boolean(left)} ∨ ${boolean(right)})"
    case Sapp(Sapp(Logical(Implies, Seq()), left), right) => s"(${boolean(left)} ⇒ ${boolean(right)})"
    case Sapp(Logical(Not, Seq()), body) => s"¬(${boolean(body)})"
    case Sapp(Sapp(Logical(Equality, Seq(domain)), left), right) =>
      if symbol(domain).contains(Bool) then s"(${boolean(left)} ⇔ ${boolean(right)})"
      else s"(${term(left)} = ${term(right)})"
    case Sapp(Logical(quantifier @ (Forall | Exists), Seq(domain: Expr[Ind] @unchecked)), predicate) =>
      val quantifierName = if quantifier == Forall then "∀" else "∃"
      predicate match
        case Sabs(_, Abs(bound, body: Expr[Ind])) =>
          s"$quantifierName(${bound.id}: ${term(domain)}, ${boolean(body)})"
        case _ =>
          val bound = Variable.fresh[Ind](Set(domain, predicate), "x")
          val application = lisa.maths.SetTheory.Functions.Predef.app(predicate)(bound)
          s"$quantifierName(${bound.id}: ${term(domain)}, ${boolean(application)})"
    case _ => term(expression)

  /** Render native connectives and embedded HOL formulas on either side of a sequent. */
  def formula(expression: Expr[Prop]): String = expression match
    case eqOne(body) => boolean(body)
    case left /\ right => s"(${formula(left)} ∧ ${formula(right)})"
    case left \/ right => s"(${formula(left)} ∨ ${formula(right)})"
    case left ==> right => s"(${formula(left)} ⇒ ${formula(right)})"
    case left <=> right => s"(${formula(left)} ⇔ ${formula(right)})"
    case !(body) => s"¬(${formula(body)})"
    case ∀(bound, body) => s"∀(${bound.id}, ${formula(body)})"
    case ∃(bound, body) => s"∃(${bound.id}, ${formula(body)})"
    case TypeAssign(element, domain) => s"${term(element)} ∈ ${term(domain)}"
    case left === right => s"${term(left)} = ${term(right)}"
    case _ => expression.toString

  /** Keep typing and non-emptiness premises visible alongside logical hypotheses. */
  def sequent(statement: Sequent): String =
    def side(formulas: Set[Expr[Prop]]): String =
      val rendered = formulas.iterator.map(formula).toVector
      if rendered.size <= 1 then rendered.mkString else rendered.mkString("( ", ", ", " )")
    s"${side(statement.left)} ⊢ ${side(statement.right)}"

  /** Attach HOL notation without changing the formulas or their kernel representation. */
  private[lisa] def displayed(statement: Sequent): Sequent =
    new Sequent(statement.left, statement.right):
      override def toString: String = sequent(this)
