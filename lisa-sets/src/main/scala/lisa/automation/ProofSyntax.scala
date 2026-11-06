package lisa.automation

import scala.annotation.targetName

/** Share expression notation and external certificate constructors across proof producers. */
object ProofSyntax:
  export lisa.kernel.fol.FOL.*
  export lisa.kernel.proof.{Sequent, isSameSequent, isImplyingSequent, sequentToFormula}
  export lisa.utils.kernel.{ProofStep, CertificateStep, ProofCertificate, Subproof, LinearProof,
    Sorry, Axiom, Assume, Definition, Discharge, Restate, RestateTrue, Hypothesis, Cut,
    LeftAnd, LeftOr, LeftImplies, LeftIff, LeftNot, LeftForall, LeftExists, LeftRefl, LeftSubstEq,
    RightAnd, RightOr, RightImplies, RightIff, RightNot, RightForall, RightExists, RightEpsilon, RightRefl, RightSubstEq,
    InstSchema, Weakening}
  export lisa.utils.K.{freshId, given}

  def predicateType(arity: Int): Sort = (0 until arity).foldLeft(Prop: Sort)((result, _) => Ind -> result)
  def functionType(arity: Int): Sort = (0 until arity).foldLeft(Ind: Sort)((result, _) => Ind -> result)

  extension (s: Sort)
    def >>:(t: Sort): Sort = Arrow(s, t)

  val Equality = equality
  val And = and
  val Or = or
  val Neg = neg
  val Implies = implies
  val Iff = iff
  val RightSubstIff = RightSubstEq
  val ⊤ = top
  val ⊥ = bot

  object Forall:
    def unapply(e: Expression): Option[(Variable, Expression)] = e match
      case Application(`forall`, Lambda(v, body)) => Some((v, body))
      case _ => None

  object Exists:
    def unapply(e: Expression): Option[(Variable, Expression)] = e match
      case Application(`exists`, Lambda(v, body)) => Some((v, body))
      case _ => None

  object Epsilon:
    def unapply(e: Expression): Option[(Variable, Expression)] = e match
      case Application(`epsilon`, Lambda(v, body)) => Some((v, body))
      case _ => None

  object Multiapp:
    def unapply(e: Expression): Option[(Expression, Seq[Expression])] =
      def collect(e: Expression, args: List[Expression]): (Expression, List[Expression]) = e match
        case Application(f, arg) => collect(f, arg :: args)
        case head => (head, args)
      val (head, args) = collect(e, Nil)
      Option.when(args.nonEmpty)((head, args))

  def multiapply(f: Expression)(args: Seq[Expression]): Expression = args.foldLeft(f)(_(_))
  def multiand(args: Seq[Expression]): Expression = args.reduceLeft(and(_)(_))
  def multior(args: Seq[Expression]): Expression = args.reduceLeft(or(_)(_))
  def lambda(v: Variable, body: Expression): Lambda = Lambda(v, body)
  def lambda(vs: Seq[Variable], body: Expression): Expression = vs.foldRight(body)(Lambda(_, _))

  extension (f: forall.type)
    @targetName("forallApply") def apply(v: Variable, body: Expression): Expression = forall(Lambda(v, body))
  extension (f: exists.type)
    @targetName("existsApply") def apply(v: Variable, body: Expression): Expression = exists(Lambda(v, body))
  extension (f: epsilon.type)
    @targetName("epsilonApply") def apply(v: Variable, body: Expression): Expression = epsilon(Lambda(v, body))

  extension (e: Expression)
    def apply(args: Expression*): Expression = multiapply(e)(args)
    def unary_! : Expression = neg(e)
    infix def ==>(other: Expression): Expression = implies(e)(other)
    infix def <=>(other: Expression): Expression = iff(e)(other)
    infix def /\(other: Expression): Expression = and(e)(other)
    infix def \/(other: Expression): Expression = or(e)(other)
    infix def ===(other: Expression): Expression = equality(e)(other)
    def repr: String = e.toString

  trait ExpressionSet[-T]:
    def apply(value: T): Set[Expression]

  given ExpressionSet[Unit] = _ => Set.empty
  given ExpressionSet[EmptyTuple] = _ => Set.empty
  given ExpressionSet[Expression] = Set(_)
  given ExpressionSet[Iterable[Expression]] = _.toSet
  given [H: ExpressionSet, T <: Tuple: ExpressionSet]: ExpressionSet[H *: T] =
    tuple => summon[ExpressionSet[H]](tuple.head) ++ summon[ExpressionSet[T]](tuple.tail)

  extension [L: ExpressionSet](left: L)
    infix def |-[R: ExpressionSet](right: R): Sequent =
      Sequent(summon[ExpressionSet[L]](left), summon[ExpressionSet[R]](right))

  extension (s: Sequent)
    infix def +<<(e: Expression): Sequent = s.copy(left = s.left + e)
    infix def +>>(e: Expression): Sequent = s.copy(right = s.right + e)
    infix def -<<(e: Expression): Sequent = s.copy(left = s.left - e)
    infix def ->>(e: Expression): Sequent = s.copy(right = s.right - e)
    def repr: String = s.toString

  extension (step: CertificateStep)
    def bot: Sequent = step match
      case s: ProofStep => s.statement
      case s: Subproof => s.statement
    def premises: Seq[Int] = step match
      case s: ProofStep => s.premises.toIndexedSeq
      case s: Subproof => s.premises

  def mapStepPremises(step: CertificateStep, f: Int => Int): CertificateStep = step match
    case s: ProofStep => ProofStep.mapPremises(s, f)
    case s: Subproof => s.copy(premises = s.premises.map(f))
