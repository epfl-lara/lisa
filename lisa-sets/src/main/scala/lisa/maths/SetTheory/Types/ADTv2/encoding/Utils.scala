package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.Quantifiers.∃!
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Ordinals.Integer.ω
import lisa.maths.SetTheory.Types.TypingHelpers.*
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.{
  ConstructorArg,
  RegularArg,
  SelfRef,
  TypeApply,
  TypeExpr,
  TypeRef
}
import lisa.utils.fol.FOL.{
  Expr as FExpr,
  FormulaSetConverter,
  Ind as FInd,
  Prop as FProp,
  Variable
}
import lisa.utils.prooflib.BasicStepTactic.*
import scala.compiletime.summonFrom

object Utils {

  object Constructors {
    var tagCounter = 0
  }

  val a, b, c, d = variable[Ind]
  val f, g = variable[Ind]
  val k, n, m = variable[Ind]
  val h = variable[Ind]
  val r, s, t = variable[Ind]
  val x, y, z = variable[Ind]

  val p, p1, p2, p3, p4 = variable[Prop]

  val P, Q = variable[Ind >>: Prop]
  val schemPred = variable[Ind >>: Prop]

  val N: Expr[Ind] = ω

  object UnreachableException extends Exception("This code should not be accessed. If you see this message, please report it to the library maintainers.")

  inline def registerConstant(c: lisa.utils.fol.FOL.Constant[?]): Unit =
    summonFrom {
      case lib: lisa.utils.prooflib.Library =>
        try lib.addSymbol(c) catch { case _: Throwable => () }
      case _ => ()
    }

  def toTerm(n: Int): Expr[Ind] =
    require(n >= 0, "n must be a non-negative integer")
    if n == 0 then ∅ else successor(toTerm(n - 1))

  def pair(x: Expr[Ind], y: Expr[Ind]): Expr[Ind] =
    unorderedPair(unorderedPair(x, x), unorderedPair(x, y))

  def in(x: Expr[Ind], y: Expr[Ind]): Expr[Prop] = x ∈ y

  def subset(x: Expr[Ind], y: Expr[Ind]): Expr[Prop] = x ⊆ y

  def functional(f: Expr[Ind]): Expr[Prop] = function(f)

  def relationDomain(f: Expr[Ind]): Expr[Ind] = dom(f)

  def restrictedFunction(f: Expr[Ind], d: Expr[Ind]): Expr[Ind] = f ↾ d

  def existsOne(v: Variable[Ind], body: Expr[Prop]): Expr[Prop] = ∃!(v, body)

  def seqEq(s1: Seq[Expr[Ind]], s2: Seq[Expr[Ind]]): Expr[Prop] =
    val eqs = s1.zip(s2).map((a, b) => a === b)
    eqs.reduceOption(_ /\ _).getOrElse(True: Expr[Prop])

  extension (s1: Seq[Expr[Ind]])
    def ===(s2: Seq[Expr[Ind]]): Expr[Prop] =
      /\(s1.zip(s2).map((left, right) => left === right))

  def seqOr(s : Iterable[Expr[Prop]]): Expr[Prop] =
    s.reduceOption(_ \/ _).getOrElse(False: Expr[Prop])

  def seqAnd(s : Iterable[Expr[Prop]]): Expr[Prop] =
    s.reduceOption(_ /\ _).getOrElse(True: Expr[Prop])

  def \/(s: Iterable[Expr[Prop]]): Expr[Prop] =
    if s.isEmpty then False else s.fold(False)(_ \/ _)

  def /\(s: Iterable[Expr[Prop]]): Expr[Prop] =
    if s.isEmpty then True else s.fold(True)(_ /\ _)

  def existsSeq(vars: Seq[Variable[FInd]], formula: FExpr[FProp]): FExpr[FProp] = 
    vars.foldRight(formula)(∃(_, _))

  def forallSeq(vars: Seq[Variable[FInd]], formula: FExpr[FProp]): FExpr[FProp] = 
    vars.foldRight(formula)(∀(_, _))

  def simplify(formula: Expr[Prop]): Expr[Prop] = formula match
    case ⊥ \/ phi => simplify(phi)
    case phi \/ ⊥ => simplify(phi)
    case phi \/ psi => simplify(phi) \/ simplify(psi)
    case ⊤ /\ phi => simplify(phi)
    case phi /\ ⊤ => simplify(phi)
    case phi /\ psi => simplify(phi) /\ simplify(psi)
    case ⊤ ==> phi => simplify(phi)
    case phi ==> psi => simplify(phi) ==> simplify(psi)
    case _ => formula

  extension (arg: ConstructorArg)
    def getOrElse(adt: Expr[Ind]): Expr[Ind] = arg match
      case SelfRef => adt
      case RegularArg(tpe) => typeExprToTerm(tpe)

  def typeExprToTerm(tpe: TypeExpr): Expr[Ind] = tpe match
    case TypeRef(name) =>
      val c = Constant[Ind](name)
      registerConstant(c)
      c
    case TypeApply(name, args) =>
      val c = Constant[Ind](s"$name[${args.mkString(",")}]")
      registerConstant(c)
      c

  def unionRange(f: Expr[Ind]): Expr[Ind] = ⋃(range(f))

  def lam(v: Variable[Ind], body: Expr[Prop]): Expr[Ind >>: Prop] = λ(v, body)

  def appSeq(f: Expr[Ind])(args: Seq[Expr[Ind]]): Expr[Ind] = 
    args.foldLeft(f)(_ * _)


  def wellTyped(s: Seq[(Expr[Ind], Expr[Ind])]): Seq[Expr[Prop]] = 
    s.map(_ :: _)

  def wellTyped(s: Seq[(Expr[Ind], ConstructorArg)])(orElse: Expr[Ind]): Seq[Expr[Prop]] = 
    s.map((t, arg) => t :: arg.getOrElse(orElse))

  def wellTypedSet(s: Seq[(Expr[Ind], Expr[Ind])]): Set[Expr[Prop]] = 
    wellTyped(s).toSet

  def wellTypedFormula(s: Seq[(Expr[Ind], Expr[Ind])]): Expr[Prop] = 
    /\ (wellTyped(s))

  def wellTypedFormula(s: Seq[(Expr[Ind], ConstructorArg)])(orElse: Expr[Ind]): Expr[Prop] = 
    /\ (wellTyped(s)(orElse))



  def functionSet(A : Expr[Ind], B: Expr[Ind]): Expr[Ind] = 
    ∅ // Placeholder

  given FormulaSetConverter[(Expr[Prop], Expr[Prop])] with
    def apply(t: (Expr[Prop], Expr[Prop])): Set[FExpr[FProp]] = Set(t._1, t._2)

  given FormulaSetConverter[(Expr[Prop], Expr[Prop], Expr[Prop])] with
    def apply(t: (Expr[Prop], Expr[Prop], Expr[Prop])): Set[FExpr[FProp]] =
      Set(t._1, t._2, t._3)

  given FormulaSetConverter[(Expr[Prop], Expr[Prop], Expr[Prop], Expr[Prop])] with
    def apply(t: (Expr[Prop], Expr[Prop], Expr[Prop], Expr[Prop])): Set[FExpr[FProp]] =
      Set(t._1, t._2, t._3, t._4)
}
