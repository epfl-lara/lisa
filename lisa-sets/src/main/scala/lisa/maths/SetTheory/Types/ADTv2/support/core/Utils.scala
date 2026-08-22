package lisa.maths.SetTheory.Types.ADTv2.support.core

import lisa.maths.SetTheory.Base.Pair
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST._
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.fol.FOL.Variable
import lisa.utils.fol.FOL.{Expr => FExpr}
import lisa.utils.fol.FOL.{Ind => FInd}
import lisa.utils.fol.FOL.{Prop => FProp}

import scala.compiletime.summonFrom

private object MyVariables {

  // Variables
  val a, b, c, d = variable[Ind]
  val f, g = variable[Ind]
  val k, n, m = variable[Ind]
  val r, s, t = variable[Ind]
  val x, y, z = variable[Ind]
  val α, β = variable[Ind]

  var h: Variable[Ind] = variable[Ind]

  val A, B = variable[Ind]

  // Propositions
  val p, p1, p2, p3, p4 = variable[Prop]
  val q1, q2 = variable[Prop]

  // Predicates
  val P, Q = variable[Ind >>: Prop]
  val schemPred = variable[Ind >>: Prop]
  val P2 = variable[Ind >>: Ind >>: Prop]

  // Constants
  val N: Expr[Ind] = lisa.maths.SetTheory.Ordinals.Integer.ω

}

object Utils {

  export MyVariables.*

  // Variables used

  // Some useful constants and functions
  object UnreachableException
      extends Exception(
        "This code should not be accessed. If you see this message, please report it to the library maintainers."
      )

  inline def registerConstant(c: lisa.utils.fol.FOL.Constant[?]): Unit = summonFrom {
    case lib: lisa.utils.prooflib.Library =>
      try lib.addSymbol(c)
      catch { case _: Throwable => () }
    case _ => ()
  }

  // Some useful shorthands for readability

  // ∀ ∃ ∈ ⊆ λ
  // ADTv2/**/*.scala

  def pair(x: Expr[Ind], y: Expr[Ind]): Expr[Ind] =
    Pair.pair(x)(y)

  // Syntactic sugar for sequences

  def appSeq(f: Expr[Ind])(args: Seq[Expr[Ind]]): Expr[Ind] =
    Option(args).getOrElse(Seq.empty).foldLeft(f)(_ * _)

  def renderAppliedSymbol(name: String, typeArgCount: Int, args: Seq[Expr[?]]): String =
    val (typeArgs, valueArgs) = args.splitAt(typeArgCount)
    val head =
      if typeArgCount == 0 then name
      else s"$name[${typeArgs.mkString(",")}]"
    valueArgs.foldLeft(head)((acc, arg) => s"$acc($arg)")

  def seqOr(s: Iterable[Expr[Prop]]): Expr[Prop] = s
    .reduceOption(_ \/ _)
    .getOrElse(False: Expr[Prop])

  def seqAnd(s: Iterable[Expr[Prop]]): Expr[Prop] = s
    .reduceOption(_ /\ _)
    .getOrElse(True: Expr[Prop])

  def seqEq(s1: Seq[Expr[Ind]], s2: Seq[Expr[Ind]]): Expr[Prop] =
    val eqs = s1.zip(s2).map((a, b) => a === b)
    eqs.reduceOption(_ /\ _).getOrElse(True: Expr[Prop])

  extension (s1: Seq[Expr[Ind]])
    def ===(s2: Seq[Expr[Ind]]): Expr[Prop] =
      seqEq(s1, s2)

  def existsSeq(vars: Seq[Variable[FInd]], formula: FExpr[FProp]): FExpr[FProp] =
    vars.foldRight(formula)(∃(_, _))

  def forallSeq(vars: Seq[Variable[FInd]], formula: FExpr[FProp]): FExpr[FProp] =
    vars.foldRight(formula)(∀(_, _))

  // Some useful functions

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
      case TypeArg(name) => Variable[Ind](name)

  def typeExprToTerm(name: String): Variable[Ind] =
    Variable[Ind](name)

  def typeExprToTerm(tpe: TypeExpr): Expr[Ind] = tpe match
    case TypeRef(name) =>
      Variable[Ind](name)
    case TypeApply(name, args) =>
      val c = Constant[Ind](s"$name[${args.mkString(",")}]")
      registerConstant(c)
      c

  // Well-typedness predicates

  def wellTyped(s: Seq[(Expr[Ind], Expr[Ind])]): Seq[Expr[Prop]] = s.map(_ :: _)

  def wellTyped(s: Seq[(Expr[Ind], ConstructorArg)])(orElse: Expr[Ind]): Seq[Expr[Prop]] =
    s.map((t, arg) => t :: arg.getOrElse(orElse))

  def wellTypedSet(s: Seq[(Expr[Ind], Expr[Ind])]): Set[Expr[Prop]] = wellTyped(s).toSet

  def wellTypedFormula(s: Seq[(Expr[Ind], Expr[Ind])]): Expr[Prop] = seqAnd(wellTyped(s))

  def wellTypedFormula(s: Seq[(Expr[Ind], ConstructorArg)])(
      orElse: Expr[Ind]
  ): Expr[Prop] = seqAnd(wellTyped(s)(orElse))

}
