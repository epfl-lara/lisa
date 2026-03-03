package lisa.maths.SetTheory.Types

//import lisa.maths.SetTheory.Base.Predef.{*, given}
//import lisa.maths.SetTheory.Functions.Predef.{*}
//import lisa.maths.SetTheory.Cardinal.Predef.{*}
//import lisa.maths.Quantifiers.*
import lisa.SetTheoryLibrary._
import lisa.maths.SetTheory.Base.Predef.∪
import lisa.maths.SetTheory.Functions.Predef._
import lisa.utils.fol.FOL.{=== => _, ∀ => _, ≠ => _, _, given}
import lisa.utils.prooflib.OutputManager

/**
 * This file defines the most common variable symbols (x, y, z, etc.)
 * and their types for a consistent use through the Calculus of Construction
 * as well as some useful helper theorems used in the typing rules.
 *
 * ## Syntactic Sugar
 *
 * This file provides ergonomic syntax extensions for dependent type theory:
 *
 * ### Type Membership
 * - `t is T` — type assignment (alias for `t ∈ T`)
 * - `t :: T` — type assignment (alias for `t ∈ T`)
 *
 * ### Function Application
 * - `f @@ x` — function application (alias for `app(f)(x)`)
 * - `f * x` — function application (alias for `app(f)(x)`)
 *
 * ### Function Types
 * - `A ->: B` — non-dependent function type (equivalent to `Π(x :: A). B` where x is fresh)
 *
 * ### Dependent Types
 * - `Π(x :: A, B(x))` — dependent product type using VarTypeAssign
 * - `fun(x :: A, e(x))` — lambda abstraction using VarTypeAssign
 */

object TypingHelpers:
  import lisa.maths.SetTheory.Base.Predef.{given}
  // import lisa.maths.SetTheory.Functions.Predef.{}
  // import lisa.maths.SetTheory.Cardinal.Predef.{}

  // Base term
  private val e1, e2, x, y, f, a, b = variable[Ind]

  // Function
  private val e = variable[Ind >>: Ind]

  // Base type
  private val T, T1 = variable[Ind]

  // Dependent type
  private val T2, T2p = variable[Ind >>: Ind]

  // Proposition
  private val Q, H = variable[Ind >>: Prop]

  // Type Universe
  private val U, U1, U2 = variable[Ind]

  // Proposition
  private val p = variable[Prop]

  /**
   * Universe(Type) level
   */
  val Typ0 = variable[Ind]
  val typeOf = ∈

  type Typ = Expr[Ind] // | Expr[Ind >>: Prop]

  // Pattern extractor for the 'app' Shallow Embedding constant.
  // It allows matching expressions of the form app(func)(arg) using the pattern Sapp(func, arg)
  object Sapp:
    def unapply(e: Expr[?]): Option[(Expr[Ind], Expr[Ind])] =
      e match
        case App(App(`app`, func), arg) =>
          Some((func.asInstanceOf[Expr[Ind]], arg.asInstanceOf[Expr[Ind]]))
        case _ => None

  // Type/Term abstraction λx:T.e <=> abs(T)(λx.e)

  private class TypeAssign_[+T <: Expr[Ind]](val x: T, val typ: Expr[Ind]) extends App[Ind, Prop](∈(x), typ)
  opaque type TypeAssign[+T <: Expr[Ind]] <: Expr[Prop] = TypeAssign_[T]

  extension [T <: Expr[Ind]](vta: TypeAssign[T]) {
    def vari: T = vta.x
    def typ: Expr[Ind] = vta.typ
  }

  object TypeAssign {
    def apply[T <: Expr[Ind]](x: T, typ: Expr[Ind]): TypeAssign[T] = new TypeAssign_(x, typ)
    def unapply[T](e: Expr[Prop]): Option[(Expr[Ind], Expr[Ind])] =
      if e.isInstanceOf[TypeAssign_[Expr[Ind]]] then
        val vta = e.asInstanceOf[TypeAssign_[Expr[Ind]]]
        Some((vta.x, vta.typ))
      else
        e match
          case x ∈ typ => Some((x.asInstanceOf[Expr[Ind]], typ))
          case _ => None
  }
  object VarTypeAssign:
    def unapply(e: Expr[Prop]): Option[(Variable[Ind], Expr[Ind])] = e match
      case TypeAssign(x: Variable[Ind], typ) => Some((x, typ))
      case _ => None

  extension [T <: Expr[Ind]](t: T) {
    infix def ::(e: Expr[Ind]) = TypeAssign[T](t, e)
    infix def is(e: Expr[Ind]) = TypeAssign[T](t, e)
  }

  inline given [T <: Expr[Ind]]: Conversion[TypeAssign[T], Expr[Prop]] with
    def apply(vta: TypeAssign[T]): Expr[Prop] = vta

  def fun(v: TypeAssign[Variable[Ind]], b: Expr[Ind]): Expr[Ind] = abs(v.typ)(λ(v.x, b))

  def `Π`(v: TypeAssign[Variable[Ind]], b: Expr[Ind]): Expr[Ind] = Pi(v.typ)(λ(v.x, b))

  class CstTypeAssign(val c: Constant[Ind], val typ: Expr[Ind]) extends App[Ind, Prop](∈(c), typ)

  // Dependent productin type: Π(x:T1).T2

  // Pattern extractor for the `⊆` Shallow Embedding constant.
  // It allows matching expressions of the form ⊆(t1)(t2) using the pattern SUnion(t1, t2)
  object SUnion:
    def unapply(e: Expr[?]): Option[(Expr[Ind], Expr[Ind])] =
      e match
        case App(App(`∪`, t1), t2) =>
          Some((t1.asInstanceOf[Expr[Ind]], t2.asInstanceOf[Expr[Ind]]))
        case _ => None

  // ============================================================================
  // Syntactic Sugar Extensions (OldTypeSystem compatibility layer)
  // ============================================================================

  /**
   * Function application operators (aliases for app)
   *
   * Usage:
   *   f @@ x  // equivalent to app(f)(x)
   *   f * x   // equivalent to app(f)(x)
   */
  extension (f: Expr[Ind]) {
    infix def @@(arg: Expr[Ind]): Expr[Ind] = app(f)(arg)
    infix def *(arg: Expr[Ind]): Expr[Ind] = app(f)(arg)
  }
  object * {
    private val multi_app = Multiapp(app)
    def unapply(t: Expr[Ind]): Option[(Expr[Ind], Expr[Ind])] = app.unapply2(t)
  }

  // ============================================================================
  // Typed Constants
  // ============================================================================

  class TypedConstant(id: Identifier, val typ: Typ, val justif: JUSTIFICATION) extends Constant[Ind](id) {
    val formula = TypeAssign[Constant[Ind]](this, typ)
    assert(justif.statement.left.isEmpty && (justif.statement.right.head == formula))

    override def substituteUnsafe(m: Map[Variable[?], Expr[?]]): TypedConstant = this
    override def substituteWithCheck(m: Map[Variable[?], Expr[?]]): TypedConstant =
      super.substituteWithCheck(m).asInstanceOf[TypedConstant]
    override def substitute(pairs: SubstPair*): TypedConstant =
      super.substitute(pairs*).asInstanceOf[TypedConstant]
  }

  def optype(t: Option[Typ], member: Expr[Ind]): Expr[Prop] = t match
    case Some(typ) => member is typ
    case None => top

  /**
    * A class representing the typing information of a functional constant.
    *
    * A functional class with `inType = Seq(T)`, `args = Seq(A)`, and `outType =
    * A -> A` represents the class of functions `Λ A : T. A -> A`.
    *
    * If `T` is `None`, this means `A` is an unrestricted set (like `A : Any`).
    */
  case class FunctionalClass(inTyp: Seq[Option[Typ]], args: Seq[Variable[Ind]], outTyp: Typ) {
    def formula(f: Expr[?]): Expr[Prop] = {
      val inner = (args.zip(inTyp).map((term, inType) => optype(inType, term)).reduceLeft[Expr[Prop]]((a, b) => a /\ b)) ==> ((f #@@ args).asInstanceOf[Expr[Ind]] `is` outTyp)
      args.foldRight(inner)((v, form) => forall(v, form))
    }

    def formulaMinusOne(f: Constant[?]): Expr[Prop] = {
      val inner = (args.zip(inTyp).map((term, inType) => optype(inType, term)).reduceLeft[Expr[Prop]]((a, b) => a /\ b)) ==> ((f #@@ args).asInstanceOf[Expr[Ind]] `is` outTyp)
      args.tail.foldRight(inner)((v, form) => forall(v, form))
    }
  }

  class FunctionalTypeAssign[S](
      const: Constant[S],
      typ: FunctionalClass
  ) extends App[Ind >>: Prop, Prop](forall, λ(typ.args.head, typ.formulaMinusOne(const))) {}

  class TypedConstantFunctional[S: Sort](id: Identifier, val typ: FunctionalClass, val justif: JUSTIFICATION) extends Constant[S](id) {

    assert(typ.inTyp.size == arity, s"TypedConstantFunctional arity mismatch: symbol $id  expected arity ${arity}, got ${typ.inTyp}.")

    override def substituteUnsafe(m: Map[Variable[?], Expr[?]]): TypedConstantFunctional[S] = this
    override def substituteWithCheck(m: Map[Variable[?], Expr[?]]): TypedConstantFunctional[S] =
      super.substituteWithCheck(m).asInstanceOf[TypedConstantFunctional[S]]
    override def substitute(pairs: SubstPair*): TypedConstantFunctional[S] =
      super.substitute(pairs*).asInstanceOf[TypedConstantFunctional[S]]

  }

  ///////////////////////
  ///// Definitions /////
  ///////////////////////

  class TypedSimpleConstantDefinition(using om: OutputManager)(fullName: String, line: Int, file: String)(
      val expression: Expr[Ind],
      val typ: Typ
  ) extends DirectDefinition[Ind](fullName, line, file)(expression, Seq[Variable[?]]()) {
    val typingName = "typing_" + fullName
    val typingJudgement = THM(cst :: typ, typingName, line, file, InternalStatement)({
      // have(expression :: typ) by TypeChecker.prove
      // thenHave(thesis) by lisa.automation.Substitution.ApplyRules(getShortDefinition(cst).get) //TODO
    })
    val typedLabel: TypedConstant = TypedConstant(cst.id, typ, typingJudgement)

  }

  def TYPEDEF(using om: OutputManager, name: sourcecode.FullName, line: sourcecode.Line, file: sourcecode.File)(term: Expr[Ind], typ: Typ): TypedConstant =
    TypedSimpleConstantDefinition(name.value, line.value, file.value)(term, typ).typedLabel

  extension (c: Constant[Ind]) {
    def typedWith(typ: Typ)(justif: JUSTIFICATION): TypedConstant =
      if justif.statement.right.size != 1 || justif.statement.left.size != 0 || !K.isSame((c `is` typ).underlying, justif.statement.right.head.underlying) then
        throw new IllegalArgumentException(s"A proof of typing of $c must be of the form ${c :: typ}, but the given justification shows ${justif.statement}.")
      else TypedConstant(c.id, typ, justif)
  }
