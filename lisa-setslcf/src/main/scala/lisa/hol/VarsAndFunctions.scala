package lisa.hol

import lisa.SetTheoryLibrary
import lisa.automation._
import lisa.maths.SetTheory.Base.Predef.∈
import lisa.maths.SetTheory.Functions.Predef.{_, given}
import lisa.maths.SetTheory.Types
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.K
import lisa.utils.UserLisaException
import lisa.utils.fol.FOL._
import lisa.utils.prooflib.BasicStepTactic._
import lisa.utils.prooflib.ProofTacticLib.ProofTactic

import SetTheoryLibrary.{have, JUSTIFICATION, thesis, THM, Proof, Theorem}

object VarsAndFunctions /*extends lisa.Main*/:

  import HOLHelperTheorems.{One, nonEmptyFuncSpace, assume}

  // import TypeSystem.*

  val f = variable[Ind]
  val x, y, z = variable[Ind]
  val a = variable[Ind]
  val A, B = variable[Ind]
  val G, H = variable[Ind >>: Ind]

  ///////////////////////////////////////////////
  /////////// Typed HOL Terms ///////////////////
  ///////////////////////////////////////////////

  class TypeVariable(id: Identifier) extends Variable[Ind](id) {
    override def rename(newId: Identifier): TypeVariable = TypeVariable(newId)
  }
  def typevar(using name: sourcecode.Name): TypeVariable = TypeVariable(K.Identifier(name.value))

  class HOLConstantType(id: Identifier, val nonEmptyThm: JUSTIFICATION) extends Constant[Ind](id)
  class HOLConstant(id: Identifier, override val typ: Expr[Ind], val thm: JUSTIFICATION) extends TypedConstant(id, typ, thm)

  class TypedVariable(id: Identifier, val typ: Expr[Ind]) extends Variable[Ind](id) {
    override def toString: String = s"${id.name}:${typ}"
    override def substituteUnsafe(m: Map[Variable[?], Expr[?]]): Expr[Ind] =
      if m.contains(this) then m(this).asInstanceOf[Expr[Ind]]
      else
        val newtyp = typ.substituteUnsafe(m)
        TypedVariable(id, newtyp).asInstanceOf[Expr[Ind]]
    override def rename(newId: Identifier): TypedVariable = TypedVariable(newId, typ)
  }
  def typedvar(typ: Expr[Ind])(using name: sourcecode.Name): TypedVariable = TypedVariable(name.value, typ)
  def typedvar(typ: Expr[Ind], id: Identifier): TypedVariable = TypedVariable(id, typ)

  class HOLAbstraction(v: TypedVariable, b: Expr[Ind]) extends App[Ind >>: Ind, Ind](abs(v.typ), λ(v, b)) {
    override def toString: String = s"λ(${v.id}:${v.typ}. $b)"

    override def substituteUnsafe(m: Map[Variable[?], Expr[?]]): App[Ind >>: Ind, Ind] =
      super.substituteUnsafe(m) match
        case App(App(`abs`, typ), Abs(v1, body)) =>
          HOLAbstraction(TypedVariable(v1.id, typ), body)
        case e =>
          println("Warning: unexpected substitution result: " + e + "for " + this)
          e
  }

  def fun(v: TypedVariable, b: Expr[Ind]): HOLAbstraction = HOLAbstraction(v, b)
  def fun(v: TypeAssign[Variable[Ind]], b: Expr[Ind]): Expr[Ind] =
    abs(v.typ)(λ(v.vari, b))

  def getContext(lo: LisaObject): Set[Expr[Prop]] =
    val frees = lo.freeVars
    frees.flatMap {
      case v: TypedVariable => Set(v is v.typ)
      case v: TypeVariable =>
        val vv = if v.id.name == "x" then Variable[Ind](K.Identifier("x", v.id.no + 1)) else Variable[Ind]("x")
        Set(exists(vv, vv ∈ v))
      case v => Set.empty
    }

  def nonEmpty(typ: Variable[Ind]): Expr[Prop] =
    val v = if typ.id.name == "x" then Variable[Ind](K.Identifier("x", typ.id.no + 1)) else Variable[Ind]("x")
    exists(v, v ∈ typ)

  class LisaHOLException(errorMessage: String)(using sourcecode.Line, sourcecode.File) extends UserLisaException(errorMessage) {
    def showError: String = errorMessage
  }

  def computeType(t: Expr[Ind]): Typ =
    val r = t match
      case tv: TypedVariable =>
        tv.typ
      case tc: TypedConstant => tc.typ
      case #@[Ind >>: Ind, Ind](#@[Ind, (Ind >>: Ind) >>: Ind](`abs`, base), Abs(v, b)) =>
        base ->: computeType(b)
      case App(App(`app`, func), arg) =>
        computeType(func) match
          case dom ->: codom =>
            val argType = computeType(arg)
            if isSame(argType, dom) then codom
            else throw new LisaHOLException("In application " + t + ", argument " + arg + " has type " + argType + " instead of expected " + dom + ".")
          case funcType => throw new LisaHOLException("In application " + t + ", function " + func + " expected to have function type A ->: B, but has type " + funcType + ". ")
      case Multiapp(func, args: List[Expr[Ind]] @unchecked) =>
        func match
          case tcf: TypedConstantFunctional[?] =>
            if tcf.arity != args.size then
              throw new LisaHOLException("computeType can only handle fully applied functions. Function " + tcf + " has arity " + tcf.arity + " but was applied to " + args.size + " arguments.")
            if args
                .zip(tcf.typ.inTyp)
                .forall((arg, inType) =>
                  inType match
                    case Some(value) =>
                      val argType = computeType(arg)
                      lisa.utils.fol.FOL.isSame(optype(inType, arg), (arg is argType))
                    case None => true
                )
            then
              val subst = (tcf.typ.args zip args).map((v, a) => (v := a))
              tcf.typ.outTyp.substitute(subst*)
            else
              val argsTypes = args.map(arg => computeType(arg))
              throw new LisaHOLException("Function " + tcf + " has type " + tcf.typ + " but was applied to arguments " + args + " of types " + argsTypes + ".")
          case _ =>
            throw new LisaHOLException(
              "computeType can only handle typed constant functionals. " + func + " is not a typed constant functional (with args " + args + "). It has class " + func.getClass + "."
            )
      case _ => throw new LisaHOLException("computeTypes only support fully typed terms. " + t + " is not fully typed.")
    r

  def computeContext(terms: Set[Expr[Ind]]): Set[TypeAssign[Variable[Ind]]] = computeContextKnown(terms, Set.empty)

  def computeContextKnown(terms: Set[Expr[Ind]], known: Set[Variable[Ind]]): Set[TypeAssign[Variable[Ind]]] =
    val frees = terms.flatMap(_.freeVars) -- known
    val r1 = frees.foldLeft(List.empty[TypeAssign[Variable[Ind]]]) {
      case (acc1, v: TypedVariable) =>
        (v is v.typ) :: acc1
      case (acc1, v) =>
        acc1
    }
    r1.toSet

  def computeContextOfFormulas(formulas: Set[Expr[Prop]], known: Set[Variable[Ind]] = Set()): (Set[TypeAssign[Variable[Ind]]]) =
    val vars = formulas.flatMap(_.freeVars) -- known
    computeContextKnown(vars.filter(_.sort == K.Ind).toSet.asInstanceOf[Set[Expr[Ind]]], Set.empty)

  def contextToMap(typeAssigns: Set[TypeAssign[Variable[Ind]]]): Map[Variable[Ind], Typ] =
    typeAssigns.map(ta => ta.vari -> ta.typ).toMap

  class HOLSequent(
      val premises: Set[Expr[Ind]],
      val conclusion: Expr[Ind],
      val typeAssigns: Set[TypeAssign[Variable[Ind]]],
      val typeVarsNonEmpty: Set[Expr[Prop]]
  ) extends Sequent(premises.map(_ === One) ++ typeAssigns, Set(conclusion === One)) {

    infix def +<<(t: Expr[Ind]): HOLSequent = HOLSequent(this.premises + t, conclusion, typeAssigns)
    infix def -<<(t: Expr[Ind]): HOLSequent = HOLSequent(this.premises - t, conclusion, typeAssigns)

    override infix def +<<(f: Expr[Prop]): Sequent =
      f match
        case ===(t, One) => +<<(t)
        case ===(One, t) => +<<(t)
        case TypeAssign(v: Variable[Ind], typ) => new HOLSequent(premises, conclusion, typeAssigns + TypeAssign(v, typ), typeVarsNonEmpty)
        case _ => super.+<<(f)
    override infix def -<<(f: Expr[Prop]): Sequent =
      f match
        case ===(t, One) => -<<(t)
        case ===(One, t) => -<<(t)
        case TypeAssign(v: Variable[Ind], typ) => new HOLSequent(premises, conclusion, typeAssigns - TypeAssign(v, typ), typeVarsNonEmpty)
        case _ => super.-<<(f)

    infix def ++<<(s1: HOLSequent): HOLSequent = HOLSequent(this.premises ++ s1.premises, conclusion, typeAssigns ++ s1.typeAssigns)
    infix def --<<(s1: HOLSequent): HOLSequent = HOLSequent(this.premises -- s1.premises, conclusion, typeAssigns -- s1.typeAssigns)

    override infix def ++<<(s1: Sequent): Sequent =
      s1 match
        case s1: HOLSequent => ++<<(s1)
        case s1: Sequent => super.++<<(s1)
    override infix def --<<(s1: Sequent): Sequent =
      s1 match
        case s1: HOLSequent => --<<(s1)
        case s1: Sequent => super.--<<(s1)
  }

  object HOLSequent {

    def apply(premises: Set[Expr[Ind]], conclusion: Expr[Ind], typeAssigns: Set[TypeAssign[Variable[Ind]]] = Set.empty, typeVarsNonEmpty: Set[Expr[Prop]] = Set.empty): HOLSequent = {
      new HOLSequent(premises, conclusion, typeAssigns, typeVarsNonEmpty)
    }

    def fromFOLSequent(s: Sequent): HOLSequent =
      if s.isInstanceOf[HOLSequent] then return s.asInstanceOf[HOLSequent]
      if s.right.size != 1 then throw new IllegalArgumentException("Sequent in HOL must have exactly one conclusion.")
      val r = s.right.head
      r match
        case eqOne(t) =>
          var vartypes = Set.empty[TypeAssign[Variable[Ind]]]
          var typeVarsNonEmpty = Set.empty[Expr[Prop]]
          var prems = Set.empty[Expr[Ind]]
          s.left.foreach { a =>
            a match
              case TypeAssign(v: Variable[Ind], typ) => vartypes += TypeAssign(v, typ)
              case exists(v1: Variable[Ind], v2 ∈ (typ: Variable[Ind])) if v1 == v2 => typeVarsNonEmpty += a
              case eqOne(t) => prems += t
              case _ => throw new IllegalArgumentException("Premises must be of the form t === One or be a type assignment. violating: " + a)
          }
          new HOLSequent(prems, t, vartypes, typeVarsNonEmpty)
        case _ =>
          throw new IllegalArgumentException("Conclusion must be of the form t === One.")

    def unapply(s: Sequent): Option[(Set[Expr[Ind]], Expr[Ind])] =
      if s.isInstanceOf[HOLSequent] then
        val s1 = s.asInstanceOf[HOLSequent]
        Some((s1.premises, s1.conclusion))
      else
        try {
          val s1 = fromFOLSequent(s)
          Some((s1.premises, s1.conclusion))
        } catch
          case e: IllegalArgumentException =>
            println(e.getMessage())
            return None
  }

  opaque type TypedForall <: Expr[Prop] & { val v: Variable[Ind]; val prop: Expr[Prop] } = TypedForallConcrete

  private class TypedForallConcrete(val v: Variable[Ind], val vType: Typ, val prop: Expr[Prop]) extends App(forall, λ(v, (v is vType) ==> prop)) {
    override def toString = s"∀$v : $vType. $prop"
  }

  object TypedForall {
    def apply(v: Variable[Ind], vType: Typ, prop: Expr[Prop]): TypedForall = new TypedForallConcrete(v, vType, prop)
  }

  def tforall(v: Variable[Ind], vType: Typ, prop: Expr[Prop]): TypedForall = TypedForall(v, vType, prop)
  def tforall(v: TypeAssign[Variable[Ind]], prop: Expr[Prop]): TypedForall = TypedForall(v.vari, v.typ, prop)
  inline given Conversion[TypedForall, Expr[Prop]] with
    def apply(tf: TypedForall): Expr[Prop] = tf

  val holeq: TypedConstantFunctional[Ind >>: Ind] = HOLHelperTheorems.=:=

  object eqOne {
    def unapply(f: Expr[Prop]): Option[Expr[Ind]] = f match {
      case ===(t, One) => Some(t)
      case ===(One, t) => Some(t)
      case _ => None
    }

    def apply(t: Expr[Ind]): Expr[Prop] = t === One
  }

  given Conversion[Expr[Ind], Expr[Prop]] = t => eqOne(t)

  extension (t1: Expr[Ind]) {
    def =:=(t2: Expr[Ind]): Expr[Ind] =
      val A = computeType(t1)
      val B = computeType(t2)
      if isSame(A, B) then holeq(A) * (t1) * (t2)
      else throw new Exception("in expression " + t1 + " =:= " + t2 + " the types " + A + " of left-hand side and " + B + " of right-hand side do not match.")
    def equalityOfType(A: Expr[Ind])(t2: Expr[Ind]): Expr[Ind] = holeq(A) * (t1) * (t2) // compute A with computeType, possibly.
  }

  object TypeNonEmptyProof extends ProofTactic {
    val A = variable[Ind]
    val B = variable[Ind]

    def apply(using proof: Proof)(typ: Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      typ match {
        case ctt: HOLConstantType => have(ctt.nonEmptyThm)
        case v: Variable[Ind] =>
          val x = Variable.fresh[Ind](Set(v), "x")
          val ax = assume(exists(x, x ∈ v))
          have(ax.statement) by Restate
        case a ->: b =>
          val x = Variable.fresh[Ind](Set(a, b), "x")
          val s1 = have(TypeNonEmptyProof(b))
          have(s1.statement.left |- exists(x, x ∈ (a ->: b))) by Tautology.from(s1, nonEmptyFuncSpace of (A := a, B := b))
        case _ => throw new IllegalArgumentException("TypeNonEmptyProof can only handle type constants, type variables, and function types.")
      }
    }
  }

  def TypingTheorem(using om: lisa.utils.prooflib.OutputManager, name: sourcecode.FullName)(assignment: Expr[Prop]): THM =
    val contextAssigns = getContext(assignment)
    Theorem(using om, name)(contextAssigns |- assignment) {
      have(thesis) by Typecheck.prove
    }

  object HOLProofType extends ProofTactic {
    def apply2(using proof: SetTheoryLibrary.Proof)(t: Expr[Ind]): proof.ProofTacticJudgement =
      val contextAssigns: Set[Expr[Prop]] = getContext(t)
      val r = Typecheck.inferProof(contextAssigns, t)
      r

    def apply(using proof: SetTheoryLibrary.Proof)(t: Expr[Ind]): proof.ProofTacticJudgement = TacticSubproof {
      given SetTheoryLibrary.type = SetTheoryLibrary
      t match
        case tc: TypedConstant =>
          have(tc.justif.statement) by Weakening(tc.justif)
        case _ =>
          have(apply2(t))
    }
  }

  given termToSetConv[T <: Expr[Ind]]: FormulaSetConverter[T] = t => Set(eqOne(t))
  given setTermToSetConv[T <: Iterable[Expr[Ind]]]: FormulaSetConverter[T] = _.map(eqOne(_)).toSet
  given Conversion[Expr[Ind], HOLSequent] = HOLSequent(Set(), _)

end VarsAndFunctions
