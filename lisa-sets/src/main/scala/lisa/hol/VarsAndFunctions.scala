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
import scala.collection.mutable

import SetTheoryLibrary.{have, JUSTIFICATION, thesis, THM, Proof, Theorem}
import lisa.utils.prooflib.BasicStepTactic.Weakening

object VarsAndFunctions /*extends lisa.Main*/:

  import HOLHelperTheorems.{One, nonEmptyFuncSpace, assume, eqRefl}

  val lib = SetTheoryLibrary

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

  class HOLPolymorphicType[S: Sort](id: Identifier, val freeTypeVars: Seq[TypeVariable], val nonEmptyThm: JUSTIFICATION) extends Constant[S](id)
  
  type HOLConstantType = HOLPolymorphicType[Ind]
  object HOLConstantType:
    def apply(id: Identifier, nonEmptyThm: JUSTIFICATION): HOLConstantType =
      HOLPolymorphicType(id, Seq.empty, nonEmptyThm)
    def unapply(typ: HOLPolymorphicType[?]): Option[HOLConstantType] =
      if typ.sort == K.Ind then Some(typ.asInstanceOf[HOLConstantType])
      else None

  class HOLConstant(id: Identifier, override val typ: Expr[Ind], val thm: JUSTIFICATION) extends TypedConstant(id, typ, thm):
    val holDefinition = 
      val theDefinition = this.definition
      // we extract the definition body, and replace the raw constant by this lifted class
      val left = this
      val right = theDefinition.statement.right.head match
        case ===(l, r) => r
        case _ => throw new IllegalArgumentException("Theorem " + thm + " used to define constant " + id + " must be an equality.")

      Theorem(holeq(typ) * left * right) {
        val s1 = lib.have((left :: typ) |- holeq(typ) * left * left) by Weakening(eqRefl of (A := typ, x := left, y := left))
        val s2 = lib.have(holeq(typ) * left * left) by Cut(thm, s1)
        val s3 = lib.have(left === right |- holeq(typ) * left * right) by RightSubstEq.withParameters(Seq((left, right)), (Seq(x), holeq(typ) * left * x))(s2)
        val s4 = lib.have(holeq(typ) * left * right) by Cut(theDefinition, s3)
      }
  class HOLPolymorphicConstant[S: Sort](id: Identifier, override val typ: FunctionalClass, override val justif: JUSTIFICATION) extends TypedConstantFunctional[S](id, typ, justif):
    /**
     * The definition of the constant as an HOL theorem.
     * 
     * ```
     *    freeTypeVars.map(nonEmpty) |- F(freeTypeVars) =:= body
     * ```
     * FIXME: currently does not account for type classes!
     */
    val holDefinition =  
      val theDefinition = this.definition
      // we extract the definition body, and replace the raw constant by this lifted class
      val left = (this #@@ typ.args).asInstanceOf[Expr[Ind]]
      val right = theDefinition.statement.right.head match
        case ===(l, r) => betaReduce(r)
        case _ => throw new IllegalArgumentException("Theorem " + justif + " used to define constant " + id + " must be an equality.")
      val nonEmpties = typ.args.map(nonEmpty).toSet
      val otyp = typ.outTyp
      Theorem(nonEmpties |- (holeq(otyp) * left * right)) {
        val typeJustif = have(nonEmpties |- (left :: otyp)) by Weakening(justif.of(typ.args*))
        val s1 = lib.have((left :: otyp) |- holeq(otyp) * left * left) by Restate.from(eqRefl of (A := otyp, x := left, y := left))
        val s2 = lib.have(nonEmpties |- holeq(otyp) * left * left) by Cut(typeJustif, s1)
        val s3 = lib.have((nonEmpties, left === right) |- holeq(otyp) * left * right) by RightSubstEq.withParameters(Seq((left, right)), (Seq(x), holeq(otyp) * left * x))(s2)
        val s4 = lib.have(nonEmpties |- holeq(otyp) * left * right) by Cut(theDefinition, s3)
      }

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
    /**
      * Pure bool premises as in HOL. Each `prem: Expr[Ind]` is equivalen to
      * adding `prem === One: Expr[Prop]` to the sequent.
      */
      val premises: Set[Expr[Ind]],
      /**
        * Premises that are not of the form `t === One` as used by HOL. Should
        * only appear in mixed HOL/FOL proofs.
        */
      val folPremises: Set[Expr[Prop]],
      /**
        * Conclusion of the sequent. The term `conclusion: Expr[Ind]` represents
        * a real conclusion of the form `conclusion === One: Expr[Prop]`.
        */
      val conclusion: Expr[Ind],
      /**
        * Type assignments appearing in the context of this sequent.
        */
      val typeAssigns: Set[TypeAssign[Variable[Ind]]],
      /**
        * Free type variables appearing in the context of this sequent, each of
        * whose non-emptiness is to be justified.
        */
      val typeVarsNonEmpty: Set[Expr[Prop]]
  ) extends Sequent(premises.map(_ === One) ++ typeAssigns, Set(conclusion === One)) {

    /**
      * Add a (boolean) term to the premises of this sequent. Equivalent to
      * assuming `t === One`.
      */
    infix def +<<(t: Expr[Ind]): HOLSequent = HOLSequent(this.premises + t, conclusion, typeAssigns)
    /**
      * Remove a (boolean) term from the premises of this sequent.
      */
    infix def -<<(t: Expr[Ind]): HOLSequent = HOLSequent(this.premises - t, conclusion, typeAssigns)

    override infix def +<<(f: Expr[Prop]): Sequent =
      f match
        case ===(t, One) => +<<(t)
        case ===(One, t) => +<<(t)
        case TypeAssign(v: Variable[Ind], typ) => new HOLSequent(premises, folPremises, conclusion, typeAssigns + TypeAssign(v, typ), typeVarsNonEmpty)
        case _ => new HOLSequent(premises, folPremises + f, conclusion, typeAssigns, typeVarsNonEmpty)
    override infix def -<<(f: Expr[Prop]): Sequent =
      f match
        case ===(t, One) => -<<(t)
        case ===(One, t) => -<<(t)
        case TypeAssign(v: Variable[Ind], typ) => new HOLSequent(premises, folPremises, conclusion, typeAssigns - TypeAssign(v, typ), typeVarsNonEmpty)
        case _ => new HOLSequent(premises, folPremises - f, conclusion, typeAssigns, typeVarsNonEmpty)

    infix def ++<<(s1: HOLSequent): HOLSequent = new HOLSequent(this.premises ++ s1.premises, this.folPremises ++ s1.folPremises, conclusion, typeAssigns ++ s1.typeAssigns, typeVarsNonEmpty ++ s1.typeVarsNonEmpty)
    infix def --<<(s1: HOLSequent): HOLSequent = new HOLSequent(this.premises -- s1.premises, this.folPremises -- s1.folPremises, conclusion, typeAssigns -- s1.typeAssigns, typeVarsNonEmpty -- s1.typeVarsNonEmpty)
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
      new HOLSequent(premises, Set.empty, conclusion, typeAssigns, typeVarsNonEmpty)
    }

    def fromFOLSequent(s: Sequent): HOLSequent =
      if s.isInstanceOf[HOLSequent] then return s.asInstanceOf[HOLSequent]
      if s.right.size != 1 then throw new IllegalArgumentException("Sequent in HOL must have exactly one conclusion.")
      val r = s.right.head
      r match
        case eqOne(t) =>
          var vartypes = Set.empty[TypeAssign[Variable[Ind]]]
          var typeVarsNonEmpty = Set.empty[Expr[Prop]]
          val prems = Set.newBuilder[Expr[Ind]]
          val folPrems = Set.newBuilder[Expr[Prop]]
          s.left.foreach { a =>
            a match
              case TypeAssign(v: Variable[Ind], typ) => vartypes += TypeAssign(v, typ)
              case exists(v1: Variable[Ind], v2 ∈ (typ: Variable[Ind])) if v1 == v2 => typeVarsNonEmpty += a
              case eqOne(t) => prems += t
              case _ => folPrems += a
          }
          new HOLSequent(prems.result(), folPrems.result(), t, vartypes, typeVarsNonEmpty)
        case _ =>
          throw new IllegalArgumentException("Conclusion must be of the form t === One.")

    def unapply(s: Sequent): Option[(Set[Expr[Ind]], Set[Expr[Prop]], Expr[Ind])] =
      if s.isInstanceOf[HOLSequent] then
        val s1 = s.asInstanceOf[HOLSequent]
        Some((s1.premises, s1.folPremises, s1.conclusion))
      else
        try {
          val s1 = fromFOLSequent(s)
          Some((s1.premises, s1.folPremises, s1.conclusion))
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

    private val cache: mutable.Map[Long, SetTheoryLibrary.JUSTIFICATION] = mutable.Map.empty  

    inline def code[S: Sort](t: Expr[S]): Long = t.underlying.uniqueNumber

    def apply2(t: Expr[Ind]): SetTheoryLibrary.JUSTIFICATION =
      cache.get(code(t)) match
        case Some(justif) => justif
        case None =>
          val contextAssigns: Set[Expr[Prop]] = getContext(t)
          val just =
            try
              Theorem(contextAssigns |- t :: computeType(t)) {
                have(thesis) by Typecheck.prove
              }
            catch
              case e: Exception =>
                throw LisaHOLException("Failed to compute and prove typing for term " + t + ": " + e.getMessage())
          cache.put(code(t), just)
          just

    def apply(t: Expr[Ind]): SetTheoryLibrary.JUSTIFICATION =
      t match
        case tc: TypedConstant =>
          tc.justif
        case _ =>
          apply2(t)
  }

  given termToSetConv[T <: Expr[Ind]]: FormulaSetConverter[T] = t => Set(eqOne(t))
  given setTermToSetConv[T <: Iterable[Expr[Ind]]]: FormulaSetConverter[T] = _.map(eqOne(_)).toSet
  given Conversion[Expr[Ind], HOLSequent] = HOLSequent(Set(), _)

end VarsAndFunctions
