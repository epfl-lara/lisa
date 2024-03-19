
package lisa.hol
import lisa.maths.settheory.types.TypeSystem.{`*` => _,  *}
import lisa.maths.settheory.types.TypeLib
import lisa.maths.settheory.types.TypeLib.{𝔹 => _, *}
import TypeChecker.*
import lisa.maths.settheory.SetTheory.{pair, ∅}

import lisa.fol.FOL as F
import lisa.fol.FOL.{Identifier, Term}
import lisa.prooflib.ProofTacticLib.ProofTactic
import lisa.SetTheoryLibrary
import lisa.hol.VarsAndFunctions.HOLSequent.toHOLSequent
import lisa.maths.settheory.SetTheory.cartesianProduct
import lisa.maths.settheory.SetTheory.secondInPair
import lisa.fol.FOLHelpers.freshVariable
import lisa.utils.unification.UnificationUtils.matchTerm


object VarsAndFunctions {

  private given lisa.prooflib.OutputManager = lisa.maths.settheory.SetTheory.om

  def main(args: Array[String]): Unit = {
    val x = typedvar(𝔹)
    val testTerm = Abstraction(x, x)

    println(testTerm)
  }

  type Type = Term

  def computeContext(terms: Set[Term]) = computeContextKnown(terms, Set.empty)

  def computeContextKnown(terms: Set[Term], known: Set[Variable]): (Set[VarTypeAssignment], Set[AbstractionDefinition]) = 
    val frees = terms.flatMap(_.freeVariables) -- known
    val (r1, r2) = frees.foldLeft((List.empty[VarTypeAssignment], List.empty[AbstractionDefinition])) {
      case ((acc1, acc2), a: AbstrVar) => 
        (acc1, a.defin :: acc2)
      case ((acc1, acc2), v: TypedVar) => 
        ((v is v.typ).asInstanceOf[VarTypeAssignment] :: acc1, acc2)
      case ((acc1, acc2), v) => 
        (acc1, acc2)
    }
    val rec = if r2.isEmpty then (Set(), Set()) else computeContextOfFormulas(r2.toSet, frees)
    (r1.toSet, r2.toSet ++ rec._2)

  def computeContextOfFormulas(formulas: Set[Formula], known: Set[Variable] = Set()): (Set[VarTypeAssignment], Set[AbstractionDefinition]) = 
    val vars = formulas.flatMap(_.freeVariables) -- known
    computeContextKnown(vars.toSet, Set.empty)

  private def HOLSeqToFOLSeq(left: Set[Term], right: Term): (Set[VarTypeAssignment], Set[AbstractionDefinition]) = {
    computeContext(left + right)
  }

  class HOLSequent(
    val premises: Set[Term],
    val conclusion: Term,
    val varTypes: Set[VarTypeAssignment],
    val abstrs: Set[AbstractionDefinition]
    ) extends F.Sequent(premises.map(_ === One) ++ varTypes ++ abstrs, Set(conclusion === One)) {

      infix def +<<(t: Term): HOLSequent = HOLSequent(this.premises + t, conclusion)
      infix def -<<(t: Term): HOLSequent = HOLSequent(this.premises - t, conclusion)

      override infix def +<<(f: Formula): F.Sequent = 
        f match 
          case ===(t, One) => +<<(t)
          case ===(One, t) => +<<(t)
          case _ => super.+<<(f)
      override infix def -<<(f: Formula): F.Sequent = 
        f match 
          case ===(t, One) => -<<(t)
          case ===(One, t) => -<<(t)
          case _ => super.-<<(f)

      infix def ++<<(s1: HOLSequent): HOLSequent = HOLSequent(this.premises ++ s1.premises, conclusion)
      infix def --<<(s1: HOLSequent): HOLSequent = HOLSequent(this.premises -- s1.premises, conclusion)

      override infix def ++<<(s1: F.Sequent): F.Sequent = 
        s1 match 
          case s1: HOLSequent => ++<<(s1)
          case s1: F.Sequent => super.++<<(s1)
      override infix def --<<(s1: F.Sequent): F.Sequent = 
        s1 match 
          case s1: HOLSequent => --<<(s1)
          case s1: F.Sequent => super.--<<(s1)

  }



  import F.{given}

  class ConstantTypeTerm(id: Identifier, val nonEmptyThm: JUSTIFICATION) extends Constant(id)

  private given TypeLib.library.type = TypeLib.library
  val boolNonEmpty = Theorem(exists(x, in(x, TypeLib.𝔹))) {
    have(thesis) by RightExists(One.justif)
  }

  val G = function[1]
  val λ = variable
  //val functionsRelativization = Axiom(∀(x, (x ∈ A) ==> (G(x) ∈ B)) ==> ∃(λ, (λ ∈ (A |=> B)) /\ ∀(x, (λ*x) === G(x))) )


  val functionalExtentionality = Axiom({
    val f = typedvar(A |=> B)
    val g = typedvar(A |=> B)
    val x = typedvar(A)
    ((f :: (A |=> B)) /\ (g :: (A |=> B)) /\ tforall(x, f*x === g*x)) ==> (f === g)
  })

  val T = variable
  val nonEmptyTypeExists = Theorem(exists(T, exists(x, in(x, T)))) {
    have(thesis) by RightExists(boolNonEmpty)
  }
  val 𝔹 = ConstantTypeTerm("𝔹", boolNonEmpty)


  val =:= : TypedConstantFunctional[1] ={
    val =:= =  F.ConstantFunctionLabel.infix("=:=", 1)
    addSymbol(=:=)
    val typ =  (A |=> (A |=> 𝔹))
    val typing_of_eq = Axiom(F.forall(A, =:=(A) :: typ))
    TypedConstantFunctional[1]("=:=", 1, FunctionalClass(Seq(any), Seq(A), (A |=> (A |=> 𝔹)), 1), typing_of_eq)
  }
  lazy val eqDefin = {
    val x = typedvar(A)
    val y = typedvar(A)
    val eqDefin = Axiom(((x::A) /\ (y::A)) ==> ((x =:= y)===One) <=> (x===y))
    eqDefin
  }

  val holeq : TypedConstantFunctional[1] = VarsAndFunctions.=:=

  object eqOne {
    def unapply(f: Formula): Option[Term] = f match {
      case ===(t, One) => Some(t)
      case ===(One, t) => Some(t)
      case _ => None
    }
    
      def apply(t: Term): Formula = t === One
  }

  given Conversion[Term, F.Formula] = t => eqOne(t)

  extension (t1:Term) {
    def =:=(t2:Term): Term = 
      val A = computeType(t1)
      if (A == computeType(t2)) 
        holeq.applySeq(Seq(A))*(t1)*(t2) 
      else 
        throw new TypingException("in expression " + t1 + " =:= " + t2 + " the types " + A + "of left-hand side and " + computeType(t2) + " of right-hand side do not match.")
    def equalityOfType(A:Term) (t2:Term): Term = holeq.applySeq(Seq(A))*(t1)*(t2) //compute A with computeType, possibly.
  }

  object HOLSequent {
    def apply(premises: Set[Term], conclusion: Term): HOLSequent = {
      val (valTypes, abstr) = HOLSeqToFOLSeq(premises, conclusion)
      new HOLSequent(premises, conclusion, valTypes, abstr)
    }

    def toHOLSequent(s: F.Sequent): HOLSequent = 
      if s.isInstanceOf[HOLSequent] then 
        return s.asInstanceOf[HOLSequent]
      if s.right.size != 1 then 
        throw new IllegalArgumentException("Sequent must have exactly one conclusion.")
      val r = s.right.head
      r match 
        case eqOne(t) => 
          var vartypes = List.empty[VarTypeAssignment]
          var abstr = List.empty[AbstractionDefinition]
          var prems = Set.empty[Term]
          s.left.foreach {
            case v: VarTypeAssignment => vartypes = v :: vartypes
            case a: AbstractionDefinition => abstr = a :: abstr
            case eqOne(t) => prems = prems + t
            case _ => throw new IllegalArgumentException("Premises must be of the form t === One, be a type assignment or an abstraction definition.")
          }
          new HOLSequent(prems.toSet, t, vartypes.toSet, abstr.toSet)
        case _ => 
          throw new IllegalArgumentException("Conclusion must be of the form t === One.")
      


    def unapply(s: F.Sequent): Option[(Set[Term], Term)] = 
      if s.isInstanceOf[HOLSequent] then 
        val s1 = s.asInstanceOf[HOLSequent]
        Some((s1.premises, s1.conclusion))
      else 
        try {
          val s1 = toHOLSequent(s)
          Some((s1.premises, s1.conclusion))
        }
        catch
          case e: IllegalArgumentException => 
            println(e.getMessage())
            return None


  }


  def TypingTheorem(using om: lisa.prooflib.OutputManager, name: sourcecode.FullName)(assignment: TypeAssignment[Type]): THM = 
    val (l1, l2) = HOLSeqToFOLSeq(Set.empty, assignment.t)
    Theorem(using om, name)(F.Sequent(l1 ++ l2, Set(assignment.t is assignment.typ))) {
      have(thesis) by TypeChecker.prove
    }
    
  extension (t:Term) {
    def * (t2:Term): Term = HOLApplication(t, t2)
  }

  object * {def unapply(t: Term): Option[(Term, Term)] = t match {
    case AppliedFunction(f, a) => Some((f, a))
    case app(f, a) => Some((f, a))
    case _ => None
  }}

  ///////////////////////////////////////
  /////////// Typed Variables ///////////
  ///////////////////////////////////////

  class TypedForall( val v: Variable, val prop: Formula ) extends BinderFormula(forall, v, v match {
    case v: TypedVar => (v is v.typ) ==> prop
    case _ => prop
  }
  ) {
    override def toString = 
      val typeStr = v match
        case v: TypedVar => s" : ${v.typ}"
        case _ => "" 
      s"∀$v$typeStr. $prop"
  }


  def tforall(v: TypedVar, prop: Formula): TypedForall = TypedForall(v, prop)

  var counter: Int = 0

  type VarTypeAssignment = Formula & TypeAssignment[Type] {val t:Variable}
  

  def nextId: Identifier = {
    counter += 1
    Identifier("$λ", counter)
  }

  sealed trait TypedHOLTerm {
    this : Term =>
    val typ: Type
    def asTerm: Term & TypedHOLTerm = this
    var typThm: Option[JUSTIFICATION] = None // conditional proof of this :: typ
  }

  class PolymorphicConstant[N <: Arity](label: TypedConstantFunctional[N], args: Term**N) extends AppliedFunctional(label, args.toSeq) with TypedHOLTerm {
    val typ = {
      val subst = (label.typ.args zip args.toSeq).map((v, a) => (v := a))
      label.typ.out.asInstanceOf[Term].substitute(subst: _*)
    }

  }
  class HOLConstant(id: Identifier, override val typ: Term, val thm: JUSTIFICATION) extends TypedConstant[Term](id, typ, thm) with TypedHOLTerm {
    typThm = Some(thm)
  }

  type HOLTerm = HOLApplication | TypedVar | Abstraction | TypedConstant[Term] | PolymorphicConstant[?]

  var i = 0
  extension (ht: HOLTerm)
    def typ = ht match
      case ht: TypedHOLTerm => ht.typ
      case tc: TypedConstant[?] => tc.typ.asInstanceOf[Term]
    
    def getTypThmOrElseUpdate(computeProof: Proof ?=> Unit): JUSTIFICATION = {
      ht match
        case ht: TypedHOLTerm => 
          ht.typThm match
            case Some(thm) => thm
            case None => 
              val name = "¢typ_hol_" + i
              i += 1
              val ctx = computeContext(Set(ht.asTerm))
              val newthm = THM( (ctx._1 ++ ctx._2) |- (ht.asTerm::ht.typ), name, summon[sourcecode.Line].value, summon[sourcecode.File].value, InternalStatement)(pr ?=> computeProof(using pr))
              ht.typThm = Some(newthm)
              newthm
        case tc: TypedConstant[?] => tc.justif
      
      
    }

  class HOLApplication(func: Term, arg: Term) extends AppliedFunction(func, arg) with TypedHOLTerm {
    val typ = computeType(func) match {
      case inType |=> outType => 
        if computeType(arg) == inType then outType
        else 
          throw new IllegalArgumentException("Argument " + arg + " of function " + func + " has type " + computeType(arg) + " instead of expected " + inType + ".")
      case funcType => throw new IllegalArgumentException("Function " + func + " expected to have function type A |=> B, but has type " + funcType + ". ")
    }

  }

  class TypedVar( id: Identifier, val typ: Type ) extends Variable(id) with TypedHOLTerm {
    override def substituteUnsafe(map: Map[SchematicLabel[?], LisaObject[?]]): Term = 

      if map.contains(this) then map(this).asInstanceOf[Term]
      else 
        val typ2 = typ.substituteUnsafe(map)
        if typ2 == typ then this
        else new TypedVar(id, typ2)

    def toStringFull = s"(${id.name}: $typ)"

    def instType(map: Map[SchematicLabel[?], LisaObject[?]]): TypedVar = new TypedVar(id, typ.substituteUnsafe(map))
    
  }

  def typedvar(using name: sourcecode.Name)(typ: Type): TypedVar = new TypedVar(Identifier(name.value), typ)


  ///////////////////////////////////////
  ///////// Lambda Abstractions /////////
  ///////////////////////////////////////


  class AbstrVar( id: Identifier, val defin:AbstractionDefinition ) extends TypedVar(id, defin.typ){
  }



  trait Abstraction  extends TypedHOLTerm{
    this : Term =>
    override def asTerm: Abstraction & Term = this

    val bound: TypedVar
    val body: Term
    val repr: AbstrVar
    val freeVars: Seq[TypedVar]
    val defin: AbstractionDefinition


    val origin: Term

    val typ: Type


    override def toString = s"${repr.id}($bound. $body)"


    private lazy val t = this * bound
    lazy val betaName = "¢beta_" + repr.id
    // import HOLSteps.{=:= => _, *, given}
    

    lazy val BETA = THM( t =:= body, betaName, summon[sourcecode.Line].value, summon[sourcecode.File].value, InternalStatement) {
      val context = VarsAndFunctions.computeContext(Set(t, body))
      assume((context._1 ++ context._2).toSeq: _*)
      val outType = defin.outType
      val pro = have(defin.bodyProp |- defin.bodyProp) by Restate
      freeVars.reverse.foreach(v => 
        have(lastStep.statement.right.head.asInstanceOf[TypedForall].prop) by Weakening(lastStep of v)
      )
      val aftFreeVars = lastStep
      val h = have((bound::bound.typ) |- (t === body)) by Weakening(aftFreeVars of bound)
      val h2 = have((bound::bound.typ, t::outType, body::outType) |- ((t =:= body) === One) ) by Substitution.ApplyRules(HOLSteps.eqCorrect of (x := t, y := body, A := outType))(h)
      val h3 = have(ProofType(body))
      val h4 = have(((bound::bound.typ, t::outType) |- ((t =:= body) === One)) ++<? h3.statement) by Cut.withParameters(body::outType)(h3, h2)
      val h5 = have(ProofType(t))
      val h6 = have(((bound::bound.typ) |- ((t =:= body) === One)) ++<? h3.statement ++<? h5.statement) by Cut.withParameters(t::outType)(h5, h4)
      val c = thenHave(t =:= body) by Restate
    }

     
  }

  private class AbstractionClosureWithoutFreeVars(
    val reprId: Identifier,
    val bound: TypedVar,
    val body: Term,
    defin: AbstractionDefinition
  ) extends AbstrVar(reprId, defin) with Abstraction{

    override def substituteUnsafe(map: Map[F.SchematicLabel[?], F.LisaObject[?]]): Term = 
      if map.contains(repr) then map(repr).asInstanceOf[Term]
      else 
        val newMap = map - bound
        AbstractionClosureWithoutFreeVars(reprId, bound.instType(newMap), body.substituteUnsafe(newMap), defin.substituteUnsafe(newMap).asInstanceOf)

    val repr: AbstrVar = this
    val freeVars: Seq[TypedVar] = Seq.empty
    val origin = this
    //override def toString = s"(λ$bound. $body)"
  }

  private class AbstractionClosureWithFreeVars(
    val repr: AbstrVar,
    val bound: TypedVar,
    val body: Term,
    val freeVars: Seq[TypedVar],
    val defin: AbstractionDefinition
  ) extends AppliedFunction(freeVars.init.foldLeft(repr: Term)((acc, v) => acc*v), freeVars.last) with Abstraction {

    //override def toString = s"(λ$bound. $body)"
    val origin = AppliedFunction(freeVars.init.foldLeft(repr: Term)((acc, v) => acc*v), freeVars.last)
    val typ = bound.typ |=> defin.outType
    override def substituteUnsafe(map: Map[F.SchematicLabel[?], F.LisaObject[?]]): AppliedFunction = 
      if map.contains(repr) then super.substituteUnsafe(map)
      else 
        val r = InstAbstraction(this, freeVars.map(v => map.getOrElse(v, v)).asInstanceOf)
        val exp = super.substituteUnsafe(map)
        if !(r == exp) then 
          println("r: " + r)
          println("exp: " + exp)
        r
  }

  class InstAbstraction(
    val base: Abstraction,
    val insts: List[Term]
  ) extends AppliedFunction(insts.init.foldLeft(base.repr: Term)((acc, v) => acc @@ v), insts.last) with TypedHOLTerm {
    val typ = base.typ
    override def toString(): String = "I"+super.toString()

  }


  object Abstraction {

    val cache = collection.mutable.Map.empty[(TypedVar, Term), Abstraction & Term]
    def apply(bound: TypedVar, body: Term): Abstraction & Term = {
      cache.getOrElseUpdate((bound, body), {
        val freeVars: Seq[TypedVar] = (body.freeVariables - bound).toSeq.sortBy(_.id.name).collect {
          case v: TypedVar if !v.isInstanceOf[AbstrVar] => v
        }
        val repr = Variable(nextId)
        val inner = tforall(bound, 
            (freeVars.foldLeft[Term](repr) { (acc, v) => 
              acc @@ v
            } @@ bound) === body
          )
        val bodyProp = freeVars.foldLeft[Formula](inner) { (acc, v) => 
          tforall(v, acc)
        }
        val outType = computeType(body)
        val defin = new AbstractionDefinition(repr, bound, body, freeVars, outType, bodyProp)
        if freeVars.isEmpty then new AbstractionClosureWithoutFreeVars(repr.id, bound, body, defin)
        else new AbstractionClosureWithFreeVars(AbstrVar(repr.id, defin), bound, body, freeVars, defin)
      }.asTerm)
    }
  }
  def λ(bound: TypedVar, body: Term) = Abstraction(bound, body)
  
  class AbstractionDefinition(
    val reprVar: Variable,
    val bound: TypedVar,
    val body: Term,
    val freeVars: Seq[TypedVar],
    val outType: Type,
    val bodyProp: Formula
  ) extends AppliedConnector(And, Seq(reprVar is freeVars.foldRight(bound.typ |=> outType)((v, acc) => v.typ |=> acc), bodyProp)) {
    val typ = freeVars.foldRight(bound.typ |=> outType)((v, acc) => v.typ |=> acc)

    override def substituteUnsafe(map: Map[F.SchematicLabel[?], F.LisaObject[?]]): Formula = 
      if map.contains(reprVar) then super.substituteUnsafe(map)
      else 
        val newMap = map - bound -- freeVars
        AbstractionDefinition(
          reprVar, 
          bound.instType(map - bound), 
          body.substituteUnsafe(newMap), 
          freeVars.map(_.instType(newMap)), 
          outType.substituteUnsafe(newMap), 
          bodyProp.substituteUnsafe(newMap)
        )

    
    import HOLSteps.{=:= => _, *, given}
    lazy val elimName = "¢elim_" + reprVar.id
    lazy val elim = Axiom(exists(reprVar, this))



  }

  var j: Int = 0




  object ProofType extends ProofTactic {
    def apply2(using proof: SetTheoryLibrary.Proof)(t:Term): proof.ProofTacticJudgement =
      val context = computeContext(Set(t))
      TypeChecker.typecheck(context._1.toSeq ++ context._2.toSet, t, None)



    def apply(using proof: SetTheoryLibrary.Proof)(t:Term): proof.ProofTacticJudgement = TacticSubproof {
      given SetTheoryLibrary.type = SetTheoryLibrary
      val r = if true then apply2(t) else t match 
        case t: TypedHOLTerm => 
          //println("Good: Caching for " + t)
          val r = t.asInstanceOf[HOLTerm].getTypThmOrElseUpdate {
            have(apply2(t.asTerm))
          }
          lisa.prooflib.SimpleDeducedSteps.Restate.from(r)(r.statement)
        case tc: TypedConstant[?] => 
          //println("Good: Caching for " + t)
          lisa.prooflib.SimpleDeducedSteps.Restate.from(tc.justif)(tc.justif.statement)
        case _ => 
          println("Warning: No caching for " + t)
          println("it has class " + t.getClass())
          apply2(t)
        //val rt = apply2(t)

        val r1 = have(r)
        val r2 = have(r1.statement) by lisa.prooflib.BasicStepTactic.Weakening(r1)
    }

      
  }






  var debug = false
  def computeType(t:Term): Type = 
    val r = {
    t match
      case t: TypedVar => 
        t.typ
      case t: TypedConstant[?] => 
        t.typ match
          case t: Term => t
          case _ => throw new IllegalArgumentException("computeTypes only support subterms typed by terms, not untyped or typed by classes.")
      case t: AppliedFunction => 
        val funcType = computeType(t.func)
        funcType match
          case inType |=> outType => 
            if computeType(t.arg) == inType then outType
            else 
              throw new IllegalArgumentException("Argument " + t.arg + " of function " + t.func + " has type " + computeType(t.arg) + " instead of expected " + inType + ".")
          case funcType => throw new IllegalArgumentException("Function " + t.func + " expected to have function type A |=> B, but has type " + funcType + ". ")
      case AppliedFunctional(label, args) => 
        label match
          case label: TypedConstantFunctional[?] => 
            val labelType = label.typ
            if args.zip(labelType.in).forall((arg, inType) => 
              (inType == any) || {
                val argType = computeType(arg)
                K.isSame((arg is inType).asFormula.underlying, (arg is argType).asFormula.underlying)
              }
            ) then
              val subst = (labelType.args zip args).map((v, a) => (v := a))
              labelType.out match {
                case t: Term => t.substitute(subst: _*)
                case f: (Term**1 |-> Formula) @unchecked => throw new IllegalArgumentException("computeTypes only support subterms typed by terms, not untyped or typed by classes.")
              }
            else 
              val argsTypes = args.map(arg =>
                try computeType(arg)
                catch
                  case e: IllegalArgumentException => "?"
                computeType
              )
              throw new IllegalArgumentException("Function " + label + " has type " + labelType + " but was applied to arguments " + args + " of types " + argsTypes + ".")
          case _ => 
            throw new IllegalArgumentException("computeTypes only support subterms typed by terms, not untyped or typed by classes.")
      case _ => 
        throw new IllegalArgumentException("computeTypes only support fully typed terms. " + t + " is not fully typed.")
      }
      r



  object TypeNonEmptyProof extends ProofTactic {
    val A = variable
    val B = variable
    val nonEmptyFuncSpace = Axiom(exists(x, in(x, B)) ==> exists(x, in(x, (A |=> B))))
    
    def apply(using proof: Proof)(typ: Term): proof.ProofTacticJudgement = TacticSubproof{ ip ?=>
      typ match {
        case ctt: ConstantTypeTerm => have(ctt.nonEmptyThm)
        case v: Variable => 
          val x = freshVariable(Set(v), "x")
          have(exists(x, in(x, v)) |- exists(x, in(x, v)))
        case a |=> b => 
          val x = freshVariable(Set(a, b), "x")
          val s1 = have(TypeNonEmptyProof(b))
          have(exists(x, in(x, a |=> b))) by Tautology.from(s1, nonEmptyFuncSpace of (A := a, B := b))
      }
    }
  }




  class NonEmptyType(val x: Variable, val typ: Term) extends BinderFormula(exists, x, in(x, typ)) {
    override def toString = s"∃${variable}. ${typ}"
  }
  object NonEmptyType {
    def apply(typ: Term): NonEmptyType = 
      val x = freshVariable(Set(typ), "x")
      new NonEmptyType(x, typ)
    def unapply(t: NonEmptyType): Some[(Variable, Term)] = Some(t.x, t.typ)
  }

  // Sequent Syntax

  trait TermSetConverter[T] {
    def apply(t: T): Set[Term]
  }

  given TermSetConverter[Unit] with {
    override def apply(u: Unit): Set[Term] = Set.empty
  }

  given TermSetConverter[EmptyTuple] with {
    override def apply(t: EmptyTuple): Set[Term] = Set.empty
  }

  given [H <: Term, T <: Tuple](using c: TermSetConverter[T]): TermSetConverter[H *: T] with {
    override def apply(t: H *: T): Set[Term] = c.apply(t.tail) + t.head
  }

  given term_to_set[T <: Term]: TermSetConverter[T] with {
    override def apply(f: T): Set[Term] = Set(f)
  }

  given term_iterable_to_set[T <: Term, I <: Iterable[T]]: TermSetConverter[I] with {
    override def apply(s: I): Set[Term] = s.toSet
  }

  private def any2set[A, T <: A](any: T)(using c: TermSetConverter[T]): Set[Term] = c.apply(any)

  extension [A, T1 <: A](left: T1)(using TermSetConverter[T1]) {
    infix def |-(right: Term): HOLSequent = HOLSequent(any2set(left), right)
    infix def ⊢(right: Term): HOLSequent = HOLSequent(any2set(left), right)
  }

  given Conversion[Term, HOLSequent] = HOLSequent(Set(), _)

}
