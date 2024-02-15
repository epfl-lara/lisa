package lisa.maths.settheory.types

import lisa.prooflib.ProofTacticLib.*
import lisa.fol.FOL
import lisa.automation.Tautology
import lisa.fol.FOL.{*, given}
import lisa.prooflib.BasicStepTactic.* 
import lisa.prooflib.SimpleDeducedSteps.*
import lisa.SetTheoryLibrary.{given, *}
import lisa.SetTheoryLibrary
import lisa.kernel.proof.SequentCalculus.SCProofStep
import lisa.maths.settheory.SetTheory.functional

object TypeLib extends lisa.Main {

  import TypeSystem.*

  val |=> : ConstantFunctionLabel[2] = ConstantFunctionLabel.infix("|=>", 2)
  private inline def  temp = |=>
  extension (t:Term) {
    def |=>(o:Term): Term = TypeLib.temp(t, o)
  }
  val app: ConstantFunctionLabel[2] = ConstantFunctionLabel("app", 2)
  addSymbol(|=>)
  addSymbol(app)

  val f = variable
  val x = variable
  val A = variable
  val B = variable
  val F = function[1]
  val funcspaceAxiom = Axiom(f ∈ (A |=> B) ==> (x ∈ A ==> app(f, x) ∈ B))
  val any = DEF(x) --> top


  // A |=> B is the set of functions from A to B
  // C |> D is the functional class of functionals from the class C to the class D
  // F is C |> D desugars into ∀(x, (x is C) => (F(x) is D))

  val testTheorem = Theorem((x is A, f is (A |=> B), F is (A |=> B) |> (A |=> B) ) |- (F(f).@@(x) is B)) {
    have(thesis) by TypeCheck.prove
  }


}

object TypeSystem  {

  import TypeLib.{
    |=>, app, f, x, A, B, funcspaceAxiom, any, definition, given
  }

  

  type Class = Term | (Term**1 |-> Formula)

  type SmallClass = Term

  case class FunctionalClass(in: Seq[Class], out: Class, arity: Int) {
    def formula[N <: Arity](f: (Term**N |-> Term)): Formula = 
      val args = (1 to arity).map(i => freshVariable(in.toSeq :+ out, "%x" + i))
      val inner = (args.zip(in.toSeq).map((term, typ) => (term is typ).asFormula).reduceLeft((a, b) => a /\ b)) ==> (f.applySeq(args) is out)
      args.foldRight(inner)((v, form) => forall(v, form))

    override def toString(): String = in.map(_.toStringSeparated()).mkString("(", ", ", ")") + " |> " + out.toStringSeparated()
  }

  extension [N <: Arity](f: (Term**N |-> Term)) {
    def is (typ: FunctionalClass): FunctionalTypeAssignment[N] & Formula  = FunctionalTypeAssignment[N](f, typ).asInstanceOf
  }

  extension[A <: Class] (c: Class) {
    def |>(out: Class): FunctionalClass = FunctionalClass(Seq(c), out, 1)
    def |>(out: FunctionalClass): FunctionalClass = FunctionalClass(c +: out.in, out.out, out.arity+1)
    def toStringSeparated(): String = c match
      case t: Term => t.toStringSeparated()
      case f: (Term**1 |-> Formula) @unchecked => f.toStringSeparated()
  }

  extension [A <: Class](t: Term) {
    def is(clas:A): TypeAssignement[A] & Formula = TypeAssignement(t, clas).asInstanceOf
    def ::(clas:A): TypeAssignement[A] & Formula = TypeAssignement(t, clas).asInstanceOf
    def @@(t2: Term): AppliedFunction = AppliedFunction(t, t2)
  }


  /**
    * A type assumption is a pair of a variable and a type.
    * It is also a formula, equal to the type applied to the variable.
    */
  sealed trait TypeAssignement[A <: Class]{
    this: Formula =>
    val t: Term
    val typ: A
    val asFormula: Formula = this

    override def toString() = t.toStringSeparated() + " ∈ " + typ.toStringSeparated()
    override def toStringSeparated(): String = "(" + toString + ")"
  }
  object TypeAssignement {

    /**
      * A type assumption is a pair of a variable and a type.
      * It is also a formula, equal to the type applied to the variable.
      */
    def apply[A <: Class](t: Term, typ:A): TypeAssignement[A] = 
      val form = typ match
        case f: Term => in(t, f)
        case f : (Term**1 |-> Formula) @unchecked => f(t)
      form match
        case f: VariableFormula => 
          throw new IllegalArgumentException("Class formula cannot be a variable formula, as we require a type to have no free variable.")
        case f: ConstantFormula => new TypeAssumptionConstant(t, typ, f)
        case f: AppliedPredicate => new TypeAssumptionPredicate(t, typ, f)
        case f: AppliedConnector => new TypeAssumptionConnector(t, typ, f)
        case f: BinderFormula => new TypeAssumptionBinder(t, typ, f)

    def unapply(ta: Formula): Option[(Term, Class)] = ta match
      case ta: TypeAssignement[?] => Some((ta.t, ta.typ))
      case in(x, set) => Some((x, set))
      case AppliedPredicate(label, args) if label.arity == 1 => Some((args.head, label.asInstanceOf[Term**1 |-> Formula]))
      case _ => None
    
  }
  val is = TypeAssignement

  given [A <: Class]: Conversion[TypeAssignement[A], Formula] = _.asInstanceOf[Formula]
  /*
  given [A <: Class]: Conversion[TypeAssignement[A], Sequent] = ta => Sequent(Set.empty, Set(ta))
  given [A <: Class]: FormulaSetConverter[TypeAssignement[A]] with {
      override def apply(f: TypeAssignement[A]): Set[Formula] = Set(f.asInstanceOf[Formula])
  }
*/
  

  private class TypeAssumptionConstant[A <: Class](val t: Term, val typ:A, formula: ConstantFormula) extends ConstantFormula(formula.id) with TypeAssignement[A]
  private class TypeAssumptionPredicate[A <: Class](val t: Term, val typ:A, formula: AppliedPredicate) extends AppliedPredicate(formula.label, formula.args) with TypeAssignement[A]
  private class TypeAssumptionConnector[A <: Class](val t: Term, val typ:A,  formula: AppliedConnector) extends AppliedConnector(formula.label, formula.args) with TypeAssignement[A]
  private class TypeAssumptionBinder[A <: Class](val t: Term, val typ:A,  formula: BinderFormula) extends BinderFormula(formula.f, formula.bound, formula.body) with TypeAssignement[A]


  type TypingContext = Iterable[TypeAssignement[?]]


  sealed trait FunctionalTypeAssignment[N <: Arity]{
    this: Formula =>
    val functional: Term**N |-> Term
    val typ: FunctionalClass
    val asFormula: Formula = this


    override def toString() = functional.toString() + " : " + typ.toString()
    override def toStringSeparated(): String = "(" + toString + ")"

  }
  object FunctionalTypeAssignment {
    def apply[N <: Arity](functional: Term**N |-> Term, typ: FunctionalClass): FunctionalTypeAssignment[N] = 
      val form = typ.formula(functional)
      form match
        case fo: VariableFormula => 
          throw new IllegalArgumentException("Class formula cannot be a variable formula, as we require a type to have no free variable.")
        case fo: ConstantFormula => new FunctionalTypeAssignmentConstant(functional, typ, fo)
        case fo: AppliedPredicate => new FunctionalTypeAssignmentPredicate(functional, typ, fo)
        case fo: AppliedConnector => new FunctionalTypeAssignmentConnector(functional, typ, fo)
        case fo: BinderFormula => new FunctionalTypeAssignmentBinder(functional, typ, fo)

    def unapply[N <: Arity](f: Formula): Option[((Term ** N) |-> Term, FunctionalClass)] = 
      f match 
        case ta: FunctionalTypeAssignment[N] => Some((ta.functional, ta.typ))
        case _ => None
  }
  private class FunctionalTypeAssignmentConstant[N <: Arity](val functional: Term**N |-> Term, val typ: FunctionalClass, formula: ConstantFormula) extends ConstantFormula(formula.id) with FunctionalTypeAssignment[N]
  private class FunctionalTypeAssignmentPredicate[N <: Arity](val functional: Term**N |-> Term, val typ: FunctionalClass, formula: AppliedPredicate) extends AppliedPredicate(formula.label, formula.args) with FunctionalTypeAssignment[N]
  private class FunctionalTypeAssignmentConnector[N <: Arity](val functional: Term**N |-> Term, val typ: FunctionalClass,  formula: AppliedConnector) extends AppliedConnector(formula.label, formula.args) with FunctionalTypeAssignment[N]
  private class FunctionalTypeAssignmentBinder[N <: Arity](val functional: Term**N |-> Term, val typ: FunctionalClass,  formula: BinderFormula) extends BinderFormula(formula.f, formula.bound, formula.body) with FunctionalTypeAssignment[N]





  class TypedConstant[A <: Class]
    (id: Identifier, val typ: A, val justif: JUSTIFICATION) extends Constant(id) with LisaObject[TypedConstant[A]]  {
    val formula = TypeAssignement(this, typ)
    assert(justif.statement.left.isEmpty && (justif.statement.right.head == formula))

    override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): TypedConstant[A] = this
  }

  // Function Labels




  class TypedConstantFunctional[N <: Arity](
    id : Identifier, arity: N, val typ: FunctionalClass, val justif: JUSTIFICATION
  ) extends ConstantFunctionLabel[N](id, arity) with LisaObject[TypedConstantFunctional[N]] {
    
    override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): TypedConstantFunctional[N] = this
  }





  class AppliedFunction(func: Term, arg: Term) extends AppliedFunctional(app, Seq(func, arg)) with LisaObject[AppliedFunction] {
    
    override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): AppliedFunction = this
  }
  object AppliedFunction {
    def unapply(af: AppliedFunctional): Option[(Term, Term)] = af match
      case AppliedFunctional(label, Seq(func, arg)) if label == app => Some((func, arg))
      case _ => None
  }


  


  


  object TypeCheck extends ProofTactic {
    val x = variable

    class TypingException(val msg: String) extends Exception(msg)

    def prove(using proof: SetTheoryLibrary.Proof)(bot:lisa.fol.FOL.Sequent): proof.ProofTacticJudgement = 
      val context = bot.left
      var success: proof.ProofTacticJudgement = null
      var typingError: proof.ProofTacticJudgement = null
      bot.right.find(goal =>
        goal match
          case (term is typ) => 
            val ptj = typecheck(using SetTheoryLibrary)(context.toSeq, term, typ)
            if ptj.isValid then
              success = ptj
              true
            else 
              typingError = ptj
              false
          case _ => false
      )
      if success != null then success else if typingError != null then typingError else proof.InvalidProofTactic("The right hand side of the goal must be a typing judgement")
    

    def typecheck(using lib: SetTheoryLibrary.type, proof: lib.Proof)(context: Seq[Formula], term:Term, typ: Class): proof.ProofTacticJudgement = 
      val typingAssumptions: Map[Term, Seq[Class]] = context.collect{
        case TypeAssignement(term, typ) => (term, typ)
      }.groupBy(_._1).map((t, l) => (t, l.map(_._2)))
      
      val functionalTypingAssumptions: Map[(? |-> Term), Seq[FunctionalClass]] = context.collect{
        case FunctionalTypeAssignment(func, typ) => (func, typ)
      }.groupBy(_._1).map((func, l) => (func, l.map(_._2)))

      TacticSubproof {
        context.foreach(assume(_))
        try {

          def innerTypecheck(context2: Map[Term, Seq[Class]], term:Term, typ:Option[Class]): Class= {
            val possibleTypes = typingAssumptions.getOrElse(term, Nil)
            if typ == Some(any) then 
              have(term is any) by Restate.from(TypeLib.any.definition of (x := term))
              any
            else if typ.isEmpty && possibleTypes.size >=1 then
              have(term is possibleTypes.head) by Restate
              possibleTypes.head
            else if (typ.nonEmpty && possibleTypes.contains(typ.get)) then
              have(term is typ.get) by Restate
              typ.get
            else term match
              case tc: TypedConstant[?] => 
                if typ.isEmpty then
                  have(tc is tc.typ) by Restate.from(tc.justif)
                  tc.typ
                else if K.isSame((tc is typ.get).asFormula.underlying, (tc is tc.typ).asFormula.underlying) then
                  have(tc is typ.get) by Restate.from(tc.justif)
                  typ.get
                else throw TypingException("Constant " + tc + " expected to be of type " + typ + " but has type " + tc.typ + ".")

              case AppliedFunction(func, arg) =>
                val funcType = innerTypecheck(context2, func, None)
                val funcProof = lastStep
                val argType = innerTypecheck(context2, arg, None)
                val argProof = lastStep
                funcType match
                  case inType |=> outType => typ match
                    case None => 
                      if K.isSame((arg is inType).asFormula.underlying, (arg is arg).asFormula.underlying) then
                        println(term)
                        have(term is outType) by Tautology.from(
                          funcspaceAxiom of (f := func, x := arg, A:= inType, B:= outType),
                          funcProof,
                            argProof
                        )
                        outType
                      else throw TypingException("Function " + func + " found to have type " + funcType + ", but argument " + arg + " has type " + argType + " instead of expected " + inType + ".")
                    case Some(typ) if K.isSame((term is typ).asFormula.underlying, (term is outType).asFormula.underlying) =>
                      if K.isSame((arg is inType).asFormula.underlying, (arg is argType).asFormula.underlying) then
                        println(term)
                        have(term is outType) by Tautology.from(
                          funcspaceAxiom of (f := func, x := arg, A:= inType, B:= outType),
                          funcProof,
                            argProof
                        )
                        typ
                      else 
                        println("error")
                        throw TypingException("Function " + func + " found to have type " + funcType + ", but argument " + arg + " has type " + argType + " instead of expected " + inType + ".")
                      
                    case _ => 
                      throw TypingException("Function " + func + " expected to have function type ? |=> " + typ + ", but has type " + funcType + ". ")
                  case _ => 
                    throw TypingException("Function " + func + " expected to have function type ? |=> " + typ + ", but has type " + funcType + ". Note that terms having multiple different types is only partialy supported.")

              case AppliedFunctional(label, args) => 
                val (argTypes, argTypesProofs) = args.map(arg => (innerTypecheck(context2, arg, None), lastStep)).unzip
                functionalTypingAssumptions.get(label) match // TODO handle TypedConstantFunctional
                  case None => 
                    throw TypingException("Function " + label + " expected to have type (" + argTypes.mkString(", ") + ") |=> ? but is untyped.")
                  case Some(labelTypes) =>
                    typ match
                      case None => 
                        val labelType = labelTypes.find(labelType =>
                          labelType.arity == args.size && 
                          (args zip argTypes).zip(labelType.in.toSeq).forall((argAndTypes, inType) => 
                            K.isSame((argAndTypes._1 is inType).asFormula.underlying, (argAndTypes._1 is argAndTypes._2).asFormula.underlying)
                          )
                        )
                        if labelType.isEmpty then
                          throw TypingException("Function " + label + " expected to have type (" + argTypes.mkString(", ") + ") |=> ? but is assigned " + labelTypes.mkString(" & ") + ". Note that terms having multiple different types is only partialy supported.")
                        else 
                          val out: Class = labelType.get.out
                          val in: Seq[Class] = labelType.get.in.toSeq
                          val labelProp = labelType.get.formula(label.asInstanceOf)
                          val labelPropStatement = have( labelProp ) by Restate
                          have(term is out) by Tautology.from(
                            (argTypesProofs :+ labelPropStatement.of(args: _*) ) : _*
                          )
                          out
                      case Some(typValue) => val labelType = labelTypes.find(labelType =>
                          labelType.arity == args.size && 
                          (args zip argTypes).zip(labelType.in.toSeq).forall((argAndTypes, inType) => 
                            K.isSame((argAndTypes._1 is inType).asFormula.underlying, (argAndTypes._1 is argAndTypes._2).asFormula.underlying)
                          ) &&
                          K.isSame((term is labelType.out).asFormula.underlying, (term is typValue).asFormula.underlying)
                        )
                        if labelType.isEmpty then
                          throw TypingException("Function " + label + " expected to have type (" + argTypes.mkString(", ") + ") |=> " + typValue + " but is assigned " + labelTypes.mkString(" & ") + ". Note that terms having multiple different types is only partialy supported.")
                        else 
                          val out: Class = labelType.get.out
                          val in: Seq[Class] = labelType.get.in.toSeq
                          val labelProp = labelType.get.formula(label.asInstanceOf)
                          val labelPropStatement = have( labelProp ) by Restate
                          have(term is typValue) by Tautology.from(
                            (argTypesProofs :+ labelPropStatement.of(args: _*) ) : _*
                          )
                          typValue

              case v: Variable => 
                if possibleTypes.isEmpty then 
                  throw TypingException("Variable " + v + " expected to be of type " + typ + " but is untyped.")
                else throw TypingException("Variable " + v + " expected to be of type " + typ + " but is assigned " + possibleTypes.mkString(" & ") + ".")

              case c: Constant => 
                if possibleTypes.isEmpty then 
                  throw TypingException("Constant " + c + " expected to be of type " + typ + " but is untyped.")
                else throw TypingException("Constant " + c + " expected to be of type " + typ + " but is assigned " + possibleTypes.mkString(" & ") + ".")

          }
          innerTypecheck(typingAssumptions, term, Some(typ))
        }
        catch {
          case e: TypingException => 
            return proof.InvalidProofTactic(e.msg)
        }
      }
      

  }
  









}
