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
import lisa.prooflib.OutputManager
import lisa.maths.settheory.SetTheory.singleton
import lisa.maths.settheory.functions.{functional, app}

object TypeLib extends lisa.Main {

  import TypeSystem.*

  val |=> : ConstantFunctionLabel[2] = ConstantFunctionLabel.infix("|=>", 2)
  private inline def  temp = |=>
  extension (t:Term) {
    def |=>(o:Term): Term = TypeLib.temp(t, o)
  }
  val app: ConstantFunctionLabel[2] = lisa.maths.settheory.functions.app
  addSymbol(|=>)

  val f = variable
  val x = variable
  val y = variable
  val z = variable
  val A = variable
  val B = variable
  val F = function[1]
  val funcspaceAxiom = Axiom(f ∈ (A |=> B) ==> (x ∈ A ==> app(f, x) ∈ B))
  val any = DEF(x) --> top


  // A |=> B is the set of functions from A to B
  // C |> D is the functional class of functionals from the class C to the class D
  // F is C |> D desugars into ∀(x, (x is C) => (F(x) is D))

  val testTheorem = Theorem((x is A, f is (A |=> B), F is (A |=> B) |> (A |=> B) ) |- (F(f)*(x) is B)) {
    have(thesis) by TypeChecker.prove
  }

  val  𝔹 = DEF() --> unorderedPair(∅, singleton(∅))

  val empty_in_B = Theorem( (∅ :: 𝔹) ) {
    have( ∅ :: unorderedPair(∅, singleton(∅))) by Tautology.from(pairAxiom of (z := ∅, x := ∅, y := singleton(∅)))
    thenHave(thesis ) by Substitution.ApplyRules(𝔹.shortDefinition)
  }

  val sing_empty_in_B = Theorem( (singleton(∅) :: 𝔹) ) {
    have( singleton(∅) :: unorderedPair(∅, singleton(∅))) by Tautology.from(pairAxiom of (z := singleton(∅), x := ∅, y := singleton(∅)))
    thenHave(thesis ) by Substitution.ApplyRules(𝔹.shortDefinition)
  }

  val Zero = DEF() --> (∅.typedWith(𝔹)(empty_in_B), 𝔹)

  val One = {
    val One = DEF() --> singleton(∅)
    val One_in_B = Theorem( (One :: 𝔹) ) {
      have(thesis) by Substitution.ApplyRules(One.shortDefinition)(sing_empty_in_B)
    }
    One.typedWith(𝔹)(One_in_B)
  }

  val zero_in_B = Theorem( (Zero :: 𝔹) ) {
    have( Zero :: 𝔹) by TypeChecker.prove
  }


}

object TypeSystem  {

  import TypeLib.{
    |=>, app, f, x, A, B, funcspaceAxiom, any, definition, given
  }

  

  type Class = Term | (Term**1 |-> Formula)

  type SmallClass = Term

  case class FunctionalClass(in: Seq[Class], args: Seq[Variable], out: Class, arity: Int) {
    def formula[N <: Arity](f: (Term**N |-> Term)): Formula = 
      val inner = (args.zip(in.toSeq).map((term, typ) => (term is typ).asFormula).reduceLeft((a, b) => a /\ b)) ==> (f.applySeq(args) is out)
      args.foldRight(inner)((v, form) => forall(v, form))

    override def toString(): String = in.map(_.toStringSeparated()).mkString("(", ", ", ")") + " |> " + out.toStringSeparated()
  }
  object FunctionalClass {
    def apply(in: Seq[Class], out: Class, arity: Int): FunctionalClass = FunctionalClass(in, Seq.empty, out, arity)
  }

  extension [N <: Arity](f: (Term**N |-> Term)) {
    def is (typ: FunctionalClass): FunctionalTypeAssignment[N] & Formula  = FunctionalTypeAssignment[N](f, typ).asInstanceOf
  }

  extension[A <: Class] (c: Class) {
    //(1 to arity).map(i => freshVariable(in.toSeq :+ out, "%x" + i))
    def |>(out: Class): FunctionalClass = FunctionalClass(Seq(c),Seq(freshVariable(Seq(out), "$x")), out, 1)
    def |>(out: FunctionalClass): FunctionalClass = 
      val newVar = freshVariable(out.in.toSeq :+ out.out, "$x")
      FunctionalClass(c +: out.in, newVar +: out.args, out.out, out.arity+1)
    def toStringSeparated(): String = c match
      case t: Term => t.toStringSeparated()
      case f: (Term**1 |-> Formula) @unchecked => f.toString()
  }

  extension [A <: Class](t: Term) {
    def is(clas:A): Formula with TypeAssignment[A] = TypeAssignment(t, clas).asInstanceOf[Formula with TypeAssignment[A]]
    def ::(clas:A): Formula with TypeAssignment[A] = TypeAssignment(t, clas).asInstanceOf[Formula with TypeAssignment[A]]
    def @@(t2: Term): AppliedFunction = AppliedFunction(t, t2)
    def *(t2: Term): AppliedFunction = AppliedFunction(t, t2)
  }


  object * {def unapply(t: Term): Option[(Term, Term)] = t match {
    case AppliedFunction(f, a) => Some((f, a))
    case app(f, a) => Some((f, a))
    case _ => None
  }}


  /**
    * A type assumption is a pair of a variable and a type.
    * It is also a formula, equal to the type applied to the variable.
    */
  sealed trait TypeAssignment[A <: Class]{
    this: Formula =>
    val t: Term
    val typ: A
    val asFormula: Formula = this

    override def toString() = 
      t.toStringSeparated() + "::" + typ.toStringSeparated()
    override def toStringSeparated(): String = "(" + toString() + ")"
  }
  object TypeAssignment {

    /**
      * A type assumption is a pair of a variable and a type.
      * It is also a formula, equal to the type applied to the variable.
      */
    def apply[A <: Class](t: Term, typ:A): TypeAssignment[A] = 
      val form = typ match
        case f: Term => in(t, f)
        case f : (Term**1 |-> Formula) @unchecked => 
          ((f: Term**1 |-> Formula)(t): Formula)
      form match
        case f: VariableFormula => 
          throw new IllegalArgumentException("Class formula cannot be a variable formula, as we require a type to have no free variable.")
        case f: ConstantFormula => new TypeAssignmentConstant(t, typ, f)
        case f: AppliedPredicate => new TypeAssignmentPredicate(t, typ, f)
        case f: AppliedConnector => new TypeAssignmentConnector(t, typ, f)
        case f: BinderFormula => new TypeAssignmentBinder(t, typ, f)

    def unapply(ta: Formula): Option[(Term, Class)] = ta match
      case ta: TypeAssignment[?] => Some((ta.t, ta.typ))
      case in(x, set) => Some((x, set))
      case AppliedPredicate(label, args) if label.arity == 1 => Some((args.head, label.asInstanceOf[Term**1 |-> Formula]))
      case _ => None
    
  }
  val is = TypeAssignment

  given [A <: Class]: Conversion[TypeAssignment[A], Formula] = _.asInstanceOf[Formula]
  /*
  given [A <: Class]: Conversion[TypeAssignment[A], Sequent] = ta => Sequent(Set.empty, Set(ta))
  given [A <: Class]: FormulaSetConverter[TypeAssignment[A]] with {
      override def apply(f: TypeAssignment[A]): Set[Formula] = Set(f.asInstanceOf[Formula])
  }
*/
  

  private class TypeAssignmentConstant[A <: Class](val t: Term, val typ:A, formula: ConstantFormula) extends ConstantFormula(formula.id) with TypeAssignment[A]
  private class TypeAssignmentPredicate[A <: Class](val t: Term, val typ:A, formula: AppliedPredicate) extends AppliedPredicate(formula.label, formula.args) with TypeAssignment[A] {
    
    override def substituteUnsafe(map: Map[FOL.SchematicLabel[?], FOL.LisaObject[?]]): FOL.Formula = 
      if map.keySet.exists(_ == typ) then super.substituteUnsafe(map)
      else
        val newArgs = args.map(_.substituteUnsafe(map))
        if newArgs == args then this else 
          val newTyp = (typ: LisaObject[?]).substituteUnsafe(map).asInstanceOf[A]

          TypeAssignmentPredicate(t.substituteUnsafe(map), newTyp, formula.copy(args = newArgs))
  }
  private class TypeAssignmentConnector[A <: Class](val t: Term, val typ:A,  formula: AppliedConnector) extends AppliedConnector(formula.label, formula.args) with TypeAssignment[A]
  private class TypeAssignmentBinder[A <: Class](val t: Term, val typ:A,  formula: BinderFormula) extends BinderFormula(formula.f, formula.bound, formula.body) with TypeAssignment[A]


  type TypingContext = Iterable[TypeAssignment[?]]


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
    val formula = TypeAssignment(this, typ)
    assert(justif.statement.left.isEmpty && (justif.statement.right.head == formula))

    override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): TypedConstant[A] = this
  }

  // Function Labels





  class TypedConstantFunctional[N <: Arity](
    id : Identifier,
    arity: N,
    val typ: FunctionalClass,
    val justif: JUSTIFICATION
  ) extends ConstantFunctionLabel[N](id, arity) with LisaObject[TypedConstantFunctional[N]] {
    
    override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): TypedConstantFunctional[N] = this
  }





  class AppliedFunction(val func: Term, val arg: Term) extends AppliedFunctional(app, Seq(func, arg)) with LisaObject[AppliedFunction] {
    
    override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): AppliedFunction = AppliedFunction(func.substituteUnsafe(map), arg.substituteUnsafe(map))

    override def toString(): String = 
      func match
        case AppliedFunction(af @ AppliedFunctional(label, args), t1) if label.id.name == "=:=" => 
          s"(${t1.toStringSeparated()} =:=_${args.head.toStringSeparated()} ${arg.toStringSeparated()})"
        case _ =>
          func.toStringSeparated() + "*(" + arg.toStringSeparated() + ")"
    override def toStringSeparated(): String = toString()
  }
  object AppliedFunction {
    def unapply(af: AppliedFunctional): Option[(Term, Term)] = af match
      case AppliedFunctional(label, Seq(func, arg)) if label == app => Some((func, arg))
      case _ => None
  }


  
  ///////////////////////
  ///// Definitions /////
  ///////////////////////


  class TypedSimpleConstantDefinition[A <: Class](using om: OutputManager)(fullName: String, line: Int, file: String)(
      val expression: Term,
      out: Variable,
      j: JUSTIFICATION,
      val typ:A
  ) extends SimpleFunctionDefinition[0](fullName, line, file)(lambda[Term, Term](Seq[Variable](), expression).asInstanceOf, out, j) {
    val typingName = "typing_" + fullName
    val typingJudgement = THM( label :: typ, typingName, line, file, InternalStatement)({
      have(expression :: typ) by TypeChecker.prove
      thenHave(thesis) by lisa.automation.Substitution.ApplyRules(getShortDefinition(label).get)
    })
    val typedLabel: TypedConstant[A] = TypedConstant(label.id, typ, typingJudgement)


  }
  object TypedSimpleConstantDefinition {
    def apply[A <: Class](using om: OutputManager)(fullName: String, line: Int, file: String)(expression: Term, typ:A): TypedSimpleConstantDefinition[A] = {
      val intName = "definition_" + fullName
      val out = Variable(freshId(expression.allSchematicLabels.map(_.id), "y"))
      val defThm = THM(ExistsOne(out, out === expression), intName, line, file, InternalStatement)({
        have(lisa.prooflib.SimpleDeducedSteps.simpleFunctionDefinition(lambda(Seq[Variable](), expression), out))
      })
      new TypedSimpleConstantDefinition(fullName, line, file)(expression, out, defThm, typ)
    }
  }
  extension (d: definitionWithVars[0]) {
    inline infix def -->[A<:Class](
          using om: OutputManager, name: sourcecode.FullName, line: sourcecode.Line, file: sourcecode.File)(term:Term, typ: A): TypedConstant[A] =
      TypedSimpleConstantDefinition[A](name.value, line.value, file.value)(term, typ).typedLabel
  }
  
  extension (c: Constant) {
    def typedWith[A <: Class](typ:A)(justif: JUSTIFICATION) : TypedConstant[A] = 
      if justif.statement.right.size != 1  || justif.statement.left.size != 0 || !K.isSame((c is typ).asFormula.underlying, justif.statement.right.head.underlying) then
        throw new IllegalArgumentException(s"A proof of typing of $c must be of the form ${c :: typ}, but the given justification shows ${justif.statement}.")
      else TypedConstant(c.id, typ, justif)
  }








  /////////////////////////
  ///// Type Checking /////
  /////////////////////////

  object TypeChecker extends ProofTactic {
    private val x = variable

    class TypingException(val msg: String) extends Exception(msg)

    def prove(using proof: SetTheoryLibrary.Proof)(bot:lisa.fol.FOL.Sequent): proof.ProofTacticJudgement = 
      val context = bot.left
      var success: proof.ProofTacticJudgement = null
      var typingError: proof.ProofTacticJudgement = null
      bot.right.find(goal =>
        goal match
          case (term is typ) => 
            val ptj = typecheck(using SetTheoryLibrary)(context.toSeq, term, Some(typ))
            if ptj.isValid then
              success = ptj
              true
            else 
              typingError = ptj
              false
          case _ => false
      )
      if success != null then success else if typingError != null then typingError else proof.InvalidProofTactic("The right hand side of the goal must be a typing judgement")
    
    private def fullFlat(context: Seq[Formula]): Seq[Formula] = context.flatMap{
      case AppliedConnector(And, cunj) => fullFlat(cunj)
      case f => Seq(f)
    }

    def typecheck(using lib: SetTheoryLibrary.type, proof: lib.Proof)(context: Seq[Formula], term:Term, typ: Option[Class]): proof.ProofTacticJudgement = 
      val typingAssumptions: Map[Term, Seq[Class]] = fullFlat(context).collect{
        case TypeAssignment(term, typ) => (term, typ)
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
                      if K.isSame((arg is inType).asFormula.underlying, (arg is argType).asFormula.underlying) then
                        have(term is outType) by Tautology.from(
                          funcspaceAxiom of (f := func, x := arg, A:= inType, B:= outType),
                          funcProof,
                            argProof
                        )
                        outType
                      else throw 
                        TypingException("Function " + func + " found to have type " + funcType + ", but argument " + arg + " has type " + argType + " instead of expected " + inType + ".")
                    case Some(typ) if K.isSame((term is typ).asFormula.underlying, (term is outType).asFormula.underlying) =>
                      if K.isSame((arg is inType).asFormula.underlying, (arg is argType).asFormula.underlying) then
                        have(term is outType) by Tautology.from(
                          funcspaceAxiom of (f := func, x := arg, A:= inType, B:= outType),
                          funcProof,
                            argProof
                        )
                        typ
                      else 
                        throw TypingException("Function " + func + " found to have type " + funcType + ", but argument " + arg + " has type " + argType + " instead of expected " + inType + ".")
                      
                    case _ => 
                      throw TypingException("Function " + func + " expected to have function type ? |=> " + typ + ", but has type " + funcType + ". ")
                  case _ => 
                    throw TypingException("Function " + func + " expected to have function type ? |=> " + typ + ", but has type " + funcType + ". Note that terms having multiple different types is only partialy supported.")

              case AppliedFunctional(label, args) => 
                val (argTypes, argTypesProofs) = args.map(arg => 
                  try (innerTypecheck(context2, arg, None), lastStep)
                  catch 
                    case e: TypingException => (any, any.definition of (x := arg)) //if no type could be constructed the normal way, we give it "any"
                ).unzip
                val labelTypes = label match
                  case label: TypedConstantFunctional[?] => 
                    (label.typ, () => label.justif) +: 
                      functionalTypingAssumptions.getOrElse(label, Nil).map(fc => (fc, () => (have( fc.formula(label.asInstanceOf) ) by Restate) ))
                      
                  case _ => functionalTypingAssumptions.getOrElse(label, Nil).map(fc => (fc, () => have( fc.formula(label.asInstanceOf) ) by Restate ))
                  functionalTypingAssumptions.get(label)
                if labelTypes.isEmpty then
                  throw TypingException("Function " + label + " expected to have type (" + argTypes.mkString(", ") + ") |=> ? but is untyped.")
                else
                  typ match
                    case None => 
                      labelTypes.find((labelType, step) =>
                        labelType.arity == args.size && 
                        (args zip argTypes).zip(labelType.in.toSeq).forall((argAndTypes, inType) => 
                          K.isSame((argAndTypes._1 is inType).asFormula.underlying, (argAndTypes._1 is argAndTypes._2).asFormula.underlying) //
                        )
                      ) match 
                        case None =>
                          throw TypingException("Function " + label + " expected to have type (" + argTypes.mkString(", ") + ") |=> ? but is assigned " + labelTypes.mkString(" & ") + ". Note that terms having multiple different types is only partialy supported.")
                        case Some(labelType, step) =>
                          val out: Class = labelType.out
                          
                          val in: Seq[Class] = labelType.in.toSeq
                          //val labelProp = labelType.formula(label.asInstanceOf)
                          val labelPropStatement = step()
                          val labInst = labelPropStatement.of(args: _*)
                          val subst = (labelType.args zip args).map((v, a) => (v := a))
                          val newOut: Class = out match {
                            case t: Term => t.substitute(subst: _*)
                            case f: (Term**1 |-> Formula) @unchecked => f.substitute(subst: _*)
                          }
                          have(term is newOut) by Tautology.from(
                            (argTypesProofs :+ labInst ) : _*
                          )
                          newOut
                    case Some(typValue) => 
                      labelTypes.find((labelType, step) =>
                        labelType.arity == args.size && 
                        (args zip argTypes).zip(labelType.in.toSeq).forall((argAndTypes, inType) => 
                          K.isSame((argAndTypes._1 is inType).asFormula.underlying, (argAndTypes._1 is argAndTypes._2).asFormula.underlying)
                        ) && {
                          val subst = (labelType.args zip args).map((v, a) => (v := a))
                          val newOut: Class = labelType.out match {
                            case t: Term => t.substitute(subst: _*)
                            case f: (Term**1 |-> Formula) @unchecked => f.substitute(subst: _*)
                          }
                          K.isSame((term is newOut).asFormula.underlying, (term is typValue).asFormula.underlying)
                          
                        }
                      ) match
                        case None =>
                          throw TypingException("Function " + label + " expected to have type (" + argTypes.mkString(", ") + ") |=> " + typValue + " but is assigned " + labelTypes.mkString(" & ") + ". Note that terms having multiple different types is only partialy supported.")
                        case Some(labelType, step) =>
                          val out: Class = labelType.out
                          val in: Seq[Class] = labelType.in.toSeq
                          //val labelProp = labelType.formula(label.asInstanceOf)
                          val labelPropStatement = step()
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

              case _: AppliedFunctional => 
                throw Exception("Why is this not handled by the previous case? Scala reports an incomplete match")

          }
          innerTypecheck(typingAssumptions, term, typ)
        }
        catch {
          case e: TypingException => 
            return proof.InvalidProofTactic(e.msg)
        }
      }
      

  }
  









}
