package lisa.maths.settheory.types

import lisa.prooflib.ProofTacticLib.ProofTactic
import lisa.fol.FOL
import lisa.automation.Tautology
import lisa.fol.FOL.{*, given}
import lisa.prooflib.BasicStepTactic.* 
import lisa.prooflib.SimpleDeducedSteps.*
import lisa.SetTheoryLibrary.{given, *}
import lisa.fol.FOLHelpers.freshVariable


object TypeSystem  {

  val functionSpace: ConstantFunctionLabel[2] = ConstantFunctionLabel("functionSpace", 2)
  extension (t:Term) {
    def |=>(o:Term): Term = functionSpace(t, o)
  }
  val app: ConstantFunctionLabel[2] = ConstantFunctionLabel("app", 2)
  addSymbol(functionSpace)
  addSymbol(app)

  private val f = variable
  private val x = variable
  private val A = variable
  private val B = variable
  val funcspaceAxiom = Axiom(f ∈ functionSpace(A, B) ==> (x ∈ A ==> app(f, x) ∈ B))

  type Class = Term | (Term**1 |-> Formula)

  type SmallClass = Term

  extension [A <: Class](t: Term) {
    def is(clas:A): TypeAssignement[A] = TypeAssignement(t, clas)
    def ::(clas:A): TypeAssignement[A] = TypeAssignement(t, clas)
    def @@(t2: Term): Term = AppliedFunction(t, t2)
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

  given Conversion[TypeAssignement[?], Formula] = _.asFormula

  

  private class TypeAssumptionConstant[A <: Class](val t: Term, val typ:A, formula: ConstantFormula) extends ConstantFormula(formula.id) with TypeAssignement[A]
  private class TypeAssumptionPredicate[A <: Class](val t: Term, val typ:A, formula: AppliedPredicate) extends AppliedPredicate(formula.label, formula.args) with TypeAssignement[A]
  private class TypeAssumptionConnector[A <: Class](val t: Term, val typ:A,  formula: AppliedConnector) extends AppliedConnector(formula.label, formula.args) with TypeAssignement[A]
  private class TypeAssumptionBinder[A <: Class](val t: Term, val typ:A,  formula: BinderFormula) extends BinderFormula(formula.f, formula.bound, formula.body) with TypeAssignement[A]


  type TypingContext = Iterable[TypeAssignement[?]]



  class TypedConstant[A <: Class]
    (id: Identifier, typ: A, val justif: JUSTIFICATION) extends Constant(id) with LisaObject[TypedConstant[A]]  {
    val formula = this is typ
    assert(justif.statement.left.isEmpty && (justif.statement.right.head == formula))

    override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): TypedConstant[A] = this

  }

  // Function Labels


  sealed trait TypedFunctional extends LisaObject[TypedFunctional] {
    this: FunctionLabel[?] =>
    def asLabel: FunctionLabel[?] = this
  }

  class TypedConstantFunctional1[In1 <: Class, Out <: Class](id: Identifier, val inType:In1, val outType: Out, justif: JUSTIFICATION) extends ConstantFunctionLabel[1](id, 1) with LisaObject[TypedConstantFunctional1[In1, Out]] {
    val formula = 
      val x = freshVariable(Seq(inType, outType), "%x")
      forall(x, (x is inType) ==> (this(x) is outType))
    assert(justif.statement.left.isEmpty && justif.statement.right == formula)

    override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): TypedConstantFunctional1[In1, Out] = this
  }

  class TypedConstantFunctional2[In1 <: Class, In2 <: Class, Out <: Class](id: Identifier, val inType1:In1, val inType2: In2, val outType: Out, justif: JUSTIFICATION) extends ConstantFunctionLabel[2](id, 2) with LisaObject[TypedConstantFunctional2[In1, In2, Out]] {
    val formula = 
      val x = freshVariable(Seq(inType1, inType2, outType), "%x")
      val y = freshVariable(Seq(inType1, inType2, outType), "%y")
      forall(x, forall(y, ((x is inType1) /\ (y is inType2)) ==> (this(x, y) is outType)))
    assert(justif.statement.left.isEmpty && justif.statement.right == formula)

    override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): TypedConstantFunctional2[In1, In2, Out] = this
  }

  class TypedConstantFunctional3[In1 <: Class, In2 <: Class, In3 <: Class, Out <: Class](id: Identifier, val inType1:In1, val inType2: In2, val inType3: In3, val outType: Out, justif: JUSTIFICATION) extends ConstantFunctionLabel[3](id, 3) with LisaObject[TypedConstantFunctional3[In1, In2, In3, Out]] {
    val formula = 
      val seq = Seq(inType1, inType2, inType3, outType)
      val x = freshVariable(seq, "%x")
      val y = freshVariable(seq, "%y")
      val z = freshVariable(seq, "%z")
      forall(x, forall(y, forall(z, ((x is inType1) /\ (y is inType2) /\ (z is inType3)) ==> (this(x, y, z) is outType))))
    assert(justif.statement.left.isEmpty && justif.statement.right == formula)

    override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): TypedConstantFunctional3[In1, In2, In3, Out] = this
  }


  class AppliedFunction(func: Term, arg: Term) extends AppliedFunctional(app, Seq(func, arg)) with LisaObject[AppliedFunction] {
    
    override def substituteUnsafe(map: Map[lisa.fol.FOL.SchematicLabel[?], lisa.fol.FOL.LisaObject[?]]): AppliedFunction = this
  }


  


  


  object TypeCheck extends ProofTactic{

    def typecheck(context: List[Formula], term:Term): Unit = 
      val typingAssumptions: Map[Term, List[Class]] = context.collect{
        case TypeAssignement(term, typ) => (term, typ)
      }.groupBy(_._1).map((t, l) => (t, l.map(_._2)))

      def innerTypecheck = ???

      ???

  }
  









}
