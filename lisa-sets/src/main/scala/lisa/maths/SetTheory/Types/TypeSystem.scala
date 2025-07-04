package lisa.maths.SetTheory.Types

import lisa.utils.prooflib.*
import lisa.utils.prooflib.ProofTacticLib.*
import lisa.utils.prooflib.BasicStepTactic.*
import lisa.utils.prooflib.SimpleDeducedSteps.*
import lisa.automation.Tautology

import lisa.maths.SetTheory.Base.Predef.{given, *}
import lisa.maths.SetTheory.Functions.Predef.*

import annotation.nowarn

/*
object TypeLib extends lisa.Main {
  // import TypeSystem.*

  val f = variable[Ind]
  val x, y, z = variable[Ind]
  val a = variable[Ind]
  val A, B = variable[Ind]
  val F = variable[ClassFunction]
  val any = DEF(λ(x, ⊤))


  // A |=> B is the set of functions from A to B
  // C |> D is the functional class of functionals from the class C to the class D
  // F is C |> D desugars into ∀(x, (x is C) => (F(x) is D))

  /*
  val testTheorem = Theorem((x `is` A, f `is` (A |=> B), F `is` (A |=> B) |> (A |=> B) ) |- (F(f)*(x) `is` B)) {
    have(thesis) by TypeChecker.prove
  }

  val 𝔹 = DEF(unorderedPair(∅, singleton(∅)))

  val `0 : 𝔹` = Theorem(∅ :: 𝔹) {
    have(∅ :: unorderedPair(∅, singleton(∅))) by Tautology.from(pairAxiom of (z := ∅, x := ∅, y := singleton(∅)))
    thenHave(thesis) by Substitution.ApplyRules(𝔹.shortDefinition)
  }

  val `1 : 𝔹` = Theorem(singleton(∅) :: 𝔹) {
    have(singleton(∅) :: unorderedPair(∅, singleton(∅))) by Tautology.from(pairAxiom of (z := singleton(∅), x := ∅, y := singleton(∅)))
    thenHave(thesis) by Substitution.ApplyRules(𝔹.shortDefinition)
  }

  // val Zero = DEF((∅.typedWith(𝔹)(`0 : 𝔹`), 𝔹))

  val One = {
    val One = DEF(singleton(∅))
    val One_in_B = Theorem(One :: 𝔹) {
      have(thesis) by Substitution.ApplyRules(One.shortDefinition)(`1 : 𝔹`)
    }
    One.typedWith(𝔹)(One_in_B)
  }

  val zero_in_B = Theorem(Zero :: 𝔹) {
    have(Zero :: 𝔹) by TypeChecker.prove
  }*/
}

object TypeSystem  {

  import TypeLib.{
    f, x, y, a, any, definition, given
  }

  type Class = Expr[Ind] | Expr[Ind >>: Prop]

  type SmallClass = Expr[Ind]

  case class FunctionalClass(in: Seq[Class], args: Seq[Variable], out: Class, arity: Int) {
    def formula[N <: Arity](f: (Expr[Ind]**N |-> Expr[Ind])): Expr[Prop] =
      val inner = (args.zip(in.toSeq).map((term, typ) => (term `is` typ).asFormula).reduceLeft((a, b) => a /\ b)) ==> (f.applySeq(args) `is` out)
      args.foldRight(inner)((v, form) => forall(v, form))

    override def toString(): String = in.map(_.toStringSeparated()).mkString("(", ", ", ")") + " |> " + out.toStringSeparated()
  }
  object FunctionalClass {
    def apply(in: Seq[Class], out: Class, arity: Int): FunctionalClass = FunctionalClass(in, Seq.empty, out, arity)
  }

  extension [N <: Arity](f: (Expr[Ind]**N |-> Expr[Ind])) {
    def is (typ: FunctionalClass): FunctionalTypeAssignment[N] & Expr[Prop]  = FunctionalTypeAssignment[N](f, typ).asInstanceOf
  }

  extension[A <: Class] (c: Class) {
    //(1 to arity).map(i => freshVariable(in.toSeq :+ out, "%x" + i))
    def |>(out: Class): FunctionalClass = FunctionalClass(Seq(c),Seq(freshVariable(Seq(out), "$x")), out, 1)
    def |>(out: FunctionalClass): FunctionalClass =
      val newVar = freshVariable(out.in.toSeq :+ out.out, "$x")
      FunctionalClass(c +: out.in, newVar +: out.args, out.out, out.arity+1)
    def toStringSeparated(): String = c match
      case t: Expr[Ind] => t.toStringSeparated()
      case f: (Expr[Ind >>: Prop]) @unchecked => f.toString()
  }

  ∅
  extension [A <: Class](t: Expr[Ind]) {
    def is(clas:A): Expr[Prop] & TypeAssignment[A] = TypeAssignment(t, clas).asInstanceOf[Expr[Prop] & TypeAssignment[A]]
    def ::(clas:A): Expr[Prop] & TypeAssignment[A] = TypeAssignment(t, clas).asInstanceOf[Expr[Prop] & TypeAssignment[A]]
    def @@(t2: Expr[Ind]): AppliedFunction = AppliedFunction(t, t2)
    def *(t2: Expr[Ind]): AppliedFunction = AppliedFunction(t, t2)
  }


  object * {def unapply(t: Expr[Ind]): Option[(Expr[Ind], Expr[Ind])] = t match {
    case AppliedFunction(f, a) => Some((f, a))
    case app(f, a) => Some((f, a))
    case _ => None
  }}


  /**
 * A type assumption is a pair of a variable and a type.
 * It is also a formula, equal to the type applied to the variable.
 */
  sealed trait TypeAssignment[A <: Class]{
    this: Expr[Prop] =>
    val t: Expr[Ind]
    val typ: A
    val asFormula: Expr[Prop] = this

    override def toString() =
      t.toStringSeparated() + "::" + typ.toStringSeparated()
    override def toStringSeparated(): String = "(" + toString() + ")"
  }
  object TypeAssignment {

    /**
 * A type assumption is a pair of a variable and a type.
 * It is also a formula, equal to the type applied to the variable.
 */
    def apply[A <: Class](t: Expr[Ind], typ:A): TypeAssignment[A] =
      val form = typ match
        case f: Expr[Ind] => in(t, f)
        case (f : Expr[Ind >>: Prop]) @unchecked =>
          f(t)
      form match
        case f: VariableFormula =>
          throw new IllegalArgumentException("Class formula cannot be a variable formula, as we require a type to have no free variable.")
        case f: ConstantFormula => new TypeAssignmentConstant(t, typ, f)
        case f: AppliedPredicate => new TypeAssignmentPredicate(t, typ, f)
        case f: AppliedConnector => new TypeAssignmentConnector(t, typ, f)
        case f: BinderFormula => new TypeAssignmentBinder(t, typ, f)

    def unapply(ta: Expr[Prop]): Option[(Expr[Ind], Class)] = ta match
      case ta: TypeAssignment[?] => Some((ta.t, ta.typ))
      case in(x, set) => Some((x, set))
      case AppliedPredicate(label, args) if label.arity == 1 => Some((args.head, label.asInstanceOf[Expr[Ind >>: Prop]]))
      case _ => None

  }
  val is = TypeAssignment

  given [A <: Class]: Conversion[TypeAssignment[A], Expr[Prop]] = _.asInstanceOf[Expr[Prop]]
  /*
  given [A <: Class]: Conversion[TypeAssignment[A], Sequent] = ta => Sequent(Set.empty, Set(ta))
  given [A <: Class]: FormulaSetConverter[TypeAssignment[A]] with {
      override def apply(f: TypeAssignment[A]): Set[Expr[Prop]] = Set(f.asInstanceOf[Expr[Prop]])
  }
 */


  private class TypeAssignmentConstant[A <: Class](val t: Expr[Ind], val typ:A, formula: ConstantFormula) extends ConstantFormula(formula.id) with TypeAssignment[A]
  private class TypeAssignmentPredicate[A <: Class](val t: Expr[Ind], val typ:A, formula: AppliedPredicate) extends AppliedPredicate(formula.label, formula.args) with TypeAssignment[A] {

    override def substituteUnsafe(map: Map[FOL.SchematicLabel[?], FOL.LisaObject[?]]): FOL.Expr[Prop] =
      if map.keySet.exists(_ == typ) then super.substituteUnsafe(map)
      else
        val newArgs = args.map(_.substituteUnsafe(map))
        if newArgs == args then this else
          val newTyp = (typ: LisaObject[?]).substituteUnsafe(map).asInstanceOf[A]

          TypeAssignmentPredicate(t.substituteUnsafe(map), newTyp, formula.copy(args = newArgs))
  }
  private class TypeAssignmentConnector[A <: Class](val t: Expr[Ind], val typ:A,  formula: AppliedConnector) extends AppliedConnector(formula.label, formula.args) with TypeAssignment[A]
  private class TypeAssignmentBinder[A <: Class](val t: Expr[Ind], val typ:A,  formula: BinderFormula) extends BinderFormula(formula.f, formula.bound, formula.body) with TypeAssignment[A]


  type TypingContext = Iterable[TypeAssignment[?]]


  sealed trait FunctionalTypeAssignment[N <: Arity]{
    this: Expr[Prop] =>
    val functional: Expr[Ind]**N |-> Expr[Ind]
    val typ: FunctionalClass
    val asFormula: Expr[Prop] = this


    override def toString() = functional.toString() + " : " + typ.toString()
    override def toStringSeparated(): String = "(" + toString + ")"

  }
  object FunctionalTypeAssignment {
    def apply[N <: Arity](functional: Expr[Ind]**N |-> Expr[Ind], typ: FunctionalClass): FunctionalTypeAssignment[N] =
      val form = typ.formula(functional)
      form match
        case fo: VariableFormula =>
          throw new IllegalArgumentException("Class formula cannot be a variable formula, as we require a type to have no free variable.")
        case fo: ConstantFormula => new FunctionalTypeAssignmentConstant(functional, typ, fo)
        case fo: AppliedPredicate => new FunctionalTypeAssignmentPredicate(functional, typ, fo)
        case fo: AppliedConnector => new FunctionalTypeAssignmentConnector(functional, typ, fo)
        case fo: BinderFormula => new FunctionalTypeAssignmentBinder(functional, typ, fo)

    def unapply[N <: Arity](f: Expr[Prop]): Option[((Expr[Ind] ** N) |-> Expr[Ind], FunctionalClass)] =
      f match
        case ta: FunctionalTypeAssignment[N] @unchecked => Some((ta.functional, ta.typ))
        case _ => None
  }
  private class FunctionalTypeAssignmentConstant[N <: Arity](val functional: Expr[Ind]**N |-> Expr[Ind], val typ: FunctionalClass, formula: ConstantFormula) extends ConstantFormula(formula.id) with FunctionalTypeAssignment[N]
  private class FunctionalTypeAssignmentPredicate[N <: Arity](val functional: Expr[Ind]**N |-> Expr[Ind], val typ: FunctionalClass, formula: AppliedPredicate) extends AppliedPredicate(formula.label, formula.args) with FunctionalTypeAssignment[N]
  private class FunctionalTypeAssignmentConnector[N <: Arity](val functional: Expr[Ind]**N |-> Expr[Ind], val typ: FunctionalClass,  formula: AppliedConnector) extends AppliedConnector(formula.label, formula.args) with FunctionalTypeAssignment[N]
  private class FunctionalTypeAssignmentBinder[N <: Arity](val functional: Expr[Ind]**N |-> Expr[Ind], val typ: FunctionalClass,  formula: BinderFormula) extends BinderFormula(formula.f, formula.bound, formula.body) with FunctionalTypeAssignment[N]





  class TypedConstant[A <: Class]
    (id: Identifier, val typ: A, val justif: JUSTIFICATION) extends Constant(id) with LisaObject[TypedConstant[A]]  {
    val formula = TypeAssignment(this, typ)
    assert(justif.statement.left.isEmpty && (justif.statement.right.head == formula))

    override def substituteUnsafe(map: Map[lisa.utils.fol.FOL.SchematicLabel[?], lisa.utils.fol.FOL.LisaObject[?]]): TypedConstant[A] = this
  }

  // Function Labels





  class TypedConstantFunctional[N <: Arity](
    id : Identifier,
    arity: N,
    val typ: FunctionalClass,
    val justif: JUSTIFICATION
  ) extends ConstantFunctionLabel[N](id, arity) with LisaObject[TypedConstantFunctional[N]] {

    override def substituteUnsafe(map: Map[lisa.utils.fol.FOL.SchematicLabel[?], lisa.utils.fol.FOL.LisaObject[?]]): TypedConstantFunctional[N] = this
  }





  class AppliedFunction(val func: Expr[Ind], val arg: Expr[Ind]) extends AppliedFunctional(app, Seq(func, arg)) with LisaObject[AppliedFunction] {

    override def substituteUnsafe(map: Map[lisa.utils.fol.FOL.SchematicLabel[?], lisa.utils.fol.FOL.LisaObject[?]]): AppliedFunction = AppliedFunction(func.substituteUnsafe(map), arg.substituteUnsafe(map))

    override def toString(): String =
      func match
        case AppliedFunction(af @ AppliedFunctional(label, args), t1) if label.id.name == "=:=" =>
          s"(${t1.toStringSeparated()} =:=_${args.head.toStringSeparated()} ${arg.toStringSeparated()})"
        case _ =>
          func.toStringSeparated() + "*(" + arg.toStringSeparated() + ")"
    override def toStringSeparated(): String = toString()
  }
  object AppliedFunction {
    def unapply(af: AppliedFunctional): Option[(Expr[Ind], Expr[Ind])] = af match
      case AppliedFunctional(label, Seq(func, arg)) if label == app => Some((func, arg))
      case _ => None
  }



  ///////////////////////
  ///// Definitions /////
  ///////////////////////


  class TypedSimpleConstantDefinition[A <: Class](using om: OutputManager)(fullName: String, line: Int, file: String)(
      val expression: Expr[Ind],
      out: Variable,
      j: JUSTIFICATION,
      val typ:A
  ) extends SimpleFunctionDefinition[0](fullName, line, file)(lambda[Expr[Ind], Expr[Ind]](Seq[Variable](), expression).asInstanceOf, out, j) {
    val typingName = "typing_" + fullName
    val typingJudgement = THM( label :: typ, typingName, line, file, InternalStatement)({
      have(expression :: typ) by TypeChecker.prove
      thenHave(thesis) by lisa.automation.Substitution.ApplyRules(getShortDefinition(label).get)
    })
    val typedLabel: TypedConstant[A] = TypedConstant(label.id, typ, typingJudgement)


  }
  object TypedSimpleConstantDefinition {
    def apply[A <: Class](using om: OutputManager)(fullName: String, line: Int, file: String)(expression: Expr[Ind], typ:A): TypedSimpleConstantDefinition[A] = {
      val intName = "definition_" + fullName
      val out = Variable(freshId(expression.allSchematicLabels.map(_.id), "y"))
      val defThm = THM(ExistsOne(out, out === expression), intName, line, file, InternalStatement)({
        have(lisa.utils.prooflib.SimpleDeducedSteps.simpleFunctionDefinition(lambda(Seq[Variable](), expression), out))
      })
      new TypedSimpleConstantDefinition(fullName, line, file)(expression, out, defThm, typ)
    }
  }


  extension (d: definitionWithVars[0]) {
    @nowarn
    inline infix def -->[A<:Class](
          using om: OutputManager, name: sourcecode.FullName, line: sourcecode.Line, file: sourcecode.File)(term:Expr[Ind], typ: A): TypedConstant[A] =
      TypedSimpleConstantDefinition[A](name.value, line.value, file.value)(term, typ).typedLabel
  }


  extension (c: Constant) {
    def typedWith[A <: Class](typ:A)(justif: JUSTIFICATION) : TypedConstant[A] =
      if justif.statement.right.size != 1  || justif.statement.left.size != 0 || !K.isSame((c `is` typ).asFormula.underlying, justif.statement.right.head.underlying) then
        throw new IllegalArgumentException(s"A proof of typing of $c must be of the form ${c :: typ}, but the given justification shows ${justif.statement}.")
      else TypedConstant(c.id, typ, justif)
  }








  /////////////////////////
  ///// Type Checking /////
  /////////////////////////

  object TypeChecker extends ProofTactic {
    private val x = variable

    class TypingException(val msg: String) extends Exception(msg)

    def prove(using proof: SetTheoryLibrary.Proof)(bot:lisa.utils.fol.FOL.Sequent): proof.ProofTacticJudgement =
      val context = bot.left
      var success: proof.ProofTacticJudgement = null
      var typingError: proof.ProofTacticJudgement = null
      bot.right.find(goal =>
        goal match
          case (term `is` typ) =>
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

    private def fullFlat(context: Seq[Expr[Prop]]): Seq[Expr[Prop]] = context.flatMap{
      case AppliedConnector(And, cunj) => fullFlat(cunj)
      case f => Seq(f)
    }

    def typecheck(using lib: SetTheoryLibrary.type, proof: lib.Proof)(context: Seq[Expr[Prop]], term:Expr[Ind], typ: Option[Class]): proof.ProofTacticJudgement =
      val typingAssumptions: Map[Expr[Ind], Seq[Class]] = fullFlat(context).collect{
        case TypeAssignment(term, typ) => (term, typ)
      }.groupBy(_._1).map((t, l) => (t, l.map(_._2)))

      val functionalTypingAssumptions: Map[(? |-> Expr[Ind]), Seq[FunctionalClass]] = context.collect{
        case FunctionalTypeAssignment(func, typ) => (func, typ)
      }.groupBy(_._1).map((func, l) => (func, l.map(_._2)))

      TacticSubproof {
        context.foreach(assume(_))
        try {

          def innerTypecheck(context2: Map[Expr[Ind], Seq[Class]], term:Expr[Ind], typ:Option[Class]): Class= {
            val possibleTypes = typingAssumptions.getOrElse(term, Nil)
            if typ == Some(any) then
              have(term `is` any) by Restate.from(TypeLib.any.definition of (x := term))
              any
            else if typ.isEmpty && possibleTypes.size >=1 then
              have(term `is` possibleTypes.head) by Restate
              possibleTypes.head
            else if (typ.nonEmpty && possibleTypes.contains(typ.get)) then
              have(term `is` typ.get) by Restate
              typ.get
            else term match
              case tc: TypedConstant[?] =>
                if typ.isEmpty then
                  have(tc `is` tc.typ) by Restate.from(tc.justif)
                  tc.typ
                else if K.isSame((tc `is` typ.get).asFormula.underlying, (tc `is` tc.typ).asFormula.underlying) then
                  have(tc `is` typ.get) by Restate.from(tc.justif)
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
                      if K.isSame((arg `is` inType).asFormula.underlying, (arg `is` argType).asFormula.underlying) then
                        have(term `is` outType) by Tautology.from(
                          functionFromApplication of (f := func, a := arg, x := inType, y := outType),
                          funcProof,
                            argProof
                        )
                        outType
                      else throw
                        TypingException("Function " + func + " found to have type " + funcType + ", but argument " + arg + " has type " + argType + " instead of expected " + inType + ".")
                    case Some(typ) if K.isSame((term `is` typ).asFormula.underlying, (term `is` outType).asFormula.underlying) =>
                      if K.isSame((arg `is` inType).asFormula.underlying, (arg `is` argType).asFormula.underlying) then
                        have(term `is` outType) by Tautology.from(
                          functionFromApplication of (f := func, a := arg, x := inType, y := outType),
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
                          K.isSame((argAndTypes._1 `is` inType).asFormula.underlying, (argAndTypes._1 `is` argAndTypes._2).asFormula.underlying) //
                        )
                      ) match
                        case None =>
                          throw TypingException("Function " + label + " expected to have type (" + argTypes.mkString(", ") + ") |=> ? but is assigned " + labelTypes.mkString(" & ") + ". Note that terms having multiple different types is only partialy supported.")
                        case Some(labelType, step) =>
                          val out: Class = labelType.out

                          val in: Seq[Class] = labelType.in.toSeq
                          //val labelProp = labelType.formula(label.asInstanceOf)
                          val labelPropStatement = step()
                          val labInst = labelPropStatement.of(args*)
                          val subst = (labelType.args zip args).map((v, a) => (v := a))
                          val newOut: Class = out match {
                            case t: Expr[Ind] => t.substitute(subst*)
                            case f: (Expr[Ind >>: Prop]) @unchecked => f.substitute(subst*)
                          }
                          have(term `is` newOut) by Tautology.from(
                            (argTypesProofs :+ labInst )*
                          )
                          newOut
                    case Some(typValue) =>
                      labelTypes.find((labelType, step) =>
                        labelType.arity == args.size &&
                        (args zip argTypes).zip(labelType.in.toSeq).forall((argAndTypes, inType) =>
                          K.isSame((argAndTypes._1 `is` inType).asFormula.underlying, (argAndTypes._1 `is` argAndTypes._2).asFormula.underlying)
                        ) && {
                          val subst = (labelType.args zip args).map((v, a) => (v := a))
                          val newOut: Class = labelType.out match {
                            case t: Expr[Ind] => t.substitute(subst*)
                            case f: (Expr[Ind >>: Prop]) @unchecked => f.substitute(subst*)
                          }
                          K.isSame((term `is` newOut).asFormula.underlying, (term `is` typValue).asFormula.underlying)

                        }
                      ) match
                        case None =>
                          throw TypingException("Function " + label + " expected to have type (" + argTypes.mkString(", ") + ") |=> " + typValue + " but is assigned " + labelTypes.mkString(" & ") + ". Note that terms having multiple different types is only partialy supported.")
                        case Some(labelType, step) =>
                          val out: Class = labelType.out
                          val in: Seq[Class] = labelType.in.toSeq
                          //val labelProp = labelType.formula(label.asInstanceOf)
                          val labelPropStatement = step()
                          have(term `is` typValue) by Tautology.from(
                            (argTypesProofs :+ labelPropStatement.of(args*) )*
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

 */
