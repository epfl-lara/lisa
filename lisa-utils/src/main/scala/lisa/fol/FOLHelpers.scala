package lisa.fol

import lisa.fol.FOL.*
import lisa.kernel.fol.FOL.Identifier
import lisa.utils.FOLParser
import lisa.utils.K
import lisa.utils.LisaException

/**
 * A helper file that provides various syntactic sugars for LISA's FOL and proofs. Best imported through utilities.Helpers
 * Usage:
 * <pre>
 * import utilities.Helpers.*
 * </pre>
 * or
 * <pre>
 * extends utilities.KernelHelpers.*
 * </pre>
 */
object FOLHelpers {
  export lisa.utils.KernelHelpers.{freshId, nFreshId, given_Conversion_String_Identifier, given_Conversion_Identifier_String, given_Conversion_Boolean_List_String_Option}

  /////////////////
  // FOL helpers //
  /////////////////

  /* Conversions */
  // Conversions to lambdaExpression's
  given [T <: LisaObject[T], R <: LisaObject[R]]: Conversion[R, LambdaExpression[T, R, 0]] = LambdaExpression[T, R, 0](Seq(), _, 0)
  given [T <: LisaObject[T], R <: LisaObject[R]]: Conversion[(SchematicLabel[T], R), LambdaExpression[T, R, 1]] = a => LambdaExpression(Seq(a._1), a._2, 1)
  given [T <: LisaObject[T], R <: LisaObject[R], N <: Arity]: Conversion[(SchematicLabel[T] ** N, R), LambdaExpression[T, R, N]] = a => {
    val s = a._1.toSeq
    LambdaExpression(s, a._2, s.length.asInstanceOf)
  }

  given [T <: LisaObject[T]]: Conversion[T, T ** 1] = **.apply[T, 1](_)

  given Conversion[Int, Arity] = _.asInstanceOf

  /*
  extension [I, O <: LisaObject[O]] (e: (I ** 0) |-> O) {
    def apply() = e.apply(EmptyTuple)
  }
   */

  // helpers to create new schematic symbols, fetching the scala name of the variable.
  def variable(using name: sourcecode.Name): Variable = Variable(name.value)
  def function[N <: Arity: ValueOf](using name: sourcecode.Name): SchematicFunctionLabel[N] = SchematicFunctionLabel[N](name.value, valueOf[N])
  def formulaVariable(using name: sourcecode.Name): VariableFormula = VariableFormula(name.value)
  def predicate[N <: Arity: ValueOf](using name: sourcecode.Name): SchematicPredicateLabel[N] = SchematicPredicateLabel[N](name.value, valueOf[N])
  def connector[N <: Arity: ValueOf](using name: sourcecode.Name): SchematicConnectorLabel[N] = SchematicConnectorLabel[N](name.value, valueOf[N])

  ////////////////////////////////////////
  //    Kernel to Front transformers    //
  ////////////////////////////////////////

  // TermLabel
  def asFrontLabel(tl: K.TermLabel): TermLabel[?] = tl match
    case tl: K.ConstantFunctionLabel => asFrontLabel(tl)
    case tl: K.SchematicTermLabel => asFrontLabel(tl)
  def asFrontLabel[N <: Arity](cfl: K.ConstantFunctionLabel): ConstantTermLabelOfArity[N] = cfl.arity.asInstanceOf[N] match
    case n: 0 => Constant(cfl.id)
    case n: N => ConstantFunctionLabel[N](cfl.id, n)
  def asFrontLabel(stl: K.SchematicTermLabel): SchematicTermLabel[?] = stl match
    case v: K.VariableLabel => asFrontLabel(v)
    case v: K.SchematicFunctionLabel => asFrontLabel(v)
  def asFrontLabel[N <: Arity](sfl: K.SchematicFunctionLabel): SchematicFunctionLabel[N] =
    SchematicFunctionLabel(sfl.id, sfl.arity.asInstanceOf)
  def asFrontLabel(v: K.VariableLabel): Variable = Variable(v.id)

  // Term
  def asFront(t: K.Term): Term = asFrontLabel(t.label).applySeq(t.args.map(asFront))

  // FormulaLabel
  def asFrontLabel(fl: K.FormulaLabel): AtomicLabel[?] | ConnectorLabel | BinderLabel = fl match
    case fl: K.ConnectorLabel => asFrontLabel(fl)
    case fl: K.AtomicLabel => asFrontLabel(fl)
    case fl: K.BinderLabel => asFrontLabel(fl)
  def asFrontLabel(pl: K.AtomicLabel): AtomicLabel[?] = pl match
    case pl: K.ConstantAtomicLabel => asFrontLabel(pl)
    case pl: K.SchematicAtomicLabel => asFrontLabel(pl)
  def asFrontLabel(cl: K.ConnectorLabel): ConnectorLabel = cl match
    case cl: K.ConstantConnectorLabel => asFrontLabel(cl)
    case cl: K.SchematicConnectorLabel => asFrontLabel(cl)
  def asFrontLabel[N <: Arity](cpl: K.ConstantAtomicLabel): ConstantAtomicLabelOfArity[N] = cpl.arity.asInstanceOf[N] match
    case n: 0 => ConstantFormula(cpl.id)
    case n: N => ConstantPredicateLabel(cpl.id, cpl.arity.asInstanceOf)
  def asFrontLabel(sfl: K.SchematicFormulaLabel): SchematicAtomicLabel[?] | SchematicConnectorLabel[?] =
    sfl match
      case v: K.VariableFormulaLabel => asFrontLabel(v)
      case v: K.SchematicPredicateLabel => asFrontLabel(v)
      case v: K.SchematicConnectorLabel => asFrontLabel(v)
  def asFrontLabel(svop: K.SchematicAtomicLabel): SchematicAtomicLabel[?] = svop match
    case v: K.VariableFormulaLabel => asFrontLabel(v)
    case v: K.SchematicPredicateLabel => asFrontLabel(v)
  def asFrontLabel(v: K.VariableFormulaLabel): VariableFormula = VariableFormula(v.id)
  def asFrontLabel[N <: Arity](spl: K.SchematicPredicateLabel): SchematicPredicateLabel[N] =
    SchematicPredicateLabel(spl.id, spl.arity.asInstanceOf)
  def asFrontLabel[N <: Arity](scl: K.SchematicConnectorLabel): SchematicConnectorLabel[N] =
    SchematicConnectorLabel(scl.id, scl.arity.asInstanceOf)
  def asFrontLabel(cpl: K.ConstantConnectorLabel): ConnectorLabel = cpl match
    case K.Neg => Neg
    case K.Implies => Implies
    case K.Iff => Iff
    case K.And => And
    case K.Or => Or
  def asFrontLabel(bl: K.BinderLabel): BaseBinderLabel = bl match {
    case K.Forall => Forall
    case K.Exists => Exists
    case K.ExistsOne => ExistsOne
  }

  // Formula
  def asFront(f: K.Formula): Formula = f match
    case f: K.AtomicFormula => asFront(f)
    case f: K.ConnectorFormula => asFront(f)
    case f: K.BinderFormula => asFront(f)
  def asFront(pf: K.AtomicFormula): Formula =
    asFrontLabel(pf.label).applySeq(pf.args.map(asFront))
  def asFront(cf: K.ConnectorFormula): Formula =
    asFrontLabel(cf.label).applyUnsafe(cf.args.map(asFront))
  def asFront(bf: K.BinderFormula): BinderFormula =
    asFrontLabel(bf.label).apply(asFrontLabel(bf.bound), asFront(bf.inner))

  // Sequents
  def asFront(s: K.Sequent): Sequent = Sequent(s.left.map(asFront), s.right.map(asFront))

  // Lambdas
  def asFrontLambda(l: K.LambdaTermTerm): LambdaExpression[Term, Term, ?] = LambdaExpression(l.vars.map(asFrontLabel), asFront(l.body), l.vars.size)
  def asFrontLambda(l: K.LambdaTermFormula): LambdaExpression[Term, Formula, ?] = LambdaExpression(l.vars.map(asFrontLabel), asFront(l.body), l.vars.size)
  def asFrontLambda(l: K.LambdaFormulaFormula): LambdaExpression[Formula, Formula, ?] = LambdaExpression(l.vars.map(asFrontLabel), asFront(l.body), l.vars.size)

  def freshVariable[A <: LisaObject[A]](obj: A, name: Identifier): Variable = Variable(freshId(obj.allSchematicLabels.map(_.id), name))
  def freshVariable[A <: LisaObject[A]](objs: Iterable[A], name: Identifier): Variable = Variable(freshId(objs.flatMap(_.allSchematicLabels).map(_.id), name))
}
