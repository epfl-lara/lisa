package lisa.front.fol.utils

import lisa.front.fol.conversions.to.TermConversionsTo
import lisa.front.fol.definitions.TermDefinitions
import lisa.front.fol.ops.CommonOps

import scala.annotation.targetName

trait TermUtils extends TermDefinitions with TermConversionsTo with CommonOps with CommonUtils {

  type RenamedFunction[B <: TermLabel[?]] = RenamedLabel[TermLabel[?], SchematicTermLabel[?], B]
  type RenamedFunctionSchema = RenamedFunction[SchematicTermLabel[?]]

  extension [L <: TermLabel[?]](renamed: RenamedFunction[L]) {
    def toAssignment: AssignedFunction = {
      val parameters = freshIds(Set.empty, renamed.from.arity).map(SchematicTermLabel.apply[0])
      AssignedFunction.unsafe(renamed.from, LambdaFunction.unsafe(parameters, Term.unsafe(renamed.to, parameters.map(Term.unsafe(_, Seq.empty)))))
    }
  }

  def toKernel(lambda: LambdaFunction[?]): lisa.kernel.fol.FOL.LambdaTermTerm =
    lisa.kernel.fol.FOL.LambdaTermTerm(lambda.parameters.map(toKernel), lambda.body)
  given Conversion[LambdaFunction[?], lisa.kernel.fol.FOL.LambdaTermTerm] = toKernel


  case class LambdaFunction[N <: Arity] private(parameters: Seq[SchematicTermLabel[0]], body: Term) extends LambdaDefinition[N, SchematicTermLabel[0], Term] {
    override type U = Term
    override protected def instantiate(args: Seq[Term]): Term =
      instantiateTermSchemas(body, parameters.zip(args).map { case (from, to) => AssignedFunction(from, LambdaFunction(_ => to)) })
  }
  object LambdaFunction {
    def apply[N <: Arity](f: FillArgs[SchematicTermLabel[0], N] => Term)(using v: ValueOf[N]): LambdaFunction[N] = {
      val n = v.value
      val dummyVariable = SchematicTermLabel[0]("") // Used to identify the existing free variables, doesn't matter if this name collides
      val taken = schematicTermLabelsOf(fillTupleParameters(_ => dummyVariable, n, f)._2).map(_.id)
      val (params, body) = fillTupleParameters(SchematicTermLabel.apply[0](_), n, f, taken)
      new LambdaFunction(params.toSeq, body)
    }
    def apply(t: Term): LambdaFunction[0] = LambdaFunction(Seq.empty, t)
    def unsafe(parameters: Seq[SchematicTermLabel[0]], body: Term): LambdaFunction[?] = new LambdaFunction(parameters, body)
  }

  case class AssignedFunction private(schema: SchematicTermLabel[?], lambda: LambdaFunction[?])
    extends AssignedSchema[SchematicTermLabel[?], SchematicTermLabel[0]] {
    override type L = LambdaFunction[?]
  }
  object AssignedFunction {
    def apply[N <: Arity](schema: SchematicTermLabel[N], lambda: LambdaFunction[N])(using v: ValueOf[N]): AssignedFunction = new AssignedFunction(schema, lambda)
    def unsafe(schema: SchematicTermLabel[?], lambda: LambdaFunction[?]): AssignedFunction = new AssignedFunction(schema, lambda)
  }

  given Conversion[Term, LambdaFunction[0]] = LambdaFunction.apply
  given labelToLambdaFunction[T](using Conversion[T, Term]): Conversion[T, LambdaFunction[0]] = LambdaFunction.apply
  given lambdaToLambdaFunction1: Conversion[SchematicTermLabel[0] => Term, LambdaFunction[1]] = LambdaFunction.apply
  given lambdaToLambdaFunction2: Conversion[((SchematicTermLabel[0], SchematicTermLabel[0])) => Term, LambdaFunction[2]] = LambdaFunction.apply

  /** @see [[lisa.kernel.fol.FOL.isSame]] */
  def isSame(t1: Term, t2: Term): Boolean =
    lisa.kernel.fol.FOL.isSame(t1, t2)

  /** @see [[lisa.kernel.fol.FOL.Term#freeVariables]] */
  def freeVariablesOf(term: Term): Set[VariableLabel] = term match {
    case VariableTerm(label) => Set(label)
    case Term(label, args) => args.flatMap(freeVariablesOf).toSet
  }

  def termLabelsOf(term: Term): Set[TermLabel[?]] = term match {
    case Term(label, args) => args.flatMap(termLabelsOf).toSet + label
  }

  /** @see [[lisa.kernel.fol.FOL.Term#schematicFunctions]] */
  def schematicTermLabelsOf(term: Term): Set[SchematicTermLabel[?]] =
    termLabelsOf(term).collect { case schematic: SchematicTermLabel[?] => schematic }

  protected case class Scope(boundVariables: Set[VariableLabel] = Set.empty)

  /**
   * Checks whether a term is well-formed. Currently returns <code>true</code> at all times.
   * @param term the term to check
   * @return if it is well-formed
   */
  def isWellFormed(term: Term): Boolean = true

  def substituteVariables(term: Term, map: Map[VariableLabel, Term]): Term = term match {
    case VariableTerm(label) => map.getOrElse(label, term)
    case Term(label, args) => Term.unsafe(label, args.map(substituteVariables(_, map)))
  }

  def instantiateTermSchemas(term: Term, functions: Seq[AssignedFunction]): Term = {
    val map: Map[SchematicTermLabel[?], LambdaFunction[?]] = functions.map(i => i.schema -> i.lambda).toMap
    def instantiateInternal(term: Term): Term = term match {
      case Term(label, args) =>
        lazy val newArgs = args.map(instantiateInternal)
        label match {
          case f: SchematicTermLabel[?] if map.contains(f) => map(f).unsafe(newArgs)
          case _ => Term.unsafe(label, newArgs)
        }
    }
    instantiateInternal(term)
  }

  def unsafeRenameVariables(term: Term, map: Map[VariableLabel, VariableLabel]): Term =
    substituteVariables(term, map.view.mapValues(VariableTerm.apply).toMap)

}