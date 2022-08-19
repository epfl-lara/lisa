package lisa.front.parser

import lisa.front.fol.FOL.*
import lisa.front.proof.Proof.*
import lisa.front.parser.FrontParsed.*
import lisa.front.parser.FrontReadingException.ResolutionException
import lisa.front.theory.SetTheory

import scala.util.{Failure, Success, Try}
import scala.util.parsing.input.{Position, Positional}
import scala.collection.View

/**
 * Resolves the intermediate representation ([[FrontParsed]]) into actual first order logic or sequent elements.
 */
private[parser] object FrontResolver {

  // Free variables must appear in the context, otherwise they will be treated as
  // nullary function terms

  case class ScopedContext(boundVariables: Set[String], freeVariables: Set[String]) {
    def variables: Set[String] = boundVariables ++ freeVariables
  }

  private def emptyScopedContext: ScopedContext = ScopedContext(Set.empty, Set.empty)

  private def resolveFunctionTermLabel(name: ParsedName, arity: Int): TermLabel[?] = name match {
    case ParsedConstant(identifier) => ConstantFunctionLabel.unsafe(identifier, arity)
    case ParsedSchema(identifier, connector) =>
      if(!connector)
        SchematicTermLabel.unsafe(identifier, arity)
      else
        throw ResolutionException("Type error: expected term, got schematic connector formula", name.pos)
  }

  private def resolvePredicateOrConnectorFormulaLabel(name: ParsedName, arity: Int): PredicateLabel[?] | SchematicConnectorLabel[?] = name match {
    case ParsedConstant(identifier) => ConstantPredicateLabel.unsafe(identifier, arity)
    case ParsedSchema(identifier, connector) =>
      if(connector)
        SchematicConnectorLabel.unsafe(identifier, arity)
      else
        SchematicPredicateLabel.unsafe(identifier, arity)
  }

  private def resolveTermContext(tree: ParsedTermOrFormula)(implicit ctx: ScopedContext): Term = tree match {
    case name: ParsedName =>
      name match {
        case ParsedConstant(identifier) =>
          // If the name in context then it must be a variable. Otherwise we fallback to a constant function
          if(ctx.variables.contains(identifier)) {
            VariableTerm(VariableLabel(identifier))
          } else {
            ConstantFunctionLabel[0](identifier)
          }
        case ParsedSchema(identifier, connector) =>
          if(!connector) {
            SchematicTermLabel[0](identifier)
          } else {
            throw ResolutionException("Type error: expected term, got schematic connector formula", tree.pos)
          }
      }
      // If the name is in the context, we decide that it is a variable

    case ParsedApplication(name, args) =>
      Term.unsafe(resolveFunctionTermLabel(name, args.size), args.map(resolveTermContext(_)))
    case ParsedOrderedPair(left, right) =>
      ConstantFunctionLabel[2]("ordered_pair")(resolveTermContext(left), resolveTermContext(right))
    case ParsedSet2(left, right) =>
      SetTheory.unorderedPairSet(resolveTermContext(left), resolveTermContext(right))
    case ParsedSet1(subtree) =>
      SetTheory.singletonSet(resolveTermContext(subtree))
    case ParsedSet0() =>
      SetTheory.emptySet
    case ParsedPower(subtree) =>
      SetTheory.powerSet(resolveTermContext(subtree))
    case ParsedUnion(subtree) =>
      SetTheory.unionSet(resolveTermContext(subtree))
    case _ => throw ResolutionException("Type error: expected term, got formula", tree.pos)
  }

  private def resolveFormulaContext(tree: ParsedTermOrFormula)(implicit ctx: ScopedContext): Formula = tree match {
    case name: ParsedName =>
      resolvePredicateOrConnectorFormulaLabel(name, 0) match {
        case predicate: PredicateLabel[?] => PredicateFormula.unsafe(predicate, Seq.empty)
        case connector: SchematicConnectorLabel[?] =>
          throw ResolutionException("Illegal: the arity of schematic connectors must be strictly positive", tree.pos)
      }
    case ParsedApplication(name, args) =>
      resolvePredicateOrConnectorFormulaLabel(name, args.size) match {
        case predicate: PredicateLabel[?] => PredicateFormula.unsafe(predicate, args.map(resolveTermContext(_)))
        case connector: SchematicConnectorLabel[?] => ConnectorFormula.unsafe(connector, args.map(resolveFormulaContext(_)))
      }
    case operator: ParsedBinaryOperator =>
      val label: Either[PredicateLabel[?], ConnectorLabel[?]] = operator match {
        case _: ParsedEqual => Left(equality)
        case _: ParsedMembership => Left(ConstantPredicateLabel[2]("set_membership"))
        case _: ParsedSubset => Left(ConstantPredicateLabel[2]("subset_of"))
        case _: ParsedSameCardinality => Left(ConstantPredicateLabel[2]("same_cardinality"))
        case _: ParsedAnd => Right(and)
        case _: ParsedOr => Right(or)
        case _: ParsedImplies => Right(implies)
        case _: ParsedIff => Right(iff)
      }
      val args = Seq(operator.left, operator.right)
      label match {
        case Left(label) => PredicateFormula.unsafe(label, args.map(resolveTermContext(_)))
        case Right(label) => ConnectorFormula.unsafe(label, args.map(resolveFormulaContext(_)))
      }
    case ParsedNot(termOrFormula) =>
      ConnectorFormula.unsafe(neg, Seq(resolveFormulaContext(termOrFormula)))
    case binder: ParsedBinder =>
      binder.bound.find(ctx.variables.contains).orElse(binder.bound.diff(binder.bound.distinct).headOption) match {
        case Some(bound) => throw ResolutionException(s"Name conflict: ${binder.bound}", binder.pos)
        case None => ()
      }
      val label = binder match {
        case _: ParsedForall => forall
        case _: ParsedExists => exists
        case _: ParsedExistsOne => existsOne
      }
      binder.bound.foldRight(resolveFormulaContext(binder.termOrFormula)(ctx.copy(boundVariables = ctx.boundVariables ++ binder.bound)))(
        (bound, body) => BinderFormula(label, VariableLabel(bound), body)
      )
    case _ => throw ResolutionException("Type error: expected formula, got term", tree.pos)
  }

  def resolveTerm(tree: ParsedTermOrFormula): Term =
    resolveTermContext(tree)(emptyScopedContext)

  def resolveTerm(tree: ParsedTopTermOrFormula): Term =
    resolveTermContext(tree.termOrFormula)(freeVariablesToContext(tree.freeVariables, tree.pos))

  def resolveFormula(tree: ParsedTermOrFormula): Formula =
    resolveFormulaContext(tree)(emptyScopedContext)

  private def freeVariablesToContext(freeVariables: Seq[String], position: Position): ScopedContext = {
    val repeated = freeVariables.diff(freeVariables.distinct).distinct
    if(repeated.isEmpty) {
      ScopedContext(Set.empty, freeVariables.toSet)
    } else {
      throw ResolutionException(s"Repeated free variable declaration: ${repeated.mkString(", ")}", position)
    }
  }

  def resolveFormula(tree: ParsedTopTermOrFormula): Formula =
    resolveFormulaContext(tree.termOrFormula)(freeVariablesToContext(tree.freeVariables, tree.pos))

  def resolveSequent(tree: ParsedSequent): Sequent = {
    val ctx = freeVariablesToContext(tree.freeVariables, tree.pos)
    Sequent(tree.left.map(resolveFormulaContext(_)(ctx)).toIndexedSeq, tree.right.map(resolveFormulaContext(_)(ctx)).toIndexedSeq)
  }

  def resolvePartialSequent(tree: ParsedPartialSequent): PartialSequent = {
    val ctx = freeVariablesToContext(tree.freeVariables, tree.pos)
    PartialSequent(tree.left.map(resolveFormulaContext(_)(ctx)).toIndexedSeq, tree.right.map(resolveFormulaContext(_)(ctx)).toIndexedSeq, tree.partialLeft, tree.partialRight)
  }

}
