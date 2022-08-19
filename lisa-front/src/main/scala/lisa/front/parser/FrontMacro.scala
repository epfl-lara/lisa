package lisa.front.parser

import lisa.front.fol.FOL.*
import lisa.front.proof.Proof.*
import lisa.front.printer.FrontPositionedPrinter

// Note: on Intellij you may want to disable syntax highlighting for this file
// ("File Types" => "Text" => "Ignored Files and Folders", add "FrontMacro.scala")

/**
 * Macros to enable compile-time string interpolation. For instance:
 * <pre>
 * val f: Formula = ...
 * formula"|- (a /\ $f); ?c"
 * </pre>
 */
object FrontMacro {
  import scala.quoted.*

  // https://github.com/lampepfl/dotty/issues/8577#issuecomment-1014729373

  extension (inline sc: StringContext) {
    transparent inline def term: Any = ${ SIParts.scMacro[TermParts]('sc) }
    transparent inline def formula: Any = ${ SIParts.scMacro[FormulaParts]('sc) }
    transparent inline def sequent: Any = ${ SIParts.scMacro[SequentParts]('sc) }
    transparent inline def partial: Any = ${ SIParts.scMacro[PartialSequentParts]('sc) }
  }

  class TermParts[P <: Tuple](parts: P) {
    transparent inline def apply(inline args: Any*): Term = ${ termApplyMacro('parts, 'args) }
    //transparent inline def unapplySeq(inline arg: Any): Option[Seq[Any]] = ${ termUnapplyMacro('parts, 'arg) }
  }
  class FormulaParts[P <: Tuple](parts: P) {
    transparent inline def apply(inline args: Any*): Formula = ${ formulaApplyMacro('parts, 'args) }
  }
  class SequentParts[P <: Tuple](parts: P) {
    transparent inline def apply(inline args: Any*): Sequent = ${ sequentApplyMacro('parts, 'args) }
  }
  class PartialSequentParts[P <: Tuple](parts: P) {
    transparent inline def apply(inline args: Any*): PartialSequent = ${ partialSequentApplyMacro('parts, 'args) }
  }

  trait SIParts[P <: Tuple](parts: P)
  object SIParts {
    def scMacro[SI[_ <: Tuple]](sc: Expr[StringContext])(using Quotes, Type[SI]): Expr[Any] = {
      import quotes.reflect.*
      val args = sc match {
        case '{StringContext(${Varargs(args)}*)} => args
      }
      val tplExpr = Expr.ofTupleFromSeq(args)
      val tplTpe = tplExpr.asTerm.tpe
      val siTpe = TypeRepr.of[SI[Tuple]].asInstanceOf[TypeRepr & Matchable] match {
        case AppliedType(siTpe, _) => siTpe
      }
      val siSym = siTpe.typeSymbol
      val siTree =
        New(TypeTree.of[SI[Tuple]])
          .select(siSym.primaryConstructor)
          .appliedToType(tplTpe)
          .appliedTo(tplExpr.asTerm)
      siTree.asExpr
    }
  }


  /*private def termUnapplyMacro[P <: Tuple](parts: Expr[P], arg: Expr[Any])(using Quotes, Type[P]): Expr[Option[Seq[Any]]] = {
    '{ None: Option[Seq[Term]] }
  }*/

  enum Variable {
    val expr: Expr[Any]
    case FunctionLabelVariable(expr: Expr[TermLabel[?]], placeholder: SchematicTermLabel[?])
    case PredicateLabelVariable(expr: Expr[PredicateLabel[?]], placeholder: SchematicPredicateLabel[?])
    case ConnectorLabelVariable(expr: Expr[ConnectorLabel[?]], placeholder: SchematicConnectorLabel[?])
    case VariableLabelVariable(expr: Expr[VariableLabel], placeholder: VariableLabel)
    case TermVariable(expr: Expr[Term], placeholder: SchematicTermLabel[0])
    case FormulaVariable(expr: Expr[Formula], placeholder: SchematicPredicateLabel[0])
  }
  import Variable.*

  case class Interpolator(idsAndVariables: Seq[(String, Variable)], tokens: Seq[FrontToken]) {
    val variables: Seq[Variable] = idsAndVariables.map { case (_, variable) => variable }
    val map: Map[String, Variable] = idsAndVariables.toMap
  }

  private def toTokens[P <: Tuple](parts: Expr[P], args: Expr[Seq[Any]])(using Quotes, Type[P]): Interpolator = {
    import quotes.reflect.{Term as _, *}

    // throw new Error(s"illegal interpolation variable: ${TypeTree.of[other]}")
    // TypeTree[ConstantType(Constant({))]
    def evaluateParts[Q <: Tuple](scrutiny: Type[Q], acc: Seq[String]): Seq[String] = scrutiny match {
      case '[ EmptyTuple ] => acc
      case '[ head *: tail ] =>
        val string = TypeTree.of[head].tpe.asInstanceOf[TypeRepr & Matchable] match {
          case ConstantType(cst) => cst.value.asInstanceOf[String] // Should always match and succeed
        }
        evaluateParts(Type.of[tail], string +: acc)
      }
    // `Type.of[P]` is equivalent to `summon[Type[P]]`
    val evaluatedParts: Seq[String] = evaluateParts(Type.of[P], Seq.empty).reverse

    val partsTokens: Seq[Seq[FrontToken]] = evaluatedParts.map(FrontLexer.lexingAscii(_)).map(_.init)
    val takenNames: Set[String] = partsTokens.flatten.collect {
      case FrontToken.Identifier(id) => id
      case FrontToken.SchematicIdentifier(id) => id
      case FrontToken.SchematicConnectorIdentifier(id) => id
    }.toSet

    val argsSeq: Seq[Expr[Any]] = args match {
      case Varargs(es) => es
    }

    // TODO raise warning when using infix notation

    def resolveArity[N <: Arity](expr: Expr[LabelType & WithArityType[N]])(using Type[N]): Int =
      TypeTree.of[N].tpe.asInstanceOf[TypeRepr & Matchable] match {
        case ConstantType(cst) => cst.value.asInstanceOf[Int]
        case _ => report.errorAndAbort(s"loosely typed label variable, the arity must be known at compile time: ${Type.show[N]}", expr)
      }

    val idsAndVariables: Seq[(String, Variable)] = argsSeq.zipWithIndex.foldLeft((Seq.empty[(String, Variable)], Map.empty[Any, String], takenNames)) { case ((acc, hashmap, taken), (expr, i)) =>
      val id = hashmap.getOrElse(expr.asTerm.toString, { // FIXME: `asTerm.toString` is not a safe way to check whether two expressions are `=:=`
        val base = s"x$i"
        if(taken.contains(base)) freshId(taken, base) else base
      })
      val variable = expr match {
        case '{ $label: TermLabel[n] } => FunctionLabelVariable(label, SchematicTermLabel.unsafe(id, resolveArity(label)))
        case '{ $label: PredicateLabel[n] } => PredicateLabelVariable(label, SchematicPredicateLabel.unsafe(id, resolveArity(label)))
        case '{ $label: ConnectorLabel[n] } => ConnectorLabelVariable(label, SchematicConnectorLabel.unsafe(id, resolveArity(label)))
        case '{ $label: VariableLabel } => VariableLabelVariable(label, VariableLabel(id))
        case '{ $term: Term } => TermVariable(term, SchematicTermLabel[0](id))
        case '{ $formula: Formula } => FormulaVariable(formula, SchematicPredicateLabel[0](id))
        case '{ $t: q } => report.errorAndAbort(s"unsupported variable type: ${Type.show[q]}", expr)
      }
      ((id, variable) +: acc, hashmap + (expr.asTerm.toString -> id), taken + id)
    }._1.reverse

    val variables = idsAndVariables.map { case (_, variable) => variable }

    val variablesTokens: Seq[FrontToken] = variables.map {
      case FunctionLabelVariable(_, placeholder) => FrontToken.SchematicIdentifier(placeholder.id)
      case PredicateLabelVariable(_, placeholder) => FrontToken.SchematicIdentifier(placeholder.id)
      case ConnectorLabelVariable(_, placeholder) => FrontToken.SchematicConnectorIdentifier(placeholder.id)
      case VariableLabelVariable(_, placeholder) => FrontToken.Identifier(placeholder.id)
      case TermVariable(_, placeholder) => FrontToken.SchematicIdentifier(placeholder.id)
      case FormulaVariable(_, placeholder) => FrontToken.SchematicIdentifier(placeholder.id)
    }

    val tokens: Seq[FrontToken] = partsTokens.head ++ variablesTokens.zip(partsTokens.tail).flatMap { case (v, p) => v +: p } :+ FrontToken.End()

    Interpolator(idsAndVariables, tokens)
  }

  private def getRenaming(variables: Seq[Variable])(using Quotes):
  Expr[(
    Seq[AssignedFunction],
      Seq[AssignedPredicate],
      Seq[AssignedConnector],
      Map[VariableLabel, VariableLabel],
    )] = {
    import LiftFOL.{*, given}

    def substMap[T, U](seq: Seq[(Expr[T], Expr[U])])(using Quotes, Type[T], Type[U]): Expr[Map[T, U]] = {
      val list: Seq[Expr[(T, U)]] = seq.map { case (k, v) =>
        '{ $k -> $v }
      }
      '{ ${liftSeq(list)}.toMap }
    }

    val functionsMap: Expr[Seq[AssignedFunction]] = liftSeq(variables.collect {
      case FunctionLabelVariable(label, placeholder) =>
        '{ RenamedLabel.unsafe(${Expr(placeholder)}, $label).toAssignment }
    })
    val predicatesMap: Expr[Seq[AssignedPredicate]] = liftSeq(variables.collect {
      case PredicateLabelVariable(label, placeholder) =>
        '{ RenamedLabel.unsafe(${Expr(placeholder)}, $label).toAssignment }
    })
    val connectorsMap: Expr[Seq[AssignedConnector]] = liftSeq(variables.collect {
      case ConnectorLabelVariable(label, placeholder) =>
        '{ RenamedLabel.unsafe(${Expr(placeholder)}, $label).toAssignment }
    })
    val variablesMap: Expr[Map[VariableLabel, VariableLabel]] = substMap(variables.collect {
      case VariableLabelVariable(label, placeholder) =>
        Expr(placeholder) -> label
    })

    val termsMap: Expr[Seq[AssignedFunction]] = liftSeq(variables.collect {
      case TermVariable(term, placeholder) =>
        '{ AssignedFunction.unsafe(${Expr(placeholder)(using toExprFunction0)}, LambdaFunction.unsafe(Seq.empty, $term)) }
    })
    val formulasMap: Expr[Seq[AssignedPredicate]] = liftSeq(variables.collect {
      case FormulaVariable(formula, placeholder) =>
        '{ AssignedPredicate.unsafe(${Expr(placeholder)(using toExprPredicate0)}, LambdaPredicate.unsafe(Seq.empty, $formula)) }
    })

    '{ ($functionsMap ++ $termsMap, $predicatesMap ++ $formulasMap, $connectorsMap, $variablesMap) }
  }

  def unsafeFixPointTermInstantiate(term: Term, functions: Seq[AssignedFunction], map: Map[VariableLabel, VariableLabel]): Term = {
    val next = instantiateTermSchemas(unsafeRenameVariables(term, map), functions)
    if(next == term) term else unsafeFixPointTermInstantiate(next, functions, map)
  }

  def unsafeFixPointFormulaInstantiate(formula: Formula, functions: Seq[AssignedFunction], predicates: Seq[AssignedPredicate], connectors: Seq[AssignedConnector], map: Map[VariableLabel, VariableLabel]): Formula = {
    val next = instantiateFormulaSchemas(unsafeRenameVariables(formula, map), functions, predicates, connectors)
    if(next == formula) formula else unsafeFixPointFormulaInstantiate(next, functions, predicates, connectors, map)
  }

  private def typeCheck(
    interpolator: Interpolator,
    functions: Set[TermLabel[?]],
    predicates: Set[PredicateLabel[?]],
    connectors: Set[SchematicConnectorLabel[?]],
    variables: Set[VariableLabel],
  )(using Quotes): Unit = {
    import quotes.reflect.*

    def reportArityMismatch(expr: Expr[?], expected: Int, actual: Int): Nothing =
      report.errorAndAbort(s"arity mismatch: variable label expects $expected arguments but you provided $actual", expr)

    // Either function or predicate
    functions.flatMap(f => interpolator.map.get(f.id).map(f -> _)).foreach { case (f, variable) =>
      variable match {
        case FunctionLabelVariable(label, placeholder) =>
          if(f.arity != placeholder.arity) {
            reportArityMismatch(label, placeholder.arity, f.arity)
          }
        case TermVariable(label, placeholder) =>
          if(f.arity != placeholder.arity) {
            report.errorAndAbort("variable term does not expect any arguments", label)
          }
        case VariableLabelVariable(label, _) => report.errorAndAbort("undeclared free variable", label)
        case other => report.errorAndAbort("expected term, got formula", other.expr)
      }
    }
    // Ditto
    predicates.flatMap(f => interpolator.map.get(f.id).map(f -> _)).foreach { case (f, variable) =>
      variable match {
        case PredicateLabelVariable(label, placeholder) =>
          if(f.arity != placeholder.arity) {
            reportArityMismatch(label, placeholder.arity, f.arity)
          }
        case FormulaVariable(label, placeholder) =>
          if(f.arity != placeholder.arity) {
            report.errorAndAbort("variable formula does not expect any arguments", label)
          }
        case VariableLabelVariable(label, _) => report.errorAndAbort("undeclared free variable", label)
        case other => report.errorAndAbort("expected formula, got term", other.expr)
      }
    }
    // Connectors are disjoint from anything else
    connectors.flatMap(f => interpolator.map.get(f.id).map(f -> _)).foreach { case (f, variable) =>
      variable match {
        case ConnectorLabelVariable(label, placeholder) =>
          if(f.arity != placeholder.arity) {
            reportArityMismatch(label, placeholder.arity, f.arity)
          }
        case other => throw new Error // Shouldn't happen
      }
    }
    // Variable are also apart
    variables.flatMap(f => interpolator.map.get(f.id).map(f -> _)).foreach { case (f, variable) =>
      variable match {
        case VariableLabelVariable(_, _) => ()
        case other => report.errorAndAbort("expected term, got formula", other.expr)
      }
    }
  }

  private def termApplyMacro[P <: Tuple](parts: Expr[P], args: Expr[Seq[Any]])(using Quotes, Type[P]): Expr[Term] = {
    import quotes.reflect.*
    import LiftFOL.{*, given}

    val interpolator = toTokens(parts, args)
    val resolved = FrontResolver.resolveTerm(FrontParser.parseTopTermOrFormula(interpolator.tokens))

    typeCheck(interpolator, termLabelsOf(resolved), Set.empty, Set.empty, freeVariablesOf(resolved))

    '{
      val (functionsMap, _, _, variablesMap) = ${getRenaming(interpolator.variables)}
      unsafeFixPointTermInstantiate(${Expr(resolved)}, functionsMap, variablesMap)
    }
  }
  private def formulaApplyMacro[P <: Tuple](parts: Expr[P], args: Expr[Seq[Any]])(using Quotes, Type[P]): Expr[Formula] = {
    import quotes.reflect.*
    import LiftFOL.{*, given}

    val interpolator = toTokens(parts, args)
    val resolved = FrontResolver.resolveFormula(FrontParser.parseTopTermOrFormula(interpolator.tokens))

    typeCheck(interpolator, termLabelsOf(resolved), predicatesOf(resolved), schematicConnectorsOf(resolved), freeVariablesOf(resolved))

    '{
      val (functionsMap, predicatesMap, connectorsMap, variablesMap) = ${getRenaming(interpolator.variables)}
      unsafeFixPointFormulaInstantiate(${Expr(resolved)}, functionsMap, predicatesMap, connectorsMap, variablesMap)
    }
  }
  private def sequentApplyMacro[P <: Tuple](parts: Expr[P], args: Expr[Seq[Any]])(using Quotes, Type[P]): Expr[Sequent] = {
    import quotes.reflect.*
    import LiftFOL.{*, given}

    val interpolator = toTokens(parts, args)
    val resolved = FrontResolver.resolveSequent(FrontParser.parseSequent(interpolator.tokens))

    typeCheck(interpolator, functionsOfSequent(resolved), predicatesOfSequent(resolved), schematicConnectorsOfSequent(resolved), freeVariablesOfSequent(resolved))

    '{
      val (functionsMap, predicatesMap, connectorsMap, variablesMap) = ${getRenaming(interpolator.variables)}
      def rename(formula: Formula): Formula =
        unsafeFixPointFormulaInstantiate(formula, functionsMap, predicatesMap, connectorsMap, variablesMap)
      Sequent(${liftSeq(resolved.left.toSeq.map(Expr.apply))}.toIndexedSeq.map(rename), ${liftSeq(resolved.right.toSeq.map(Expr.apply))}.toIndexedSeq.map(rename))
    }
  }
  private def partialSequentApplyMacro[P <: Tuple](parts: Expr[P], args: Expr[Seq[Any]])(using Quotes, Type[P]): Expr[PartialSequent] = {
    import quotes.reflect.*
    import LiftFOL.{*, given}

    val interpolator = toTokens(parts, args)
    val resolved = FrontResolver.resolvePartialSequent(FrontParser.parsePartialSequent(interpolator.tokens))

    typeCheck(interpolator, functionsOfSequent(resolved), predicatesOfSequent(resolved), schematicConnectorsOfSequent(resolved), freeVariablesOfSequent(resolved))

    '{
      val (functionsMap, predicatesMap, connectorsMap, variablesMap) = ${getRenaming(interpolator.variables)}
      def rename(formula: Formula): Formula =
        unsafeFixPointFormulaInstantiate(formula, functionsMap, predicatesMap, connectorsMap, variablesMap)
      PartialSequent(${liftSeq(resolved.left.toSeq.map(Expr.apply))}.toIndexedSeq.map(rename), ${liftSeq(resolved.right.toSeq.map(Expr.apply))}.toIndexedSeq.map(rename), ${Expr(resolved.partialLeft)}, ${Expr(resolved.partialRight)})
    }
  }


  private object LiftFOL {
    def liftSeq[T](seq: Seq[Expr[T]])(using Quotes, Type[T]): Expr[Seq[T]] =
      seq.foldRight('{ Seq.empty[T] })((e, acc) => '{ $e +: $acc })

    // TODO support the generic type conversion (it's harder than it looks)

    given ToExpr[SchematicTermLabel[?]] with {
      def apply(f: SchematicTermLabel[?])(using Quotes): Expr[SchematicTermLabel[?]] =
        '{ SchematicTermLabel.unsafe(${Expr(f.id)}, ${Expr(f.arity.asInstanceOf[Int])}) }
    }
    given ToExpr[ConstantFunctionLabel[?]] with {
      def apply(f: ConstantFunctionLabel[?])(using Quotes): Expr[ConstantFunctionLabel[?]] =
        '{ ConstantFunctionLabel.unsafe(${Expr(f.id)}, ${Expr(f.arity.asInstanceOf[Int])}) }
    }
    given ToExpr[SchematicPredicateLabel[?]] with {
      def apply(f: SchematicPredicateLabel[?])(using Quotes) =
        '{ SchematicPredicateLabel.unsafe(${Expr(f.id)}, ${Expr(f.arity.asInstanceOf[Int])}) }
    }
    given ToExpr[ConstantPredicateLabel[?]] with {
      def apply(f: ConstantPredicateLabel[?])(using Quotes): Expr[ConstantPredicateLabel[?]] =
        '{ ConstantPredicateLabel.unsafe(${Expr(f.id)}, ${Expr(f.arity.asInstanceOf[Int])}) }
    }
    given ToExpr[SchematicConnectorLabel[?]] with {
      def apply(f: SchematicConnectorLabel[?])(using Quotes) =
        '{ SchematicConnectorLabel.unsafe(${Expr(f.id)}, ${Expr(f.arity.asInstanceOf[Int])}) }
    }
    given ToExpr[VariableLabel] with {
      def apply(l: VariableLabel)(using Quotes) =
        '{ VariableLabel(${Expr(l.id)}) }
    }
    given ToExpr[BinderLabel] with {
      def apply(l: BinderLabel)(using Quotes) =
        l match {
          case `forall` => '{ forall }
          case `exists` => '{ exists }
          case `existsOne` => '{ existsOne }
        }
    }

    // FIXME "hack" otherwise the two givens would clash
    val toExprFunction0: ToExpr[SchematicTermLabel[0]] = new {
      def apply(f: SchematicTermLabel[0])(using Quotes): Expr[SchematicTermLabel[0]] =
        '{ SchematicTermLabel[0](${Expr(f.id)}) }
    }
    val toExprPredicate0: ToExpr[SchematicPredicateLabel[0]] = new {
      def apply(f: SchematicPredicateLabel[0])(using Quotes): Expr[SchematicPredicateLabel[0]] =
        '{ SchematicPredicateLabel[0](${Expr(f.id)}) }
    }

    given ToExpr[TermLabel[?]] with {
      def apply(f: TermLabel[?])(using Quotes): Expr[TermLabel[?]] = f match {
        case constant: ConstantFunctionLabel[?] => Expr(constant)(using summon[ToExpr[ConstantFunctionLabel[?]]])
        case schematic: SchematicTermLabel[?] => Expr(schematic)(using summon[ToExpr[SchematicTermLabel[?]]])
      }
    }
    given ToExpr[PredicateLabel[?]] with {
      def apply(f: PredicateLabel[?])(using Quotes): Expr[PredicateLabel[?]] = f match {
        case constant: ConstantPredicateLabel[?] => Expr(constant)(using summon[ToExpr[ConstantPredicateLabel[?]]])
        case schematic: SchematicPredicateLabel[?] => Expr(schematic)(using summon[ToExpr[SchematicPredicateLabel[?]]])
      }
    }
    given ToExpr[ConnectorLabel[?]] with {
      def apply(f: ConnectorLabel[?])(using Quotes): Expr[ConnectorLabel[?]] = f match {
        case constant: ConstantConnectorLabel[?] => constant match {
          case `neg` => '{ neg }
          case `implies` => '{ implies }
          case `iff` => '{ iff }
          case `and` => '{ and }
          case `or` => '{ or }
        }
        case schematic: SchematicConnectorLabel[?] => Expr(schematic)(using summon[ToExpr[SchematicConnectorLabel[?]]])
      }
    }

    given ToExpr[Term] with {
      def apply(t: Term)(using Quotes): Expr[Term] = t match {
        case VariableTerm(label) => '{ VariableTerm(${Expr(label)}) }
        case Term(label, args) => '{ Term.unsafe(${Expr(label)}, ${liftSeq(args.map(Expr.apply(_)))}) }
      }
    }
    given ToExpr[Formula] with {
      def apply(f: Formula)(using Quotes): Expr[Formula] = f match {
        case PredicateFormula(label, args) => '{ PredicateFormula.unsafe(${Expr(label)}, ${liftSeq(args.map(Expr.apply(_)))}) }
        case ConnectorFormula(label, args) => '{ ConnectorFormula.unsafe(${Expr(label)}, ${liftSeq(args.map(Expr.apply(_)))}) }
        case BinderFormula(label, bound, inner) => '{ BinderFormula(${Expr(label)}, ${Expr(bound)}, ${Expr(inner)}) }
      }
    }
  }

}
