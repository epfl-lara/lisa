package lisa.maths.SetTheory.Types.ADT

import lisa.utils.fol.FOL.{_, given}
import lisa.maths.SetTheory.Types.ADT.interface.{ADT, Constructor}
import lisa.maths.SetTheory.Types.ADT.encoding.SemanticADT
import lisa.maths.SetTheory.Types.ADT.syntax.AST.{ConstructorArg, SelfRef as RecursiveField, TypeArg}
import lisa.maths.SetTheory.Types.TypingHelpers.{TypeAssign, typ, vari}

import scala.language.dynamics
import scala.quoted.{Expr as Quoted, Quotes, Type, Varargs}

/**
 * Datatype declarations: `inductive(| zero(), | succ(n :: SelfRef))`.
 * Import `{inductive, SelfRef, |}` alongside the ADT DSL; field binders are existing LISA variables.
 */
object InductiveInfixSyntax {

  /**
   * The datatype being declared, implicitly applied to all its declared type parameters.
   */
  val SelfRef: Expr[Ind] = Variable[Ind]("inductiveSelf")

  /**
   * An immutable constructor specification, evaluated before any definitions are registered.
   */
  final case class Clause(name: String, fields: Seq[TypeAssign[Variable[Ind]]])

  /**
   * Converts statically checked constructor arguments to their ordered field list.
   */
  sealed trait Fields[T] {

    /**
     * Extracts the fields without evaluating any proofs.
     */
    def toList(value: T): List[TypeAssign[Variable[Ind]]]
  }

  /**
   * Accepts no fields, a single assignment, or a tuple of assignments.
   */
  object Fields {

    /**
     * Empty parentheses denote a nullary constructor.
     */
    given Fields[Unit] with {
      def toList(value: Unit): List[TypeAssign[Variable[Ind]]] = Nil
    }

    /**
     * A single assignment denotes one field.
     */
    given Fields[TypeAssign[Variable[Ind]]] with {
      def toList(value: TypeAssign[Variable[Ind]]): List[TypeAssign[Variable[Ind]]] = List(value)
    }

    /**
     * Ends the recursive traversal of a field tuple.
     */
    given Fields[EmptyTuple] with {
      def toList(value: EmptyTuple): List[TypeAssign[Variable[Ind]]] = Nil
    }

    /**
     * Preserves tuple order and requires every element to be a variable assignment.
     */
    given [H <: TypeAssign[Variable[Ind]], T <: Tuple](using tail: Fields[T]): Fields[H *: T] with {
      def toList(value: H *: T): List[TypeAssign[Variable[Ind]]] = value.head :: tail.toList(value.tail)
    }
  }

  /**
   * Introduces named constructors using infix calls such as `| cons(head :: A, tail :: SelfRef)`.
   */
  object | extends Dynamic {

    /**
     * Accepts the Unit, single assignment, or tuple supplied by Scala's infix syntax.
     */
    infix def applyDynamic[T](name: String)(fields: T)(using encoder: Fields[T]): Clause = Clause(name, encoder.toList(fields))
  }

  /**
   * An ADT with statically checked constructor selections.
   */
  final class Declaration[S] private[InductiveInfixSyntax] (semantic: SemanticADT)(using Sort[S]) extends ADT[S](semantic) with Selectable {
    private val members = constructors.iterator.map(constructor => constructor.semantic.name -> constructor).toMap

    /**
     * Selects an existing constructor without Java reflection or further proof generation.
     */
    def selectDynamic(name: String): Constructor[S] = members(name)

  }

  /**
   * Defines a monomorphic datatype from comma-separated constructor clauses.
   */
  transparent inline def inductive(inline body: Clause*)(using inline name: sourcecode.Name): Any =
    ${ expand[Ind]('{ Seq.empty[Variable[Ind]] }, 'body, 'name, '{ summon[Sort[Ind]] }) }

  /**
   * Defines a datatype with one explicit type parameter.
   */
  transparent inline def inductive(inline parameter: Variable[Ind])(inline body: Clause*)(using inline name: sourcecode.Name): Any =
    ${ expand[Ind >>: Ind]('{ Seq(parameter) }, 'body, 'name, '{ summon[Sort[Ind >>: Ind]] }) }

  /**
   * Defines a datatype with two explicit type parameters.
   */
  transparent inline def inductive(inline parameters: (Variable[Ind], Variable[Ind]))(inline body: Clause*)(using inline name: sourcecode.Name): Any =
    ${ expand[Ind >>: Ind >>: Ind]('{ val p = parameters; Seq(p._1, p._2) }, 'body, 'name, '{ summon[Sort[Ind >>: Ind >>: Ind]] }) }

  /**
   * Defines a datatype with three explicit type parameters.
   */
  transparent inline def inductive(inline parameters: (Variable[Ind], Variable[Ind], Variable[Ind]))(inline body: Clause*)(using inline name: sourcecode.Name): Any =
    ${ expand[Ind >>: Ind >>: Ind >>: Ind]('{ val p = parameters; Seq(p._1, p._2, p._3) }, 'body, 'name, '{ summon[Sort[Ind >>: Ind >>: Ind >>: Ind]] }) }

  /**
   * Defines a datatype with four explicit type parameters.
   */
  transparent inline def inductive(inline parameters: (Variable[Ind], Variable[Ind], Variable[Ind], Variable[Ind]))(inline body: Clause*)(using
      inline name: sourcecode.Name
  ): Any =
    ${ expand[Ind >>: Ind >>: Ind >>: Ind >>: Ind]('{ val p = parameters; Seq(p._1, p._2, p._3, p._4) }, 'body, 'name, '{ summon[Sort[Ind >>: Ind >>: Ind >>: Ind >>: Ind]] }) }

  /**
   * Defines a datatype with five explicit type parameters.
   */
  transparent inline def inductive(inline parameters: (Variable[Ind], Variable[Ind], Variable[Ind], Variable[Ind], Variable[Ind]))(inline body: Clause*)(using
      inline name: sourcecode.Name
  ): Any =
    ${ expand[Ind >>: Ind >>: Ind >>: Ind >>: Ind >>: Ind]('{ val p = parameters; Seq(p._1, p._2, p._3, p._4, p._5) }, 'body, 'name, '{ summon[Sort[Ind >>: Ind >>: Ind >>: Ind >>: Ind >>: Ind]] }) }

  /**
   * Runs the macro-validated clauses and builds its datatype after all clauses have been collected.
   */
  def build[S: Sort](parameters: Seq[Variable[Ind]], clauses: Seq[Clause], name: String): Declaration[S] = {
    require(parameters.forall(_ != null), "Inductive type parameters must be initialized before the declaration.")
    require(parameters.distinct.size == parameters.size, "An inductive declaration has duplicate type parameters.")

    val constructors = clauses.map { case Clause(constructorName, fields) =>
      val arguments = fields.map { field =>
        val argument: ConstructorArg =
          // Identity distinguishes the recursive placeholder even from an identically named external variable.
          if field.typ eq SelfRef then RecursiveField
          else
            parameters.find(_ == field.typ) match {
              case Some(parameter) => TypeArg(parameter.id.toString)
              case None => throw new IllegalArgumentException(s"Constructor $constructorName has a field type that is neither a declared parameter nor the recursive type.")
            }
        (field.vari.id.toString, argument)
      }
      (constructorName, arguments)
    }
    new Declaration[S](API.buildSemanticADT(name, parameters.map(_.id.toString), constructors))
  }

  private def expand[S: Type](
      parameters: Quoted[Seq[Variable[Ind]]],
      body: Quoted[Seq[Clause]],
      name: Quoted[sourcecode.Name],
      sort: Quoted[Sort[S]]
  )(using quotes: Quotes): Quoted[Any] = {
    import quotes.reflect.*

    def strip(term: Term): Term = term match {
      case Inlined(_, Nil, expression) => strip(expression)
      case Typed(expression, _) => strip(expression)
      case Block(Nil, expression) => strip(expression)
      case other => other
    }

    def application(term: Term, arguments: List[List[Term]] = Nil): (Term, List[List[Term]]) = strip(term) match {
      case Apply(function, args) => application(function, args :: arguments)
      case TypeApply(function, _) => application(function, arguments)
      case function => (function, arguments)
    }

    val arguments = body match {
      case Varargs(clauses) => clauses
      case _ => report.errorAndAbort("Supply constructor clauses directly, separated by commas.", body)
    }
    val selector = strip('{ | }.asTerm).symbol
    val clauses = arguments.map { clause =>
      val term = clause.asTerm
      application(term) match {
        case (Select(receiver, "applyDynamic"), List(Literal(StringConstant(constructorName))) :: _) if strip(receiver).symbol == selector =>
          (constructorName, clause)
        case _ => report.errorAndAbort("Expected a constructor clause such as | zero() or | succ(n :: SelfRef).", clause)
      }
    }
    val names = clauses.map(_._1)
    if names.distinct.size != names.size then report.errorAndAbort("An inductive declaration has duplicate constructor names.", body)
    val declarationType = TypeRepr.of[Declaration[S]]
    val reserved = (declarationType.typeSymbol.methodMembers ++ declarationType.typeSymbol.fieldMembers).map(_.name).toSet
    names.find(reserved.contains).foreach(constructorName => report.errorAndAbort(s"Constructor '$constructorName' conflicts with a declaration member.", body))

    val compiledBody = Quoted.ofSeq(clauses.map(_._2))
    val resultType = names.foldLeft(declarationType)((parent, constructorName) => Refinement(parent, constructorName, TypeRepr.of[Constructor[S]]))
    // Quoting this generic factory call triggers recursive type widening in Scala 3.8.4.
    val factory = TypeApply(Select.unique('{ InductiveInfixSyntax }.asTerm, "build"), List(TypeTree.of[S]))
    val declaration = Apply(Apply(factory, List(parameters.asTerm, compiledBody.asTerm, Select.unique(name.asTerm, "value"))), List(sort.asTerm))
    TypeApply(Select.unique(declaration, "asInstanceOf"), List(Inferred(resultType))).asExpr
  }
}
