package lisa.maths.SetTheory.Types.ADT.PatternMatching.semantics

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADT.PatternMatching.PatternNode
import lisa.maths.SetTheory.Types.ADT.PatternMatching.PatternNode.Bind
import lisa.maths.SetTheory.Types.ADT.PatternMatching.PatternNode.Construct
import lisa.maths.SetTheory.Types.ADT.interface.ADT
import lisa.maths.SetTheory.Types.ADT.interface.Constructor
import lisa.maths.SetTheory.Types.ADT.interface.SpecializedADT

/**
 * A disjoint, exhaustive case analysis over resolved constructor patterns.
 */
private[ADT] sealed trait DecisionTree

/**
 * Compiles and renders the typed case analysis retained by a pattern system.
 */
private[ADT] object DecisionTree {

  /**
   * A sequence of constructor-field indices starting at the matched input.
   */
  type Occurrence = List[Int]

  /**
   * Inspects a value of the given specialized datatype, with one branch per constructor.
   */
  final case class Split(
      occurrence: Occurrence,
      domain: SpecializedADT[?],
      branches: Vector[(Constructor[?], DecisionTree)]
  ) extends DecisionTree

  /**
   * Selects a source clause and assigns its binders in their original order.
   */
  final case class Leaf(
      clauseIndex: Int,
      bindings: Vector[(Variable[Ind], Occurrence)]
  ) extends DecisionTree

  private final case class Column(occurrence: Occurrence, typ: Expr[Ind])
  private final case class Row(
      patterns: List[Option[PatternNode]],
      clauseIndex: Int,
      bindings: Vector[(Variable[Ind], Occurrence)]
  )

  /**
   * Checks exhaustiveness and disjointness while compiling the clauses in source order.
   */
  def compile(domain: SpecializedADT[?], clauses: Seq[Construct]): Either[String, DecisionTree] = {
    val rows = clauses.zipWithIndex.map { (pattern, index) =>
      Row(List(Some(pattern)), index, Vector.empty)
    }.toList
    new Compiler(clauses).split(List(Column(Nil, domain.term)), rows, 0, domain)
  }

  private final class Compiler(clauses: Seq[Construct]) {
    def split(
        columns: List[Column],
        rows: List[Row],
        index: Int,
        domain: SpecializedADT[?]
    ): Either[String, DecisionTree] = {
      val column = columns(index)
      val substitutions = domain.base.typeVariablesSeq.zip(domain.typeArgs).map((v, arg) => v := arg)
      val branches = Vector.newBuilder[(Constructor[?], DecisionTree)]
      val constructors = domain.base.constructors.iterator
      // An empty datatype produces an empty split even when there are no rows.
      while constructors.hasNext do
        val constructor = constructors.next()
        val children = constructor.semantic.semanticSignature.zipWithIndex.map { case ((_, typ), field) =>
          Column(column.occurrence :+ field, typ.substitute(substitutions*))
        }.toList
        val nextColumns = columns.patch(index, children, 1)
        val nextRows = rows.flatMap { row =>
          row.patterns(index) match
            case Some(Construct(head, _, arguments)) if head.id == constructor.id =>
              Some(row.copy(patterns = row.patterns.patch(index, arguments.map(Some(_)), 1)))
            case Some(_: Construct) => None
            case binder =>
              val bindings = binder match
                case Some(Bind(v, _)) => row.bindings :+ (v -> column.occurrence)
                case _ => row.bindings
              Some(
                row.copy(
                  patterns = row.patterns.patch(index, List.fill(children.size)(None), 1),
                  bindings = bindings
                )
              )
        }
        if nextRows.isEmpty then
          val location = occurrenceName(column.occurrence)
          return Left(s"Case for ${constructor.name} is missing at $location; the patterns are not exhaustive.")
        descend(nextColumns, nextRows, column.occurrence) match
          case Left(error) => return Left(error)
          case Right(tree) => branches += constructor -> tree
      Right(Split(column.occurrence, domain, branches.result()))
    }

    private def descend(columns: List[Column], rows: List[Row], lastSplit: Occurrence): Either[String, DecisionTree] = {
      val index = columns.indices.find { i =>
        rows.exists(_.patterns(i).exists(_.isInstanceOf[Construct]))
      }
      index match
        case Some(i) =>
          ADT.unapply(columns(i).typ) match
            case Some((adt, arguments)) => split(columns, rows, i, new SpecializedADT(adt, arguments))
            case None => Left(s"Cannot inspect a constructor at ${occurrenceName(columns(i).occurrence)} of type ${columns(i).typ}.")
        case None =>
          rows match
            case scala.collection.immutable.::(row, Nil) =>
              val remaining = columns.zip(row.patterns).collect { case (column, Some(Bind(v, _))) =>
                v -> column.occurrence
              }
              val positions = (row.bindings ++ remaining).toMap
              val bindings = clauses(row.clauseIndex).binders.map(v => v -> positions(v)).toVector
              Right(Leaf(row.clauseIndex, bindings))
            case Nil => Left(s"A case is missing at ${occurrenceName(lastSplit)}; the patterns are not exhaustive.")
            case _ =>
              val matched = rows.map(row => clauses(row.clauseIndex))
              val unconditional = matched.forall(_.arguments.forall(_.isInstanceOf[Bind]))
              val prefix =
                if unconditional then s"Overlapping unconditional cases for ${matched.head.constructor.name}. "
                else ""
              Left(s"${prefix}Clauses ${rows.map(_.clauseIndex).mkString(", ")} overlap at ${occurrenceName(lastSplit)}.")
    }
  }

  /**
   * Renders an occurrence for diagnostics.
   */
  def occurrenceName(occurrence: Occurrence): String =
    if occurrence.isEmpty then "x" else "x." + occurrence.mkString(".")

  /**
   * Renders a resolved pattern without using names as constructor identities.
   */
  def showPattern(pattern: PatternNode): String = pattern match
    case Bind(v, _) => v.toString
    case Construct(constructor, _, Nil) => constructor.name
    case Construct(constructor, _, arguments) => s"${constructor.name}(${arguments.map(showPattern).mkString(", ")})"

  /**
   * Renders the retained tree with its constructor branches and source-clause bindings.
   */
  def render(tree: DecisionTree, indent: String = ""): String = tree match
    case Leaf(index, bindings) =>
      val assignments = bindings.map((v, path) => s"$v = ${occurrenceName(path)}").mkString(", ")
      s"${indent}clause $index${if bindings.isEmpty then "" else s" {$assignments}"}"
    case Split(occurrence, domain, branches) =>
      val children = branches.map { (constructor, child) =>
        s"$indent  ${constructor.name}:\n${render(child, indent + "    ")}"
      }
      (s"${indent}split ${occurrenceName(occurrence)} : ${domain.term}" +: children).mkString("\n")
}
