package lisa.maths.SetTheory.Types.ADT.PatternMatching.syntax

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.PatternMatching.PatternValidation
import lisa.maths.SetTheory.Types.ADT.PatternMatching.semantics.Clause
import lisa.maths.SetTheory.Types.ADT.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADT.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADT.interface.Constructor
import lisa.maths.SetTheory.Types.ADT.interface.SpecializedADT

/**
 * Collects cases and retains their resolved patterns and proof-facing binders.
 */
class CaseAccumulator[T, R](val comp: R) {

  private sealed trait Entry
  private final case class Raw(constructor: Constructor[?], arguments: Seq[Expr[Ind]], payload: T) extends Entry
  private final case class Prepared(clause: Clause[T]) extends Entry

  private val underlying = scala.collection.mutable.ArrayBuffer.empty[Entry]

  /**
   * Collects a function case until its domain is known.
   */
  def +=(cons: Constructor[?], args: Seq[Expr[Ind]], value: T): Unit =
    underlying += Raw(cons, args, value)

  /**
   * Retains the exact pattern view used to construct an induction case's assumptions.
   */
  private[syntax] def addResolved(pattern: Pattern, value: T): Unit =
    underlying += Prepared(Clause(pattern, value))

  /**
   * Resolves remaining cases and compiles their shared pattern structure without changing payloads.
   */
  def compile(adt: SpecializedADT[?], avoid: T => Seq[Expr[?]] = _ => Seq.empty): Either[String, PatternSystem[T]] = {
    val sharedAvoid = underlying.toSeq.flatMap {
      case Raw(_, _, payload) => avoid(payload)
      case Prepared(clause) => avoid(clause.payload)
    }
    val clauses = Vector.newBuilder[Clause[T]]
    var index = 0
    while index < underlying.size do
      val resolved = underlying(index) match
        case Raw(constructor, arguments, payload) =>
          PatternValidation.resolveCase(constructor, arguments, adt).map { root =>
            Clause(Pattern.fromResolved(root, sharedAvoid), payload)
          }
        case Prepared(clause) => Right(clause)
      resolved match
        case Left(error) => return Left(error)
        case Right(clause) =>
          underlying(index) = Prepared(clause)
          clauses += clause
      index += 1
    PatternSystem.compile(adt, clauses.result())
  }
}
