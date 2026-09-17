package lisa.maths.SetTheory.Types.ADTv2.tactics

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.interface.ADT
import lisa.maths.SetTheory.Types.ADTv2.interface.SpecializedADT
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST._

/**
 * Recovers the [[TypeExpr]] / [[SpecializedADT]] structure of a typing term such as
 * `ADT(T1, ..., Tn)`, used by the induction tactic to infer the ADT a variable is
 * typed with.
 */
object TypeTermParser {

  // TODO: switch from string-parsing to structure reading
  // in particular for specialized ADTs

  /**
   * Parses a type printed as a string repr (e.g. `"List[Nat]"`) into a [[TypeExpr]].
   * Returns [[None]] when the repr is malformed (unbalanced brackets, empty args, ...).
   */
  def parseTypeExprRepr(repr: String): Option[TypeExpr] =
    def splitTopLevelArgs(raw: String): Option[Seq[String]] =
      if raw.isEmpty then Some(Seq.empty)
      else
        val args = scala.collection.mutable.ArrayBuffer.empty[String]
        val current = new StringBuilder
        var depth = 0
        var i = 0
        var bad = false
        val n = raw.length
        while i < n && !bad do
          raw.charAt(i) match
            case '[' =>
              depth += 1
              current.append('[')
            case ']' =>
              depth -= 1
              if depth < 0 then bad = true
              else current.append(']')
            case ',' if depth == 0 =>
              val arg = current.toString.trim
              if arg.isEmpty then bad = true
              else
                args += arg
                current.clear()
            case ch => current.append(ch)
          i += 1

        if bad || depth != 0 then None
        else
          val lastArg = current.toString.trim
          if lastArg.isEmpty then None
          else
            args += lastArg
            Some(args.toSeq)

    val s = repr.trim
    if s.isEmpty then None
    else
      val bracketIdx = s.indexOf('[')
      if bracketIdx < 0 then Some(TypeRef(s))
      else if !s.endsWith("]") then None
      else
        val name = s.substring(0, bracketIdx)
        val inner = s.substring(bracketIdx + 1, s.length - 1)
        splitTopLevelArgs(inner).flatMap { args =>
          args
            .foldLeft[Option[Seq[TypeExpr]]](Some(Seq.empty)) { (acc, arg) =>
              acc.flatMap(seq => parseTypeExprRepr(arg).map(seq :+ _))
            }
            .map(parsed => TypeApply(name, parsed))
        }

  /**
   * Recovers the [[TypeExpr]] of a typing term, recognising registered ADTs by their
   * semantic id and falling back to the constant's string repr otherwise.
   */
  def typeTermToTypeExpr(term: Expr[Ind]): Option[TypeExpr] = {

    def parseTypeExprArgs(args: Seq[Expr[?]]): Option[Seq[TypeExpr]] =
      args.foldLeft[Option[Seq[TypeExpr]]](Some(Seq.empty))((acc, arg) => acc.flatMap(parsed => typeTermToTypeExpr(arg.asInstanceOf[Expr[Ind]]).map(parsed :+ _)))

    val (head, args) = unfoldAllApp(term)
    val maybeADT = ADT.allADTs.collectFirst {
      case adt if (head match
            case c: Constant[Ind] @unchecked => c.id == adt.semantic.id
            case _ => false
          ) =>
        adt
    }

    maybeADT
      .flatMap(adt => parseTypeExprArgs(args).map(typeArgs => if typeArgs.isEmpty then TypeRef(adt.name) else TypeApply(adt.name, typeArgs)))
      .orElse(
        head match
          case c: Constant[Ind] @unchecked =>
            parseTypeExprArgs(args).flatMap(parsedArgs =>
              parseTypeExprRepr(c.id.name).map {
                case TypeRef(name) if parsedArgs.nonEmpty => TypeApply(name, parsedArgs)
                case base if parsedArgs.isEmpty => base
                case _ => TypeApply(c.id.name, parsedArgs)
              }
            )
          case _ => None
      )
  }

  /**
   * Infers the [[SpecializedADT]] a typing term refers to, if any.
   */
  def inferADTFromTypeTerm(typeTerm: Expr[Ind]): Option[SpecializedADT[?]] =
    typeTermToTypeExpr(typeTerm)
      .flatMap((tpe: TypeExpr) => ADT.unapply(tpe))
      .map { case (adt, typeArgs) =>
        adt.specialize(typeArgs.map(typeExprToTerm)*)
      }
}
