package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.syntax

import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.{
  ConstructorPattern,
  ConstructorPatternSystem,
  NestedConstructorPattern,
  NestedPatternSystem,
  PatternSystem
}
import lisa.maths.SetTheory.Types.ADTv2.interface.{ADT, Constructor}
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 * Mutable accumulator collecting constructor cases before validation and compilation.
 *
 * An ordered buffer is used (not a map) to support multiple patterns per constructor,
 * as needed for nested patterns like `cons(tru, tl)` and `cons(fals, tl)`.
 */
class CaseAccumulator[N <: Arity, T, R](val comp: R) {

  private val underlying = scala.collection.mutable
    .ArrayBuffer[(Constructor[N], Seq[Expr[Ind]], T)]()

  def +=(cons: Constructor[N], args: Seq[Expr[Ind]], value: T): Unit =
    underlying += ((cons, args, value))

  /**
   * Validates coverage and builds a [[PatternSystem]] in one step.
   *
   * Returns [[Left]] with an error message if:
   *   - any constructor of `adt` has no matching case,
   *   - a case refers to a constructor not in `adt`, or
   *   - an arity mismatch is detected.
   *
   * Produces a [[ConstructorPatternSystem]] when every case uses plain binder variables.
   * Falls back to a [[NestedPatternSystem]] when at least one case contains a concrete
   * term argument (e.g. `cons(tru, tl)`).
   */
  def compile(adt: ADT[N])(using ev: T =:= Expr[Ind]): Either[String, PatternSystem[N]] =
    validateCoverage(adt) match
      case Some(err) => Left(err)
      case None =>
        val isNested = underlying.exists { case (_, args, _) =>
          args.exists(!_.isInstanceOf[Variable[Ind]])
        }
        Right(if isNested then buildNestedSystem(ev) else buildConstructorSystem(ev))

  /**
   * Validates coverage and builds a constructor-keyed map for use in induction proofs.
   *
   * Unlike [[compile]], this method requires:
   *   - all arguments to be binder variables (no nested patterns), and
   *   - at most one pattern per constructor.
   *
   * Returns [[Left]] with an error message on any violation.
   */
  def validateAndBuild(adt: ADT[N]): Either[String, Map[Constructor[N], (Seq[Variable[Ind]], T)]] =
    validateCoverage(adt) match
      case Some(err) => Left(err)
      case None =>
        underlying.foldLeft[Either[String, Map[Constructor[N], (Seq[Variable[Ind]], T)]]](Right(Map.empty)) {
          case (Left(err), _) => Left(err)
          case (Right(acc), (cons, args, value)) =>
            if acc.contains(cons) then
              Left(s"Multiple patterns for ${cons.name} are not supported in induction proofs.")
            else
              val vars = args.collect { case v: Variable[Ind] => v }
              if vars.size != args.size then
                Left(s"Case ${cons.name}: induction requires variable binders, found a concrete term argument.")
              else
                Right(acc + (cons -> (vars, value)))
        }

  private def validateCoverage(adt: ADT[N]): Option[String] =
    val constructors = adt.constructors.toSet
    val caseConstructors = underlying.map(_._1).toSet

    val missing = constructors -- caseConstructors
    val unknown = caseConstructors -- constructors

    if missing.nonEmpty then
      Some(s"Case for ${missing.head.name} is missing.")
    else if unknown.nonEmpty then
      Some(s"${unknown.head.name} is not a constructor of ${adt.name}.")
    else
      underlying.foldLeft[Option[String]](None) { case (acc, (cons, args, _)) =>
        acc.orElse(
          Option.when(args.size != cons.semantic.arity)(
            s"Case ${cons.name}: ${args.size} argument(s) provided but constructor arity is ${cons.semantic.arity}."
          )
        )
      }

  private def buildConstructorSystem(ev: T =:= Expr[Ind]): ConstructorPatternSystem[N] =
    ConstructorPatternSystem(underlying.toSeq.map { case (cons, args, body) =>
      ConstructorPattern(cons.semantic, args.map(_.asInstanceOf[Variable[Ind]]), ev(body))
    })

  private def buildNestedSystem(ev: T =:= Expr[Ind]): NestedPatternSystem[N] =
    NestedPatternSystem(underlying.toSeq.map { case (cons, args, body) =>
      NestedConstructorPattern.fromArgs(
        cons.semantic,
        args.map {
          case v: Variable[Ind] => Left(v)
          case t                => Right(t)
        },
        ev(body)
      )
    })
}

@deprecated("Use CaseAccumulator", "ADTv2")
type CaseBuilder[N <: Arity, T, R] = CaseAccumulator[N, T, R]
