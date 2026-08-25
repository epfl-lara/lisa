package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.syntax

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.induction.InductionBranchSystem
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.induction.PatternToInduction
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.constructor.ConstructorPattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.constructor.ConstructorPatternSystem
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.nested.NestedPatternSystem
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.nested.NestedConstructorPattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.interface.ADT
import lisa.maths.SetTheory.Types.ADTv2.interface.Constructor
import lisa.maths.SetTheory.Types.ADTv2.interface.SpecializedADT
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.substitutionsFromArgs

/**
 * Mutable accumulator collecting constructor cases before validation and compilation.
 *
 * An ordered buffer is used (not a map) to support multiple patterns per constructor,
 * as needed for nested patterns like `cons(tru, tl)` and `cons(fals, tl)`.
 */
class CaseAccumulator[T, R](val comp: R) {

  private val underlying = scala.collection.mutable
    .ArrayBuffer[(Constructor[?], Seq[Expr[Ind]], T)]()

  def +=(cons: Constructor[?], args: Seq[Expr[Ind]], value: T): Unit =
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
  def compile(adt: SpecializedADT[?])(using ev: T =:= Expr[Ind]): Either[String, PatternSystem] =
    validateCoverage(adt.base) match
      case Some(err) => Left(err)
      case None => Right(buildPatternSystem(adt, bodyAt = ev))

  def compileForInduction(
      adt: SpecializedADT[?]
  ): Either[String, InductionBranchSystem[T]] =
    validateCoverage(adt.base) match
      case Some(err) => Left(err)
      case None => PatternToInduction.compile(
          adt,
          buildPatternSystem(adt, bodyAt = _ => ∅),
          underlying.toSeq.map(_._3)
        )

  private def validateCoverage(adt: ADT[?]): Option[String] =
    val constructors: Set[Constructor[?]] = adt.constructors.toSet
    val caseConstructors: Set[Constructor[?]] = underlying.map(_._1).toSet

    val missing = constructors -- caseConstructors
    val unknown = caseConstructors -- constructors

    if missing.nonEmpty then Some(s"Case for ${missing.head.name} is missing.")
    else if unknown.nonEmpty then Some(s"${unknown.head.name} is not a constructor of ${adt.name}.")
    else
      underlying.foldLeft[Option[String]](None) { case (acc, (cons, args, _)) =>
        acc.orElse(
          Option.when(args.size != cons.semantic.arity)(
            s"Case ${cons.name}: ${args.size} argument(s) provided but constructor arity is ${cons.semantic.arity}."
          )
        )
      }

  private def buildConstructorSystem(
      adt: SpecializedADT[?],
      typeSubstitutions: Seq[lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.TypeSubstitution],
      bodyAt: T => Expr[Ind]
  ): ConstructorPatternSystem =
    ConstructorPatternSystem(
      domain = adt.base.semantic,
      patterns = underlying.toSeq.map { case (cons, args, body) =>
        ConstructorPattern(
          cons.semantic,
          args.map(_.asInstanceOf[Variable[Ind]]),
          bodyAt(body).substitute(typeSubstitutions*),
          typeSubstitutions = typeSubstitutions,
          specializedAdtTerm = adt.term
        )
      },
      specializedAdtTerm = adt.term
    )

  private def buildNestedSystem(
      adt: SpecializedADT[?],
      typeSubstitutions: Seq[lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.TypeSubstitution],
      bodyAt: T => Expr[Ind]
  ): NestedPatternSystem =
    val patterns = underlying.toSeq.map { case (cons, args, body) =>
      NestedConstructorPattern.fromArgs(
        cons.semantic,
        args.map {
          case v: Variable[Ind] => Left(v)
          case t => Right(t.substitute(typeSubstitutions*).asInstanceOf[Expr[Ind]])
        },
        bodyAt(body).substitute(typeSubstitutions*).asInstanceOf[Expr[Ind]],
        typeSubstitutions,
        adt.term
      )
    }
    
    // A non-nullary (deeply nested) guard ⇒ multi-level system; otherwise the
    // restricted nullary-split system (which also supports recursion).
    {
      NestedPatternSystem(adt.base.semantic, patterns, typeSubstitutions, adt.term)
    }

  private def buildPatternSystem(
      adt: SpecializedADT[?],
      bodyAt: T => Expr[Ind]
  ): PatternSystem =
    {
      val typeSubstitutions =
        substitutionsFromArgs("ADT", adt.base.name, adt.base.typeVariablesSeq, adt.typeArgs)
          .filter(substitution => substitution._2.asInstanceOf[Expr[Ind]] != substitution._1.asInstanceOf[Variable[Ind]])
      val isNested = underlying.exists { case (_, args, _) =>
        args.exists(!_.isInstanceOf[Variable[Ind]])
      }
      val system =
        if isNested then buildNestedSystem(adt, typeSubstitutions, bodyAt)
        else buildConstructorSystem(adt, typeSubstitutions, bodyAt)
      system
    }
}
