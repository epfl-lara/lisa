package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.syntax

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.induction.InductionBranchSystemWithPayload
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
import lisa.utils.debug.Time
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
  def compile(adt: SpecializedADT[N])(using ev: T =:= Expr[Ind]): Either[String, PatternSystem[N]] =
    validateCoverage(adt.base) match
      case Some(err) => Left(err)
      case None => Right(buildPatternSystem(adt, bodyAt = ev))

  def compilePatterns(adt: SpecializedADT[N]): Either[String, PatternSystem[N]] =
    validateCoverage(adt.base) match
      case Some(err) => Left(err)
      case None =>
        Right(buildPatternSystem(adt, bodyAt = _ => ∅))

  def compileForInduction(
      adt: SpecializedADT[N]
  ): Either[String, InductionBranchSystemWithPayload[N, T]] =
    for
      patternSystem <- compilePatterns(adt)
      compiled <- PatternToInduction.compileWithPayload(
        adt,
        patternSystem,
        underlying.toSeq.map(_._3)
      )
    yield compiled

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
            if acc.contains(cons) then Left(s"Multiple patterns for ${cons.name} are not supported in induction proofs.")
            else
              val vars = args.collect { case v: Variable[Ind] => v }
              if vars.size != args.size then Left(s"Case ${cons.name}: induction requires variable binders, found a concrete term argument.")
              else Right(acc + (cons -> (vars, value)))
        }

  private def validateCoverage(adt: ADT[N]): Option[String] =
    val constructors = adt.constructors.toSet
    val caseConstructors = underlying.map(_._1).toSet

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
      adt: SpecializedADT[N],
      typeSubstitutions: Seq[lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.TypeSubstitution],
      bodyAt: T => Expr[Ind]
  ): ConstructorPatternSystem[N] =
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
      adt: SpecializedADT[N],
      typeSubstitutions: Seq[lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.TypeSubstitution],
      bodyAt: T => Expr[Ind]
  ): PatternSystem[N] =
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
    Time.measure(s"PatternSystem build NestedPatternSystem") {
      NestedPatternSystem(adt.base.semantic, patterns, typeSubstitutions, adt.term)
    }

  private def buildPatternSystem(
      adt: SpecializedADT[N],
      bodyAt: T => Expr[Ind]
  ): PatternSystem[N] =
    Time.measure(s"PatternSystem compilation") {
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
