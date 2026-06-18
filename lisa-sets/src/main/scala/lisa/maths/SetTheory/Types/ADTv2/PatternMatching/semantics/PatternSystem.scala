package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics

import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.encoding.SemanticConstructor
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.utils.prooflib.ProofTacticLib.Arity


/**
 * Generic semantic template for a compiled pattern-matching family.
 */
trait PatternSystem[N <: Arity] {

  def patterns: Seq[Pattern[N]]

  def constructors: Seq[SemanticConstructor[N]]

  def patternsFor(constructor: SemanticConstructor[N]): Seq[Pattern[N]]

  def patternFor(constructor: SemanticConstructor[N]): Pattern[N] =
    patternsFor(constructor) match
      case Seq(pattern) => pattern
      case Seq() =>
        throw new IllegalArgumentException(
          s"No pattern registered for constructor ${constructor.name}."
        )
      case _ =>
        throw new IllegalArgumentException(
          s"Constructor ${constructor.name} has several patterns; use patternsFor instead of patternFor."
        )

  def caseMembership(p: Expr[Ind]): Expr[Prop] =
    seqOr(
      patterns.map(pattern =>
        existsSeq(
          pattern.variables2,
          pattern.freshBranchPremise /\ (p === pair(pattern.freshInputTerm, pattern.bodyAtFreshVars2))
        )
      )
    )

  def caseCoverage(term: Expr[Ind]): Expr[Prop] =
    seqOr(
      patterns.map(pattern =>
        existsSeq(
          pattern.variables2,
          pattern.freshBranchPremise /\ (term === pattern.freshInputTerm)
        )
      )
    )

  def supportsAutomaticCoverage: Boolean =
    patterns.forall(pattern => simplify(pattern.branchCondition) == ⊤) &&
      constructors.forall(constructor => patternsFor(constructor).size == 1)

  protected val incompatibleCache = collection.mutable.Map.empty[(Pattern[N], Pattern[N]), THM]
  protected val branchSelectionCache = collection.mutable.Map.empty[(SemanticConstructor[N], Expr[Ind]), THM]

  lazy val coverage: THM

  def branchSelectionFor(constructor: SemanticConstructor[N], term: Expr[Ind]): THM

  def incompatible(pattern1: Pattern[N], pattern2: Pattern[N]): THM

  lazy val debugTheorems: Seq[(String, Either[String, THM])] = {
    val coverageFact = "coverage" -> Right(coverage)
    val selectorFacts = constructors.map(constructor =>
      val term = variable[Ind](s"${constructor.name}/debugTerm")
      s"branchSelectionFor(${constructor.name})" -> Right(branchSelectionFor(constructor, term))
    )
    val incompatibilityFacts = patterns.zipWithIndex.flatMap { case (pattern1, index1) =>
      patterns.zipWithIndex.collect {
        case (pattern2, index2) if index1 < index2 =>
          val label = s"incompatible(${pattern1.name}#$index1, ${pattern2.name}#$index2)"
          try label -> Right(incompatible(pattern1, pattern2))
          catch case exception: IllegalArgumentException => label -> Left(exception.getMessage)
      }
    }
    coverageFact +: (selectorFacts ++ incompatibilityFacts)
  }

  lazy val debugDump: Unit = {
    println(s"===== PatternSystem Debug (${getClass.getSimpleName}) =====")
    println(s"constructors: ${constructors.map(_.name).mkString(", ")}")
    println(s"patterns: ${patterns.map(_.name).mkString(", ")}")
    debugTheorems.foreach {
      case (label, Right(theorem)) =>
        println(s"[$label] ${theorem.statement}")
      case (label, Left(message)) =>
        println(s"[$label] skipped: $message")
    }
    println("")
  }
}

object PatternSystem {
  def constructorCases[N <: Arity](
      patterns: Seq[Pattern[N]]
  ): Map[SemanticConstructor[N], Seq[Pattern[N]]] =
    patterns
      .foldLeft(Map.empty[SemanticConstructor[N], Vector[Pattern[N]]]) { case (acc, pattern) =>
        pattern match
          case constructorHead: ConstructorHeadPattern[N] =>
            val c = constructorHead.semanticConstructor
            acc.updated(c, acc.getOrElse(c, Vector.empty) :+ pattern)
          case _ =>
            throw new IllegalArgumentException(
              s"Pattern ${pattern.name} is not constructor-headed."
            )
      }
      .iterator
      .map((c, ps) => c -> ps.toSeq)
      .toMap
}
