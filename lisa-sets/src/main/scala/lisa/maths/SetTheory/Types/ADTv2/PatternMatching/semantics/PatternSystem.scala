package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.ADTv2.encoding.{SemanticADT, SemanticConstructor}
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.utils.prooflib.BasicStepTactic.RightForall
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.SimpleDeducedSteps.InstantiateForall

/**
 * Semantic template for a compiled pattern-matching family.
 *
 * This is intentionally minimal. The existing implementation still routes through
 * `Map[SemanticConstructor, (Seq[Variable], Expr)]`; this trait names the target API
 * before the consumers migrate to it.
 */
trait PatternSystem[N <: Arity] {

  def patterns: Seq[Pattern[N]]

  def constructors: Seq[SemanticConstructor[N]] =
    patterns.map(_.semanticConstructor).distinct

  def patternsFor(constructor: SemanticConstructor[N]): Seq[Pattern[N]] =
    patterns.filter(_.semanticConstructor == constructor)

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
    seqOr(patterns.map(pattern =>
      existsSeq(
        pattern.variables2,
        pattern.freshBranchPremise /\ (p === pair(pattern.freshInputTerm, pattern.bodyAtFreshVars2))
      )
    ))

  def caseCoverage(term: Expr[Ind]): Expr[Prop] =
    seqOr(patterns.map(pattern =>
      existsSeq(
        pattern.variables2,
        pattern.freshBranchPremise /\ (term === pattern.freshInputTerm)
      )
    ))

  def supportsAutomaticCoverage: Boolean =
    patterns.forall(pattern => simplify(pattern.branchCondition) == ⊤) &&
      constructors.forall(constructor => patternsFor(constructor).size == 1)

  def coverage(domain: SemanticADT[N]): THM = {
    require(
      supportsAutomaticCoverage,
      "Automatic coverage is only available for constructor-only pattern systems with one unconditional branch per constructor."
    )
    val coveredTerm = variable[Ind]
    Lemma(∀(coveredTerm :: domain.term, simplify(caseCoverage(coveredTerm)))) { sp ?=>
      have(coveredTerm :: domain.term ==> simplify(caseCoverage(coveredTerm))) by
        InstantiateForall(coveredTerm)(domain.elim)
      thenHave(thesis) by RightForall
    }
  }
}

final case class ConstructorPatternSystem[N <: Arity](
    override val patterns: Seq[Pattern[N]]
) extends PatternSystem[N]

object ConstructorPatternSystem {
  def apply[N <: Arity](
      rawCases: Map[SemanticConstructor[N], (Seq[Variable[Ind]], Expr[Ind])]
  ): ConstructorPatternSystem[N] =
    ConstructorPatternSystem(rawCases.toSeq.map((constructor, value) =>
      ConstructorPattern(constructor, value._1, value._2)
    ))
}
