package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.ADTv2.encoding.{SemanticADT, SemanticConstructor}
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 * A constructor-headed pattern where some arguments are compiled into branch
 * guards instead of being kept as user binders.
 *
 * For example, `cons(tru, tl)` is represented with binders `(_cons0, tl)` and
 * branch condition `_cons0 === tru`.
 */
final case class NestedConstructorPattern[N <: Arity](
    semanticConstructor: SemanticConstructor[N],
    binders: Seq[Variable[Ind]],
    body: Expr[Ind],
    override val branchCondition: Expr[Prop]
) extends ConstructorHeadPattern[N] {
  override def withBody(newBody: Expr[Ind]): Pattern[N] = copy(body = newBody)
}

object NestedConstructorPattern {

  /**
   * Builds a nested pattern from a mixed argument list.
   *
   * `Left(v)` keeps `v` as a binder.
   * `Right(t)` introduces a fresh binder and adds an equality guard against `t`.
   */
  def fromArgs[N <: Arity](
      constructor: SemanticConstructor[N],
      args: Seq[Either[Variable[Ind], Expr[Ind]]],
      body: Expr[Ind]
  ): NestedConstructorPattern[N] =
    val binders: Seq[Variable[Ind]] = args.zipWithIndex.map {
      case (Left(v), _)  => v
      case (Right(_), i) => variable[Ind](s"${constructor.name}/arg$i")
    }
    val conditions: Seq[Expr[Prop]] = args.zip(binders).collect {
      case (Right(term), binder) => binder === term
    }
    val condition = conditions match
      case Nil          => ⊤
      case head +: tail => tail.foldLeft(head)(_ /\ _)
    NestedConstructorPattern(constructor, binders, body, condition)
}

/**
 * Pattern system supporting several guarded branches for the same constructor.
 *
 * Proof obligations are intentionally left open for now.
 */
final case class NestedPatternSystem[N <: Arity](
    override val patterns: Seq[ConstructorHeadPattern[N]]
) extends PatternSystem[N] {
  override def constructors: Seq[SemanticConstructor[N]] =
    patterns.map(_.semanticConstructor).distinct

  override def patternsFor(constructor: SemanticConstructor[N]): Seq[Pattern[N]] =
    patterns.filter(_.semanticConstructor == constructor)

  override def supportsAutomaticCoverage: Boolean = false

  override def coverage(domain: SemanticADT[N]): THM = {
    val coveredTerm = variable[Ind]
    Lemma(∀(coveredTerm :: domain.term, simplify(caseCoverage(coveredTerm)))) { sp ?=>
      have(thesis) by Sorry
    }
  }

  override def branchSelectionFor(constructor: SemanticConstructor[N], term: Expr[Ind]): THM =
    Lemma(
      forallSeq(
        constructor.variables2,
        (wellTypedFormula(constructor.semanticSignature2) /\ (term === constructor.appliedTerm2)) ==>
          seqOr(patternsFor(constructor).map(pattern =>
            pattern.freshBranchCondition /\ (term === pattern.freshInputTerm)
          ))
      )
    ) {
      have(thesis) by Sorry
    }

  override def incompatible(pattern1: Pattern[N], pattern2: Pattern[N]): THM = {
    val constructorPattern1 = pattern1 match
      case pattern: ConstructorHeadPattern[N] => pattern
      case _ =>
        throw new IllegalArgumentException(
          s"Pattern ${pattern1.name} is not constructor-headed."
        )
    val constructorPattern2 = pattern2 match
      case pattern: ConstructorHeadPattern[N] => pattern
      case _ =>
        throw new IllegalArgumentException(
          s"Pattern ${pattern2.name} is not constructor-headed."
        )

    Lemma(
      (constructorPattern1.branchPremise1 /\ constructorPattern2.freshBranchPremise) ==>
        !(constructorPattern1.inputTerm1 === constructorPattern2.inputTerm2)
    ) {
      have(thesis) by Sorry
    }
  }
}

object NestedPatternSystem {
  def fromMixedArgs[N <: Arity](
      rawCases: Seq[(SemanticConstructor[N], Seq[Either[Variable[Ind], Expr[Ind]]], Expr[Ind])]
  ): NestedPatternSystem[N] =
    NestedPatternSystem(rawCases.map((constructor, args, body) =>
      NestedConstructorPattern.fromArgs(constructor, args, body)
    ))
}
