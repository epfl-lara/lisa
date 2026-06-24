package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.constructor

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.encoding.SemanticADT
import lisa.maths.SetTheory.Types.ADTv2.encoding.SemanticConstructor
import lisa.maths.SetTheory.Types.ADTv2.interface.ADT
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.{ConstructorHeadPattern, Pattern, PatternSystem}
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.TypeSubstitution
import lisa.utils.debug.Time
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.utils.prooflib.BasicStepTactic.RightForall
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.SimpleDeducedSteps.InstantiateForall

private[PatternMatching] final case class ConstructorPattern[N <: Arity](
    semanticConstructor: SemanticConstructor[N],
    binders: Seq[Variable[Ind]],
    body: Expr[Ind],
    override val branchCondition: Expr[Prop] = ⊤,
    override val typeSubstitutions: Seq[TypeSubstitution] = Seq.empty,
    override val specializedAdtTerm: Expr[Ind]
) extends ConstructorHeadPattern[N] {
  override def withBody(newBody: Expr[Ind]): Pattern[N] = copy(body = newBody)
}

private[PatternMatching] final case class ConstructorPatternSystem[N <: Arity](
    domain: SemanticADT[N],
    override val patterns: Seq[ConstructorHeadPattern[N]],
    specializedAdtTerm: Expr[Ind]
) extends PatternSystem[N] {
  override def constructors: Seq[SemanticConstructor[N]] =
    patterns.map(_.semanticConstructor).distinct

  override def patternsFor(constructor: SemanticConstructor[N]): Seq[Pattern[N]] =
    patterns.filter(_.semanticConstructor == constructor)

  override lazy val coverage: THM = Time.measure(s"ConstructorPatternSystem/Coverage") {
    require(
      supportsAutomaticCoverage,
      "Automatic coverage is only available for constructor-only pattern systems with one unconditional branch per constructor."
    )
    val coveredTerm = variable[Ind]
    Lemma(∀(coveredTerm :: specializedAdtTerm, simplify(caseCoverage(coveredTerm)))) { sp ?=>
      have(coveredTerm :: domain.term ==> simplify(caseCoverage(coveredTerm))) by
        InstantiateForall(coveredTerm)(ConstructorPatternSystem.domainElim(domain, specializedAdtTerm))
      thenHave(thesis) by RightForall
    }
  }

  override def incompatible(pattern1: Pattern[N], pattern2: Pattern[N]): THM =
    incompatibleCache.getOrElseUpdate(
      (pattern1, pattern2),
      Time.measure(s"ConstructorPattern/Incompatible") {
        require(pattern1 != pattern2, "incompatible is only meaningful for distinct patterns.")
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
        require(
          !constructorPattern1.hasSameHeadAs(constructorPattern2),
          s"ConstructorPatternSystem cannot derive incompatibility for same-head patterns (${pattern1.name}); this system expects at most one pattern per constructor."
        )

        Lemma(
          (constructorPattern1.branchPremise1 /\ constructorPattern2.freshBranchPremise) ==>
            !(constructorPattern1.inputTerm1 === constructorPattern2.inputTerm2)
        ) {
          have(thesis) by Tautology.from(constructorPattern1.disjointness(constructorPattern2))
        }
      }
    )

  override def branchSelectionFor(constructor: SemanticConstructor[N], term: Expr[Ind]): THM =
    branchSelectionCache.getOrElseUpdate(
      (constructor, term),
      Time.measure(s"Pattern/Branch selection") {
        val constructorPatterns = patternsFor(constructor)
        require(
          constructorPatterns.size == 1,
          s"ConstructorPatternSystem expects exactly one pattern for constructor ${constructor.name}."
        )
        val pattern = constructorPatterns.head
        Lemma(
          forallSeq(
            constructor.variables2,
            (wellTypedFormula(constructor.semanticSignature2) /\ (term === constructor.appliedTerm2)) ==>
              (pattern.freshBranchCondition /\ (term === pattern.freshInputTerm))
          )
        ) {
          have(thesis) by Tautology
        }
      }
    )
}

private[PatternMatching] object ConstructorPatternSystem {
  private def domainElim[N <: Arity](domain: SemanticADT[N], specializedAdtTerm: Expr[Ind]): THM =
    if specializedAdtTerm == domain.term then domain.elim
    else
      val base = domain.elim
      val substitutions = domain.typeVariablesSeq.zip(ADT.unapply(specializedAdtTerm).map(_._2).getOrElse(Seq.empty)).map((v, arg) => v := arg)
      Lemma(base.statement.substitute(substitutions*)) { sp ?=>
        have(thesis) by Restate.from(base.of(substitutions*))
      }

  def apply[N <: Arity](
      rawCases: Map[SemanticConstructor[N], (Seq[Variable[Ind]], Expr[Ind])]
  ): ConstructorPatternSystem[N] =
    ConstructorPatternSystem(
      ADT.getADT(rawCases.head._1.adtName).get.semantic.asInstanceOf[SemanticADT[N]],
      rawCases.toSeq.map((constructor, value) => ConstructorPattern(constructor, value._1, value._2, specializedAdtTerm = constructor.adtTerm)),
      rawCases.head._1.adtTerm
    )
}
