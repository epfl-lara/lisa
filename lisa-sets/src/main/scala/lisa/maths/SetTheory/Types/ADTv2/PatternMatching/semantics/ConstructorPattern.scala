package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.Pair
import lisa.maths.SetTheory.Types.ADTv2.encoding.{SemanticADT, SemanticConstructor}
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.{altEqualityTransitivity, constructorTagDisequality}
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.utils.prooflib.BasicStepTactic.RightForall
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.SimpleDeducedSteps.InstantiateForall

final case class ConstructorPattern[N <: Arity](
    semanticConstructor: SemanticConstructor[N],
    binders: Seq[Variable[Ind]],
    body: Expr[Ind],
    override val branchCondition: Expr[Prop] = ⊤
) extends ConstructorHeadPattern[N] {
  override def withBody(newBody: Expr[Ind]): Pattern[N] = copy(body = newBody)
}

final case class ConstructorPatternSystem[N <: Arity](
    override val patterns: Seq[ConstructorHeadPattern[N]]
) extends PatternSystem[N] {
  override def constructors: Seq[SemanticConstructor[N]] =
    patterns.map(_.semanticConstructor).distinct

  override def patternsFor(constructor: SemanticConstructor[N]): Seq[Pattern[N]] =
    patterns.filter(_.semanticConstructor == constructor)

  override def coverage(domain: SemanticADT[N]): THM = {
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

  override def incompatible(pattern1: Pattern[N], pattern2: Pattern[N]): THM = {
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
      val branch1 = assume(constructorPattern1.branchPremise1 /\ constructorPattern2.freshBranchPremise)
      val branch1Typed = have(constructorPattern1.branchPremise1) by Tautology.from(branch1)
      val branch2Typed = have(constructorPattern2.freshBranchPremise) by Tautology.from(branch1)

      assume(constructorPattern1.inputTerm1 === constructorPattern2.inputTerm2)
      val inputsEqual = have(constructorPattern1.inputTerm1 === constructorPattern2.inputTerm2) by Hypothesis

      have(constructorPattern1.shortDefinition.statement.right.head) by Tautology.from(constructorPattern1.shortDefinition)
      val p1ShortAtVars1 = constructorPattern1.variables1.foldLeft(lastStep)((_, v1) =>
        lastStep.statement.right.head match
          case forall(v, phi) =>
            thenHave(phi.substituteUnsafe(Map(v -> v1)).asInstanceOf[Expr[Prop]]) by InstantiateForall(v1)
          case _ => throw UnreachableException
      )
      val p1StructuralEq = p1ShortAtVars1.statement.right.head match
        case _ ==> consequent => have(consequent) by Tautology.from(p1ShortAtVars1, branch1Typed)
        case _                => throw UnreachableException

      have(constructorPattern2.shortDefinition.statement.right.head) by Tautology.from(constructorPattern2.shortDefinition)
      val p2ShortAtVars2 = constructorPattern2.variables2.foldLeft(lastStep)((_, v2) =>
        lastStep.statement.right.head match
          case forall(v, phi) =>
            thenHave(phi.substituteUnsafe(Map(v -> v2)).asInstanceOf[Expr[Prop]]) by InstantiateForall(v2)
          case _ => throw UnreachableException
      )
      val p2StructuralEq = p2ShortAtVars2.statement.right.head match
        case _ ==> consequent => have(consequent) by Tautology.from(p2ShortAtVars2, branch2Typed)
        case _                => throw UnreachableException

      val p1StructuralToApplied = have(constructorPattern1.structuralTerm1 === constructorPattern1.inputTerm1) by
        Congruence.from(p1StructuralEq)
      val p1StructuralEqP2Applied = have(constructorPattern1.structuralTerm1 === constructorPattern2.inputTerm2) by
        Tautology.from(
          altEqualityTransitivity of (
            x := constructorPattern1.structuralTerm1,
            y := constructorPattern1.inputTerm1,
            z := constructorPattern2.inputTerm2
          ),
          p1StructuralToApplied,
          inputsEqual
        )
      val structuralEq = have(constructorPattern1.structuralTerm1 === constructorPattern2.structuralTerm2) by Tautology.from(
        altEqualityTransitivity of (
          x := constructorPattern1.structuralTerm1,
          y := constructorPattern2.inputTerm2,
          z := constructorPattern2.structuralTerm2
        ),
        p1StructuralEqP2Applied,
        p2StructuralEq
      )
      val tagsFromStructuralEq = have(
        constructorPattern1.structuralTerm1 === constructorPattern2.structuralTerm2 |-
          (constructorPattern1.tagTerm1 === constructorPattern2.tagTerm2) /\
          (constructorPattern1.subterm1 === constructorPattern2.subterm2)
      ) by Tautology.from(
        Pair.extensionality of (
          a := constructorPattern1.tagTerm1,
          b := constructorPattern1.subterm1,
          c := constructorPattern2.tagTerm2,
          d := constructorPattern2.subterm2
        )
      )
      val tagsEqual = have(constructorPattern1.tagTerm1 === constructorPattern2.tagTerm2) by
        Tautology.from(structuralEq, tagsFromStructuralEq)
      val minTag = Math.min(constructorPattern1.semanticConstructor.underlying.tag, constructorPattern2.semanticConstructor.underlying.tag)
      val maxTag = Math.max(constructorPattern1.semanticConstructor.underlying.tag, constructorPattern2.semanticConstructor.underlying.tag)
      val tagsDifferent = have(!(constructorPattern1.tagTerm1 === constructorPattern2.tagTerm2)) by Tautology.from(
        constructorTagDisequality(constructorPattern1.tagTerm1, constructorPattern2.tagTerm2, minTag, maxTag)
      )
      have(thesis) by Tautology.from(tagsEqual, tagsDifferent)
    }
  }

  override def branchSelectionFor(constructor: SemanticConstructor[N], term: Expr[Ind]): THM = {
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
}

object ConstructorPatternSystem {
  def apply[N <: Arity](
      rawCases: Map[SemanticConstructor[N], (Seq[Variable[Ind]], Expr[Ind])]
  ): ConstructorPatternSystem[N] =
    ConstructorPatternSystem(rawCases.toSeq.map((constructor, value) =>
      ConstructorPattern(constructor, value._1, value._2)
    ))
}
