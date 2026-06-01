package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.Pair
import lisa.maths.SetTheory.Types.ADTv2.encoding.{SemanticADT, SemanticConstructor}
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.ConstructorTyping
import lisa.utils.fol.FOL.SubstPair
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 * Semantic template for one compiled branch of a pattern-matching definition.
 *
 * This trait only contains branch-level operations shared by every current
 * pattern family.
 */
trait Pattern[N <: Arity] {

  def binders: Seq[Variable[Ind]]

  def body: Expr[Ind]

  def semanticConstructor: SemanticConstructor[N]

  def name: String = semanticConstructor.name

  def correspondsTo(candidate: SemanticConstructor[N]): Boolean =
    semanticConstructor == candidate

  def hasSameHeadAs(other: Pattern[N]): Boolean =
    semanticConstructor == other.semanticConstructor

  def arity: Int = semanticConstructor.arity

  def inputTermAt(vars: Seq[Variable[Ind]]): Expr[Ind] =
    semanticConstructor.appliedTerm(vars)

  def inputTerm: Expr[Ind] = inputTermAt(binders)

  def typingSignatureAt(vars: Seq[Variable[Ind]]): Seq[(Variable[Ind], Expr[Ind])] =
    semanticConstructor.semanticSignature(vars)

  def typingPremisesAt(vars: Seq[Variable[Ind]]): Set[Expr[Prop]] =
    wellTypedSet(typingSignatureAt(vars))

  def typingFormulaAt(vars: Seq[Variable[Ind]]): Expr[Prop] =
    wellTypedFormula(typingSignatureAt(vars))

  def typingPremises: Set[Expr[Prop]] = typingPremisesAt(binders)

  def typingFormula: Expr[Prop] = typingFormulaAt(binders)

  def branchCondition: Expr[Prop] = ⊤

  def branchPremise: Expr[Prop] = simplify(typingFormula /\ branchCondition)

  def variables2: Seq[Variable[Ind]] = semanticConstructor.variables2

  def freshInputTerm: Expr[Ind] = inputTermAt(variables2)

  def freshTypingFormula: Expr[Prop] = typingFormulaAt(variables2)

  def branchConditionAt(vars: Seq[Variable[Ind]]): Expr[Prop] =
    branchCondition.substitute(binders.zip(vars).map((from, to) => from := to)*).asInstanceOf[Expr[Prop]]

  def freshBranchCondition: Expr[Prop] = branchConditionAt(variables2)

  def branchPremiseAt(vars: Seq[Variable[Ind]]): Expr[Prop] =
    simplify(typingFormulaAt(vars) /\ branchConditionAt(vars))

  def freshBranchPremise: Expr[Prop] = simplify(freshTypingFormula /\ freshBranchCondition)

  def bodySubstituted(subst: Seq[(Variable[Ind], Expr[Ind])]): Expr[Ind] =
    body.substitute(subst.map((from, to) => from := to)*).asInstanceOf[Expr[Ind]]

  def bodyAt(vars: Seq[Variable[Ind]]): Expr[Ind] =
    bodySubstituted(binders.zip(vars))

  def bodyAtFreshVars2: Expr[Ind] = bodyAt(variables2)

  def inputTypingAt(vars: Seq[Variable[Ind]], adtTerm: Expr[Ind]): THM = {
    require(adtTerm == semanticConstructor.adt.term, "Pattern.inputTypingAt currently expects the owning ADT term.")
    ConstructorTyping.constructorApplicationTyping(semanticConstructor, vars)
  }

  def withBody(newBody: Expr[Ind]): Pattern[N]
}

/**
 * Generic semantic template for a compiled pattern-matching family.
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

  def coverage(domain: SemanticADT[N]): THM

  def branchSelectionFor(constructor: SemanticConstructor[N], term: Expr[Ind]): THM

  def incompatible(pattern1: Pattern[N], pattern2: Pattern[N]): THM
}

final case class SpecializedPattern[N <: Arity](
    underlying: Pattern[N],
    typeSubstitutions: Seq[SubstPair { type S = Ind }],
    specializedAdtTerm: Expr[Ind]
) extends Pattern[N] {
  override def semanticConstructor: SemanticConstructor[N] = underlying.semanticConstructor

  private def specializeTerm(term: Expr[Ind]): Expr[Ind] =
    term.substitute(typeSubstitutions*)

  private def specializeProp(formula: Expr[Prop]): Expr[Prop] =
    formula.substitute(typeSubstitutions*)

  override lazy val binders: Seq[Variable[Ind]] = underlying.binders
  override lazy val body: Expr[Ind] = specializeTerm(underlying.body)
  override lazy val branchCondition: Expr[Prop] = specializeProp(underlying.branchCondition)
  override lazy val typingPremises: Set[Expr[Prop]] =
    underlying.typingPremises.map(specializeProp)
  override lazy val typingFormula: Expr[Prop] =
    specializeProp(underlying.typingFormula)

  override def inputTermAt(vars: Seq[Variable[Ind]]): Expr[Ind] =
    specializeTerm(underlying.inputTermAt(vars))

  override def typingSignatureAt(vars: Seq[Variable[Ind]]): Seq[(Variable[Ind], Expr[Ind])] =
    underlying.typingSignatureAt(vars).map((variable, typ) => variable -> specializeTerm(typ))

  override def inputTypingAt(vars: Seq[Variable[Ind]], adtTerm: Expr[Ind]): THM = {
    require(
      adtTerm == specializedAdtTerm,
      "SpecializedPattern.inputTypingAt expects the specialized ADT term."
    )
    val base = ConstructorTyping.constructorApplicationTyping(semanticConstructor, vars)
    Lemma(base.statement.substitute(typeSubstitutions*)) {
      have(thesis) by Restate.from(base.of(typeSubstitutions*))
    }
  }

  override def withBody(newBody: Expr[Ind]): Pattern[N] =
    copy(underlying = underlying.withBody(newBody), specializedAdtTerm = specializedAdtTerm)
}

final case class SpecializedPatternSystem[N <: Arity](
    underlying: PatternSystem[N],
    domain: SemanticADT[N],
    typeSubstitutions: Seq[SubstPair { type S = Ind }],
    specializedAdtTerm: Expr[Ind]
) extends PatternSystem[N] {
  private lazy val specializedPatternsByUnderlying: Map[Pattern[N], Pattern[N]] =
    underlying.patterns.map(pattern =>
      pattern -> SpecializedPattern(pattern, typeSubstitutions, specializedAdtTerm)
    ).toMap

  override lazy val patterns: Seq[Pattern[N]] =
    underlying.patterns.map(specializedPatternsByUnderlying)

  override def supportsAutomaticCoverage: Boolean =
    underlying.supportsAutomaticCoverage

  override def coverage(domain: SemanticADT[N]): THM = {
    val base = underlying.coverage(domain)
    Lemma(base.statement.substitute(typeSubstitutions*)) {
      have(thesis) by Restate.from(base.of(typeSubstitutions*))
    }
  }

  override def branchSelectionFor(constructor: SemanticConstructor[N], term: Expr[Ind]): THM = {
    val base = underlying.branchSelectionFor(constructor, term)
    Lemma(base.statement.substitute(typeSubstitutions*)) {
      have(thesis) by Restate.from(base.of(typeSubstitutions*))
    }
  }

  override def incompatible(pattern1: Pattern[N], pattern2: Pattern[N]): THM = {
    val underlyingPattern1 = specializedPatternsByUnderlying.collectFirst {
      case (raw, specialized) if specialized == pattern1 => raw
    }.getOrElse(
      throw new IllegalArgumentException(s"Unknown specialized pattern ${pattern1.name}.")
    )
    val underlyingPattern2 = specializedPatternsByUnderlying.collectFirst {
      case (raw, specialized) if specialized == pattern2 => raw
    }.getOrElse(
      throw new IllegalArgumentException(s"Unknown specialized pattern ${pattern2.name}.")
    )
    val base = underlying.incompatible(underlyingPattern1, underlyingPattern2)
    Lemma(base.statement.substitute(typeSubstitutions*)) {
      have(thesis) by Restate.from(base.of(typeSubstitutions*))
    }
  }
}

object SpecializedPatternSystem {
  def apply[N <: Arity](
      underlying: PatternSystem[N],
      domain: SemanticADT[N],
      typeSubstitutions: Seq[SubstPair { type S = Ind }],
      specializedAdtTerm: Expr[Ind]
  ): PatternSystem[N] =
    if typeSubstitutions.isEmpty then underlying
    else
      new SpecializedPatternSystem(
        underlying = underlying,
        domain = domain,
        typeSubstitutions = typeSubstitutions,
        specializedAdtTerm = specializedAdtTerm
      )
}
