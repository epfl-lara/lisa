package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.ADTv2.encoding.SemanticConstructor
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.ConstructorTyping
import lisa.utils.fol.FOL.SubstPair
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 * Constructor-headed patterns expose extra proof data coming from the semantic
 * constructor encoding.
 */
trait ConstructorHeadPattern[N <: Arity] extends Pattern[N] {

  def semanticConstructor: SemanticConstructor[N]

  override def name: String = semanticConstructor.name

  override def arity: Int = semanticConstructor.arity

  def correspondsTo(candidate: SemanticConstructor[N]): Boolean =
    semanticConstructor == candidate

  def hasSameHeadAs(other: ConstructorHeadPattern[N]): Boolean =
    semanticConstructor == other.semanticConstructor

  override def inputTermAt(vars: Seq[Variable[Ind]]): Expr[Ind] =
    semanticConstructor.appliedTerm(vars)

  override def typingSignatureAt(vars: Seq[Variable[Ind]]): Seq[(Variable[Ind], Expr[Ind])] =
    semanticConstructor.semanticSignature(vars)

  override def variables2: Seq[Variable[Ind]] = semanticConstructor.variables2

  override def inputTypingAt(vars: Seq[Variable[Ind]], adtTerm: Expr[Ind]): THM = {
    require(
      adtTerm == semanticConstructor.adt.term,
      "ConstructorHeadPattern.inputTypingAt expects the owning ADT term."
    )
    ConstructorTyping.constructorApplicationTyping(semanticConstructor, vars)
  }

  def variables1: Seq[Variable[Ind]] = semanticConstructor.variables1

  def inputTerm1: Expr[Ind] = inputTermAt(variables1)

  def inputTerm2: Expr[Ind] = inputTermAt(variables2)

  def typingFormula1: Expr[Prop] = typingFormulaAt(variables1)

  def typingFormula2: Expr[Prop] = typingFormulaAt(variables2)

  def branchPremise1: Expr[Prop] = branchPremiseAt(variables1)

  def structuralTerm1: Expr[Ind] = semanticConstructor.structuralTerm1

  def structuralTerm2: Expr[Ind] = semanticConstructor.structuralTerm2

  def tagTerm1: Expr[Ind] = semanticConstructor.underlying.tagTerm

  def tagTerm2: Expr[Ind] = semanticConstructor.underlying.tagTerm

  def subterm1: Expr[Ind] = semanticConstructor.underlying.subterm1

  def subterm2: Expr[Ind] = semanticConstructor.underlying.subterm2

  def injectivity: THM = semanticConstructor.injectivity

  def shortDefinition: THM = semanticConstructor.shortDefinition
}

object ConstructorHeadPattern {
  private final case class SpecializedConstructorHeadPattern[N <: Arity](
      specialized: SpecializedPattern[N],
      underlyingHead: ConstructorHeadPattern[N],
      typeSubstitutions: Seq[SubstPair { type S = Ind }],
      specializedAdtTerm: Expr[Ind]
  ) extends ConstructorHeadPattern[N] {
    private def specializeTerm(term: Expr[Ind]): Expr[Ind] =
      term.substitute(typeSubstitutions*)

    override def semanticConstructor: SemanticConstructor[N] =
      underlyingHead.semanticConstructor

    override def binders: Seq[Variable[Ind]] =
      specialized.binders

    override def body: Expr[Ind] =
      specialized.body

    override def branchCondition: Expr[Prop] =
      specialized.branchCondition

    override def inputTermAt(vars: Seq[Variable[Ind]]): Expr[Ind] =
      specialized.inputTermAt(vars)

    override def typingSignatureAt(vars: Seq[Variable[Ind]]): Seq[(Variable[Ind], Expr[Ind])] =
      specialized.typingSignatureAt(vars)

    override def variables2: Seq[Variable[Ind]] =
      specialized.variables2

    override def inputTypingAt(vars: Seq[Variable[Ind]], adtTerm: Expr[Ind]): THM =
      specialized.inputTypingAt(vars, adtTerm)

    override def withBody(newBody: Expr[Ind]): Pattern[N] =
      require(specialized.withBody(newBody))

    override def structuralTerm1: Expr[Ind] =
      specializeTerm(underlyingHead.structuralTerm1)

    override def structuralTerm2: Expr[Ind] =
      specializeTerm(underlyingHead.structuralTerm2)

    override def tagTerm1: Expr[Ind] =
      specializeTerm(underlyingHead.tagTerm1)

    override def tagTerm2: Expr[Ind] =
      specializeTerm(underlyingHead.tagTerm2)

    override def subterm1: Expr[Ind] =
      specializeTerm(underlyingHead.subterm1)

    override def subterm2: Expr[Ind] =
      specializeTerm(underlyingHead.subterm2)

    override def injectivity: THM = {
      val base = underlyingHead.injectivity
      Lemma(base.statement.substitute(typeSubstitutions*)) {
        have(thesis) by Restate.from(base.of(typeSubstitutions*))
      }
    }

    override def shortDefinition: THM = {
      val base = underlyingHead.shortDefinition
      Lemma(base.statement.substitute(typeSubstitutions*)) {
        have(thesis) by Restate.from(base.of(typeSubstitutions*))
      }
    }
  }

  def require[N <: Arity](pattern: Pattern[N]): ConstructorHeadPattern[N] =
    pattern match
      case constructorHead: ConstructorHeadPattern[N] => constructorHead
      case specialized: SpecializedPattern[N] =>
        SpecializedConstructorHeadPattern(
          specialized = specialized,
          underlyingHead = require(specialized.underlying),
          typeSubstitutions = specialized.typeSubstitutions,
          specializedAdtTerm = specialized.specializedAdtTerm
        )
      case _ =>
        throw new IllegalArgumentException(
          s"Pattern ${pattern.name} is not constructor-headed."
        )
}
