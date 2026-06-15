package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics

import lisa.maths.SetTheory.Functions.Pi.->:
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.encoding.SemanticConstructor
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.TypeSubstitution
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.instantiatedSemanticSignature
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.specializeTerm
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.maths.SetTheory.Types.TypingTheorems.arrowElim
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 * Constructor-headed patterns expose extra proof data coming from the semantic
 * constructor encoding.
 */
private[PatternMatching] trait ConstructorHeadPattern[N <: Arity] extends Pattern[N] {

  def semanticConstructor: SemanticConstructor[N]

  def typeSubstitutions: Seq[TypeSubstitution] = Seq.empty

  def specializedAdtTerm: Expr[Ind] = semanticConstructor.adt.term

  override def name: String = semanticConstructor.name

  override def arity: Int = semanticConstructor.arity

  def correspondsTo(candidate: SemanticConstructor[N]): Boolean =
    semanticConstructor == candidate

  override def matchesConstructorCase(constructor: SemanticConstructor[N], args: Seq[Expr[Ind]]): Boolean =
    semanticConstructor == constructor &&
      guardSignature == args.zipWithIndex.collect {
        case (t, i) if !t.isInstanceOf[Variable[Ind]] => (i, t)
      }.toSet

  def hasSameHeadAs(other: ConstructorHeadPattern[N]): Boolean =
    semanticConstructor == other.semanticConstructor

  override def inputTermAt(vars: Seq[Variable[Ind]]): Expr[Ind] =
    specializeTerm(semanticConstructor.appliedTerm(vars), typeSubstitutions)

  override def typingSignatureAt(vars: Seq[Variable[Ind]]): Seq[(Variable[Ind], Expr[Ind])] =
    instantiatedSemanticSignature(semanticConstructor.semanticSignature(vars), typeSubstitutions)

  override def variables2: Seq[Variable[Ind]] = semanticConstructor.variables2

  private def constructorApplicationTyping[N <: Arity](
      c: SemanticConstructor[N],
      args: Seq[Variable[Ind]]
  ): THM = Lemma(
    wellTypedFormula(c.semanticSignature(args)) |- (c.appliedTerm(args) :: c.adt.term)
  ) {
    have(c.term(c.typeVariablesSeq) :: c.typ) by Restate.from(c.intro)
    val introTyping = lastStep
    val argsWellTyped = assume(wellTypedFormula(c.semanticSignature(args)))

    val finalTyping = args
      .foldLeft(
        (introTyping, c.term(c.typeVariablesSeq): Expr[Ind], c.typ: Expr[Ind])
      ) { case ((accFact, accTerm, accType), argument) =>
        accType match
          case domainTy ->: codomainTy =>
            val argumentTyping = have(
              wellTypedFormula(c.semanticSignature(args)) |- argument :: domainTy
            ) by Tautology.from(argsWellTyped)
            val nextTyping = have(
              wellTypedFormula(c.semanticSignature(args)) |- (accTerm * argument) :: codomainTy
            ) by Tautology.from(
              accFact,
              arrowElim of (f := accTerm, a := domainTy, b := codomainTy, x := argument),
              argumentTyping
            )
            (nextTyping, accTerm * argument, codomainTy)
          case _ => throw UnreachableException
      }
      ._1

    have(thesis) by Restate.from(finalTyping)
  }

  override def inputTypingAt(vars: Seq[Variable[Ind]], adtTerm: Expr[Ind]): THM = {
    require(
      adtTerm == specializedAdtTerm,
      "ConstructorHeadPattern.inputTypingAt expects the compiled specialized ADT term."
    )
    val base = constructorApplicationTyping(semanticConstructor, vars)
    if typeSubstitutions.isEmpty then base
    else
      Lemma(base.statement.substitute(typeSubstitutions*)) {
        have(thesis) by Restate.from(base.of(typeSubstitutions*))
      }
  }

  def variables1: Seq[Variable[Ind]] = semanticConstructor.variables1

  def inputTerm1: Expr[Ind] = inputTermAt(variables1)

  def inputTerm2: Expr[Ind] = inputTermAt(variables2)

  def typingFormula1: Expr[Prop] = typingFormulaAt(variables1)

  def typingFormula2: Expr[Prop] = typingFormulaAt(variables2)

  def branchPremise1: Expr[Prop] = branchPremiseAt(variables1)

  def structuralTerm1: Expr[Ind] = specializeTerm(semanticConstructor.structuralTerm1, typeSubstitutions)

  def structuralTerm2: Expr[Ind] = specializeTerm(semanticConstructor.structuralTerm2, typeSubstitutions)

  def tagTerm1: Expr[Ind] = specializeTerm(semanticConstructor.underlying.tagTerm, typeSubstitutions)

  def tagTerm2: Expr[Ind] = specializeTerm(semanticConstructor.underlying.tagTerm, typeSubstitutions)

  def subterm1: Expr[Ind] = specializeTerm(semanticConstructor.underlying.subterm1, typeSubstitutions)

  def subterm2: Expr[Ind] = specializeTerm(semanticConstructor.underlying.subterm2, typeSubstitutions)

  def injectivity: THM = {
    val base = semanticConstructor.injectivity
    if typeSubstitutions.isEmpty then base
    else
      Lemma(base.statement.substitute(typeSubstitutions*)) {
        have(thesis) by Restate.from(base.of(typeSubstitutions*))
      }
  }

  def shortDefinition: THM = {
    val base = semanticConstructor.shortDefinition
    if typeSubstitutions.isEmpty then base
    else
      Lemma(base.statement.substitute(typeSubstitutions*)) {
        have(thesis) by Restate.from(base.of(typeSubstitutions*))
      }
  }
}

private[PatternMatching] object ConstructorHeadPattern {
  def require[N <: Arity](pattern: Pattern[N]): ConstructorHeadPattern[N] =
    pattern match
      case constructorHead: ConstructorHeadPattern[N] => constructorHead
      case _ =>
        throw new IllegalArgumentException(
          s"Pattern ${pattern.name} is not constructor-headed."
        )
}
