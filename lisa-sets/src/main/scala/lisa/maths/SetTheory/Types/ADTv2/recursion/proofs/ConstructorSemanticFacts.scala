package lisa.maths.SetTheory.Types.ADTv2.recursion.proofs

import lisa.maths.SetTheory.Types.ADTv2.encoding.SemanticConstructor
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.{
  TypeSubstitution,
  instantiatedSemanticSignature,
  specializeFormula,
  specializeTerm
}
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.ProofTacticLib.Arity

object ConstructorSemanticFacts {

  final case class SpecializedConstructorFacts[N <: Arity](
      underlying: SemanticConstructor[N],
      typeSubstitutions: Seq[TypeSubstitution]
  ) {
    def name: String = underlying.name
    def variables2: Seq[Variable[Ind]] = underlying.variables2
    def selfRefVariables2: Seq[Variable[Ind]] = underlying.selfRefVariables2
    def semanticSignature2: Seq[(Variable[Ind], Expr[Ind])] =
      instantiatedSemanticSignature(underlying.semanticSignature2, typeSubstitutions)
    def heightTypingFormula(heightSet: Expr[Ind]): Expr[Prop] =
      specializeFormula(underlying.heightTypingFormula(heightSet), typeSubstitutions)
    def branchPremiseAtHeight(heightSet: Expr[Ind], term: Expr[Ind]): Expr[Prop] =
      specializeFormula(underlying.branchPremiseAtHeight(heightSet, term), typeSubstitutions)
    def branchAtHeight(heightSet: Expr[Ind], term: Expr[Ind]): Expr[Prop] =
      specializeFormula(underlying.branchAtHeight(heightSet, term), typeSubstitutions)
    def appliedTerm2: Expr[Ind] =
      specializeTerm(underlying.appliedTerm2, typeSubstitutions)
    def semanticTypingFromHeight(heightFun: Expr[Ind], n: Expr[Ind])(using sourcecode.Line, sourcecode.File): THM =
      underlying.semanticTypingFromHeightAt(typeSubstitutions)(heightFun, n)
    def appliedEqualityFromStructural(heightFun: Expr[Ind], n: Expr[Ind], term0: Expr[Ind])(using sourcecode.Line, sourcecode.File): THM =
      underlying.appliedEqualityFromStructuralAt(typeSubstitutions)(heightFun, n, term0)
  }

  def specializedConstructors[N <: Arity](
      constructors: Seq[SemanticConstructor[N]],
      typeSubstitutions: Seq[TypeSubstitution]
  ): Seq[SpecializedConstructorFacts[N]] =
    constructors.map(SpecializedConstructorFacts(_, typeSubstitutions))

  def constructorBranchAtHeight[N <: Arity](
      c: SpecializedConstructorFacts[N],
      heightSet: Expr[Ind],
      term: Expr[Ind]
  ): Expr[Prop] =
    c.branchAtHeight(heightSet, term)

  def constructorBranchesAtHeight[N <: Arity](
      constructors: Seq[SpecializedConstructorFacts[N]],
      heightSet: Expr[Ind],
      term: Expr[Ind]
  ): Map[SpecializedConstructorFacts[N], Expr[Prop]] =
    constructors.map(c => c -> constructorBranchAtHeight(c, heightSet, term)).toMap

  def constructorDisjunctionAtHeight[N <: Arity](
      constructors: Seq[SpecializedConstructorFacts[N]],
      heightSet: Expr[Ind],
      term: Expr[Ind]
  ): Expr[Prop] =
    seqOr(constructors.map(c => constructorBranchAtHeight(c, heightSet, term)))
}
