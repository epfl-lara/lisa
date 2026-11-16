package lisa.maths.SetTheory.Types.ADTv2.recursion.proofs

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.encoding.SemanticConstructor
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.TypeSubstitution
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.instantiatedSemanticSignature
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.specializeTerm
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._

private[recursion] object ConstructorSemanticFacts {

  final case class SpecializedConstructorFacts(
      underlying: SemanticConstructor,
      typeSubstitutions: Seq[TypeSubstitution]
  ) {
    private val heightArgument = Variable[Ind](freshId(underlying.typeVariablesSeq ++ underlying.variables2, s"${underlying.fullName}/heightArgument"))
    private val termArgument = Variable[Ind](freshId(underlying.typeVariablesSeq ++ underlying.variables2 :+ heightArgument, s"${underlying.fullName}/termArgument"))

    def name: String = underlying.name
    def variables2: Seq[Variable[Ind]] = underlying.variables2
    def selfRefVariables2: Seq[Variable[Ind]] = underlying.selfRefVariables2
    def semanticSignature2: Seq[(Variable[Ind], Expr[Ind])] =
      instantiatedSemanticSignature(underlying.semanticSignature2, typeSubstitutions)
    def heightTypingFormula(heightSet: Expr[Ind]): Expr[Prop] =
      underlying.heightTypingFormula(heightArgument).substitute((typeSubstitutions :+ (heightArgument := heightSet))*)
    def branchPremiseAtHeight(heightSet: Expr[Ind], term: Expr[Ind]): Expr[Prop] =
      underlying.branchPremiseAtHeight(heightArgument, termArgument).substitute((typeSubstitutions ++ Seq(heightArgument := heightSet, termArgument := term))*)
    def branchAtHeight(heightSet: Expr[Ind], term: Expr[Ind]): Expr[Prop] =
      existsSeq(variables2, branchPremiseAtHeight(heightSet, term))
    def appliedTerm2: Expr[Ind] =
      specializeTerm(underlying.appliedTerm2, typeSubstitutions)
    def semanticTypingFromHeight(heightFun: Expr[Ind], n: Expr[Ind])(using sourcecode.Line, sourcecode.File): THM =
      underlying.semanticTypingFromHeightAt(typeSubstitutions)(heightFun, n)
    def appliedEqualityFromStructural(heightFun: Expr[Ind], n: Expr[Ind], term0: Expr[Ind])(using sourcecode.Line, sourcecode.File): THM =
      underlying.appliedEqualityFromStructuralAt(typeSubstitutions)(heightFun, n, term0)
  }

  def specializedConstructors(
      constructors: Seq[SemanticConstructor],
      typeSubstitutions: Seq[TypeSubstitution]
  ): Seq[SpecializedConstructorFacts] =
    constructors.map(SpecializedConstructorFacts(_, typeSubstitutions))

  def constructorBranchAtHeight(
      c: SpecializedConstructorFacts,
      heightSet: Expr[Ind],
      term: Expr[Ind]
  ): Expr[Prop] =
    c.branchAtHeight(heightSet, term)

  def constructorDisjunctionAtHeight(
      constructors: Seq[SpecializedConstructorFacts],
      heightSet: Expr[Ind],
      term: Expr[Ind]
  ): Expr[Prop] =
    seqOr(constructors.map(c => constructorBranchAtHeight(c, heightSet, term)))
}
