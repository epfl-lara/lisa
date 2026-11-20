package lisa.maths.SetTheory.Types.ADT.recursion.proofs

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADT.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADT.encoding.SemanticConstructor
import lisa.maths.SetTheory.Types.ADT.support.InterfaceHelpers.TypeSubstitution
import lisa.maths.SetTheory.Types.ADT.support.InterfaceHelpers.instantiatedSemanticSignature
import lisa.maths.SetTheory.Types.ADT.support.core.Utils._
import lisa.utils.prooflib.Thm

private[recursion] object ConstructorSemanticFacts {

  final case class SpecializedConstructorFacts(
      underlying: SemanticConstructor,
      typeSubstitutions: Seq[TypeSubstitution],
      variables2: Seq[Variable[Ind]]
  ) {
    private val heightArgument = Variable[Ind](freshId(underlying.typeVariablesSeq ++ underlying.variables2, s"${underlying.fullName}/heightArgument"))
    private val termArgument = Variable[Ind](freshId(underlying.typeVariablesSeq ++ underlying.variables2 :+ heightArgument, s"${underlying.fullName}/termArgument"))
    private val substitutions = typeSubstitutions ++ underlying.variables2.zip(variables2).map((from, to) => from := to)

    def name: String = underlying.name
    def selfRefVariables2: Seq[Variable[Ind]] = underlying.recursiveBinders(variables2)
    def semanticSignature2: Seq[(Variable[Ind], Expr[Ind])] =
      instantiatedSemanticSignature(underlying.semanticSignature(variables2), typeSubstitutions)
    def heightTypingFormula(heightSet: Expr[Ind]): Expr[Prop] =
      underlying.heightTypingFormula(heightArgument).substitute((substitutions :+ (heightArgument := heightSet))*)
    def branchPremiseAtHeight(heightSet: Expr[Ind], term: Expr[Ind]): Expr[Prop] =
      underlying.branchPremiseAtHeight(heightArgument, termArgument).substitute((substitutions ++ Seq(heightArgument := heightSet, termArgument := term))*)
    def branchAtHeight(heightSet: Expr[Ind], term: Expr[Ind]): Expr[Prop] =
      existsSeq(variables2, branchPremiseAtHeight(heightSet, term))
    def appliedTerm2: Expr[Ind] =
      underlying.appliedTerm2.substitute(substitutions*)
    def semanticTypingFromHeight(heightFun: Expr[Ind], n: Expr[Ind])(using proof: lisa.SetTheoryLibrary.ProofBuilder): Thm =
      underlying.semanticTypingFromHeightAt(typeSubstitutions, variables2)(heightFun, n)
    def appliedEqualityFromStructural(heightFun: Expr[Ind], n: Expr[Ind], term0: Expr[Ind])(using proof: lisa.SetTheoryLibrary.ProofBuilder): Thm =
      underlying.appliedEqualityFromStructuralAt(typeSubstitutions, variables2)(heightFun, n, term0)
  }

  def specializedConstructors(
      patterns: PatternSystem[?],
      typeSubstitutions: Seq[TypeSubstitution]
  ): Seq[SpecializedConstructorFacts] =
    patterns.constructors.map { constructor =>
      SpecializedConstructorFacts(constructor, typeSubstitutions, patterns.clausesFor(constructor).head.variables2.take(constructor.arity))
    }

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
