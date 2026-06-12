package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.induction

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.interface.Constructor
import lisa.maths.SetTheory.Types.ADTv2.interface.SpecializedADT
import lisa.utils.prooflib.ProofTacticLib.Arity

final case class InductionBranch[N <: Arity](
    constructor: Constructor[N],
    binders: Seq[Variable[Ind]],
    recursiveBinders: Seq[Variable[Ind]],
    typingAssumptions: Seq[Expr[Prop]],
    guardAssumptions: Seq[Expr[Prop]]
)

final case class InductionBranchSystem[N <: Arity](
    domain: SpecializedADT[N],
    branchesByConstructor: Map[Constructor[N], Seq[InductionBranch[N]]]
) {
  def constructors: Seq[Constructor[N]] =
    domain.base.constructors

  def branchesFor(constructor: Constructor[N]): Seq[InductionBranch[N]] =
    branchesByConstructor.getOrElse(constructor, Seq.empty)

  lazy val branches: Seq[InductionBranch[N]] =
    constructors.flatMap(branchesFor)

  def supportsSingleBranchPerConstructor: Boolean =
    constructors.forall(constructor => branchesFor(constructor).size == 1)
}

final case class InductionBranchWithPayload[N <: Arity, T](
    branch: InductionBranch[N],
    payload: T
)

final case class InductionBranchSystemWithPayload[N <: Arity, T](
    domain: SpecializedADT[N],
    branchesByConstructor: Map[Constructor[N], Seq[InductionBranchWithPayload[N, T]]]
) {
  def constructors: Seq[Constructor[N]] =
    domain.base.constructors

  def branchesFor(constructor: Constructor[N]): Seq[InductionBranchWithPayload[N, T]] =
    branchesByConstructor.getOrElse(constructor, Seq.empty)

  lazy val branches: Seq[InductionBranchWithPayload[N, T]] =
    constructors.flatMap(branchesFor)

  def supportsSingleBranchPerConstructor: Boolean =
    constructors.forall(constructor => branchesFor(constructor).size == 1)
}
