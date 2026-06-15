package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.induction

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.ConstructorHeadPattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.interface.Constructor
import lisa.maths.SetTheory.Types.ADTv2.interface.SpecializedADT
import lisa.maths.SetTheory.Types.ADTv2.support.Time
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.simplify
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.SelfRef
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.utils.prooflib.ProofTacticLib.Arity

object PatternToInduction {

  def compile[N <: Arity](
      domain: SpecializedADT[N],
      system: PatternSystem[N]
  ): Either[String, InductionBranchSystem[N]] =
    Time.measure("PatternSystem -> InductionBranchSystem") {
      for
        patternBranches <- compileBranches(domain, system)
        _ <- ensureCoverage(domain, patternBranches)
      yield InductionBranchSystem(
        domain = domain,
        branchesByConstructor = patternBranches.groupBy(_.constructor).withDefaultValue(Seq.empty)
      )
    }

  def compileWithPayload[N <: Arity, T](
      domain: SpecializedADT[N],
      system: PatternSystem[N],
      payloads: Seq[T]
  ): Either[String, InductionBranchSystemWithPayload[N, T]] =
    Time.measure("PatternSystem -> InductionBranchSystemWithPayload") {
      for
        branches <- compileBranches(domain, system)
        _ <- ensureCoverage(domain, branches)
        _ <-
          if branches.size == payloads.size then Right(())
          else
            Left(
              s"Induction payload attachment mismatch: ${branches.size} compiled branches for ${payloads.size} payload(s)."
            )
      yield InductionBranchSystemWithPayload(
        domain = domain,
        branchesByConstructor =
          branches.zip(payloads).map((branch, payload) => branch.constructor -> InductionBranchWithPayload(branch, payload)).groupBy(_._1).view.mapValues(_.map(_._2)).toMap.withDefaultValue(Seq.empty)
      )
    }

  private def compileBranches[N <: Arity](
      domain: SpecializedADT[N],
      system: PatternSystem[N]
  ): Either[String, Seq[InductionBranch[N]]] =
    system.patterns.foldLeft[Either[String, Seq[InductionBranch[N]]]](Right(Seq.empty)) {
      case (Left(err), _) => Left(err)
      case (Right(acc), pattern) =>
        compileBranch(domain, pattern).map(acc :+ _)
    }

  private def compileBranch[N <: Arity](
      domain: SpecializedADT[N],
      pattern: lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern[N]
  ): Either[String, InductionBranch[N]] =
    pattern match
      case constructorPattern: ConstructorHeadPattern[N] =>
        if constructorPattern.specializedAdtTerm != domain.term then
          Left(
            s"Pattern ${constructorPattern.name} was compiled for ${constructorPattern.specializedAdtTerm}, expected ${domain.term}."
          )
        else
          constructorFor(domain, constructorPattern).map(constructor =>
            InductionBranch(
              constructor = constructor,
              binders = constructorPattern.binders,
              recursiveBinders = recursiveBindersFor(constructorPattern),
              typingAssumptions = constructorPattern
                .typingSignatureAt(constructorPattern.binders)
                .map { case (variable, typ) => variable :: typ },
              guardAssumptions = guardAssumptionsFor(constructorPattern)
            )
          )
      case _ =>
        Left(s"Pattern ${pattern.name} is not constructor-headed and cannot drive induction.")

  private def constructorFor[N <: Arity](
      domain: SpecializedADT[N],
      pattern: ConstructorHeadPattern[N]
  ): Either[String, Constructor[N]] =
    domain.base.constructors.find(_.semantic == pattern.semanticConstructor) match
      case Some(constructor) => Right(constructor)
      case None =>
        Left(
          s"Constructor ${pattern.semanticConstructor.name} does not belong to specialized ADT ${domain.name}."
        )

  private def recursiveBindersFor[N <: Arity](
      pattern: ConstructorHeadPattern[N]
  ): Seq[Variable[Ind]] =
    pattern.semanticConstructor.underlying.specification.zip(pattern.binders).collect { case (SelfRef, binder) =>
      binder
    }

  private def guardAssumptionsFor[N <: Arity](
      pattern: ConstructorHeadPattern[N]
  ): Seq[Expr[Prop]] =
    val normalized = simplify(pattern.branchCondition)
    if normalized == (True: Expr[Prop]) then Seq.empty else Seq(normalized)

  private def ensureCoverage[N <: Arity](
      domain: SpecializedADT[N],
      branches: Seq[InductionBranch[N]]
  ): Either[String, Unit] =
    val covered = branches.map(_.constructor).toSet
    val missing = domain.base.constructors.filterNot(covered.contains)
    missing.headOption match
      case Some(constructor) =>
        Left(s"Induction pattern system is missing constructor ${constructor.name}.")
      case None => Right(())
}
