package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.induction

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.ConstructorHeadPattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.interface.Constructor
import lisa.maths.SetTheory.Types.ADTv2.interface.SpecializedADT
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.simplify
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.utils.prooflib.ProofTacticLib.Arity

final case class InductionBranch[N <: Arity, T](
    constructor: Constructor[N],
    binders: Seq[Variable[Ind]],
    recursiveBinders: Seq[Variable[Ind]],
    typingAssumptions: Seq[Expr[Prop]],
    guardAssumptions: Seq[Expr[Prop]],
    payload: T
){

  def map[U](f: T => U): InductionBranch[N, U] = 
    InductionBranch(constructor, binders, recursiveBinders, typingAssumptions, guardAssumptions, f(payload))

}

final case class InductionBranchSystem[N <: Arity, T](
    domain: SpecializedADT[N],
    system: PatternSystem[N],
    branchesByConstructor: Map[Constructor[N], Seq[InductionBranch[N, T]]]
) {

  def branchesFor(constructor: Constructor[N]): Seq[InductionBranch[N, T]] =
    branchesByConstructor.getOrElse(constructor, Seq.empty)

  val branches: Seq[InductionBranch[N, T]] =
    domain.base.constructors.flatMap(branchesFor)

}

object PatternToInduction {

  private def ensureCoverage[N <: Arity, T](
    domain: SpecializedADT[N], 
    branches: Seq[InductionBranch[N, T]]
  ): Either[String, Seq[InductionBranch[N, T]]] =
    val covered = branches.map(_.constructor).toSet
    val missing = domain.base.constructors.filterNot(covered.contains)
    missing.headOption match
      case Some(constructor) =>
        Left(s"Induction pattern system is missing constructor ${constructor.name}.")
      case None => Right(branches)

  def compile[N <: Arity, T](
      domain: SpecializedADT[N],
      system: PatternSystem[N],
      payloads: Seq[T]
  ): Either[String, InductionBranchSystem[N, T]] =
    {

      if system.patterns.size != payloads.size then
        Left(
          s"Induction payload attachment mismatch: ${system.patterns.size} compiled branches for ${payloads.size} payloads."
        )
      else

        val compiledBranches: Either[String, Seq[InductionBranch[N, T]]] =
          system.patterns.zip(payloads).map { 
            case (pattern, payload) => compileBranch(domain, pattern, payload) 
          }.foldLeft[Either[String, Seq[InductionBranch[N, T]]]](Right(Seq.empty)) {
            case (Left(err), _) => Left(err)
            case (Right(acc), branch) => branch.map(acc :+ _)
          } match
            case Left(err) => Left(err)
            case Right(branches) => ensureCoverage(domain, branches)

        compiledBranches match
          case Left(err) => Left(err)
          case Right(compiledBranches) =>
            Right( InductionBranchSystem(
              domain = domain,
              system = system,
              branchesByConstructor =
                compiledBranches.map(
                  branch => branch.constructor -> branch
                ).groupBy(_._1).view.mapValues(_.map(_._2)).toMap.withDefaultValue(Seq.empty)
            ))
    }

  private def compileBranch[N <: Arity, T](
      domain: SpecializedADT[N],
      pattern: Pattern[N],
      payload: T
  ): Either[String, InductionBranch[N, T]] =
    pattern match
      case constructorPattern: ConstructorHeadPattern[N] =>
        if constructorPattern.specializedAdtTerm != domain.term then
          Left(
            s"Pattern ${constructorPattern.name} was compiled for ${constructorPattern.specializedAdtTerm}, expected ${domain.term}."
          )
        else
          val constructorOpt: Either[String, Constructor[N]] = 
            domain.base.constructors.find(_.semantic == constructorPattern.semanticConstructor) match
              case Some(constructor) => Right(constructor)
              case None =>
                Left(
                  s"Constructor ${constructorPattern.semanticConstructor.name} does not belong to specialized ADT ${domain.name}."
                )

          constructorOpt.map(constructor =>

            val normalized = simplify(constructorPattern.branchCondition)
            val guardAssumptions = if normalized == (True: Expr[Prop]) then Seq.empty else Seq(normalized)
            InductionBranch(
              constructor = constructor,
              binders = constructorPattern.binders,
              recursiveBinders = constructorPattern.semanticConstructor.recursiveBinders(constructorPattern.binders),
              typingAssumptions = constructorPattern
                .typingSignatureAt(constructorPattern.binders)
                .map { case (variable, typ) => variable :: typ },
              guardAssumptions = guardAssumptions,
              payload = payload
            )
          )
      case _ =>
        Left(s"Pattern ${pattern.name} is not constructor-headed and cannot drive induction.")

}
