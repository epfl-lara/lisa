package lisa.utils.prooflib

import lisa.kernel.fol.{FOL => KF}
import lisa.kernel.{proof => K}
import lisa.utils.collection.Extensions.{_, given}
import lisa.utils.fol.FOL._
import lisa.utils.prooflib.Helpers._
import lisa.utils.prooflib.ProofCarrier.Failure
import lisa.utils.prooflib.ProofHelpers._

object BasicStep:

  ///////////////////////////////////////////////////////////////////////////////
  // Error reporting helpers
  ///////////////////////////////////////////////////////////////////////////////

  case class FrontKernelMismatch(reason: String) extends Exception:
    def msg = s"[FATAL] Front-end and kernel mismatch: $reason"

  case object UnreachableErrorException extends Exception:
    def msg = "[FATAL] This error path should be unreachable."

  private def theoryMismatch(step: String, expected: K.Theory, actual: K.Theory): Failure =
    Failure(withParams(s"$step: premises and conclusion had mismatched underlying theories.", "Expected" -> expected, "Actual" -> actual))

  private def liftGeneralError(step: String, err: K.GeneralError): Failure =
    err match
      case e: K.TheoryMismatch => theoryMismatch(step, e.expected, e.actual)
      case e: K.SortMismatch =>
        Failure(
          withParams(s"$step: an expression has the wrong sort.", "Expected" -> e.expected, "Actual" -> e.actual, "Expression" -> e.expression)
        )

  private def inferenceFailure(message: String, conclusion: Sequent, params: (String, Any)*): ProofJudgement =
    Failure(withParams(message, ("Conclusion", conclusion) +: params*))

  ///////////////////////////////////////////////////////////////////////////////
  // Proof construction helpers
  ///////////////////////////////////////////////////////////////////////////////

  private def successful(thm: K.Thm, conclusion: Sequent)(using Library): ProofJudgement =
    ProofJudgement(Thm(conclusion, thm))

  /**
   * Weakening helper. Does not handle errors like [[Weakening.apply]].
   * Intended to be used inside tactics for quickly unfolding a kernel
   * weakening step.
   */
  private inline def weakening(conclusion: K.Sequent, premise: K.Thm)(using library: Library): Option[K.Thm] =
    K.Weakening(using library.theory)(conclusion, premise).toOption

  ///////////////////////////////////////////////////////////////////////////////
  // Basic Step Definitions
  //
  // Each step defines an apply function to be used in proof scripts, ideally
  // performing parameter inference for convenience. In the case it is inferring
  // some parameters, the actual kernel call should be delegated to a version of
  // the step with explicit parameters, called `withParameters` by convention.
  //
  // Basic steps should largely just be wrappers around kernel calls with some
  // parameter inference.
  ///////////////////////////////////////////////////////////////////////////////

  object Sorry extends SequentTactic:
    def apply(using sourcecode.File, sourcecode.Line)(using library: Library)(conclusion: Sequent): ProofJudgement =
      val underlying = conclusion.underlying
      K.Sorry(using library.theory)(underlying)
        .lift(conclusion)

  object Axiom extends SequentTactic:
    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(statement: Sequent): ProofJudgement =
      library
        .Axiom(file, line)(statement)
        .lift(statement)

  object Hypothesis extends SequentTactic:
    private def liftError(conclusion: Sequent, pivot: Expr[Prop])(err: K.Hypothesis.ErrorType): Failure =
      err match
        // step-specific errors
        case _: K.Hypothesis.MissingFromLeft =>
          assert(!conclusion.left.containsEq(pivot), s"Pivot $pivot is in the left side of the conclusion $conclusion, despite the kernel reporting it as missing.")
          val base = s"Hypothesis pivot is missing from the left side of the conclusion"
          Failure(withParams(base, "Pivot" -> pivot, "Conclusion" -> conclusion))
        case _: K.Hypothesis.MissingFromRight =>
          assert(!conclusion.right.containsEq(pivot), s"Pivot $pivot is in the right side of the conclusion $conclusion, despite the kernel reporting it as missing.")
          val base = s"Hypothesis pivot is missing from the right side of the conclusion"
          Failure(withParams(base, "Pivot" -> pivot, "Conclusion" -> conclusion))
        // general errors
        case _: K.SortMismatch =>
          // should only happen if the pivot is not a prop, which is ensured by
          // the front type system
          throw FrontKernelMismatch("Expr[Prop] pivot is not a kernel Prop")
        case _: K.TheoryMismatch =>
          // Hyp has no premises
          throw UnreachableErrorException

    def withParameters(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(pivot: Expr[Prop])(conclusion: Sequent): ProofJudgement =
      K.Hypothesis(using library.theory)(conclusion.underlying, pivot.underlying)
        .mapLeft(liftError(conclusion, pivot))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent): ProofJudgement =
      val pivot =
        // default to syntactic match
        conclusion.left
          .find(conclusion.right.contains)
          .orElse:
            // try falling back to weaker eq match
            conclusion.left.find(phi => conclusion.right.containsEq(phi))

      pivot match
        case Some(phi) => withParameters(using file, line)(phi)(conclusion)
        case None =>
          Failure(
            withParams(
              "Could not infer a Hypothesis pivot occurring on both sides of the conclusion.",
              "Conclusion" -> conclusion
            )
          )

  object Restate extends SequentTactic, PremiseSequentTactic:
    private def liftError(conclusion: Sequent, premise: K.Thm)(err: K.Restate.ErrorType): Failure =
      err match
        case _: K.Restate.NotImplying =>
          Failure(
            withParams("Restate premise is not OL-equivalent to the conclusion.", "Premise" -> Thm.liftSequent(premise.statement), "Conclusion" -> conclusion)
          )
        case e: K.GeneralError => liftGeneralError("Restate", e)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
      K.Restate(using library.theory)(conclusion.underlying, premise)
        .mapLeft(liftError(conclusion, premise))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent): ProofJudgement =
      RestateTrue(using file, line)(using library)(conclusion)

    def from(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(premise: K.Thm)(conclusion: Sequent): ProofJudgement =
      apply(using file, line)(using library)(conclusion, premise)

  object RestateTrue extends SequentTactic:
    private def liftError(conclusion: Sequent)(err: K.RestateTrue.ErrorType): Failure =
      err match
        case _: K.RestateTrue.NotTrivial =>
          Failure(withParams("RestateTrue conclusion is not OL-equivalent to truth.", "Conclusion" -> conclusion))

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent): ProofJudgement =
      K.RestateTrue(using library.theory)(conclusion.underlying)
        .mapLeft(liftError(conclusion))
        .lift(conclusion)

  object Cut:
    private def prove(conclusion: K.Sequent, prem1: K.Thm, prem2: K.Thm, phi: KF.Expression)(using library: Library): K.Cut.Result[K.Thm] =
      K.Cut(using library.theory)(conclusion, prem1, prem2, phi)

    private def liftError(conclusion: Sequent, prem1: K.Thm, prem2: K.Thm, phi: Expr[Prop])(
        err: K.Cut.ErrorType
    ): Failure =
      err match
        case _: K.Cut.MissingFromFirst =>
          Failure(withParams("Cut: LHS of first premise is not contained in the conclusion.", "Premise" -> prem1, "Conclusion" -> conclusion))
        case _: K.Cut.MissingFromSecond =>
          Failure(withParams("Cut: RHS of second premise is not contained in the conclusion.", "Premise" -> prem2, "Conclusion" -> conclusion))
        case _: K.Cut.ExtraneousInFirst =>
          Failure(
            withParams(
              "Cut: RHS of first premise contains a formula other than the pivot that is absent from the conclusion.",
              "Pivot" -> phi,
              "First premise" -> prem1.statement,
              "Conclusion" -> conclusion
            )
          )
        case _: K.Cut.ExtraneousInSecond =>
          Failure(
            withParams(
              "Cut: LHS of second premise contains a formula other than the pivot that is absent from the conclusion.",
              "Pivot" -> phi,
              "Second premise" -> prem2.statement,
              "Conclusion" -> conclusion
            )
          )
        case e: K.GeneralError => liftGeneralError("Cut", e)

    def withParameters(using
        file: sourcecode.File,
        line: sourcecode.Line
    )(using
        library: Library
    )(phi: Expr[Prop])(
        prem1: K.Thm,
        prem2: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, prem1, prem2, phi.underlying)
        .mapLeft(liftError(conclusion, prem1, prem2, phi))
        .lift(conclusion)

    def apply(using
        file: sourcecode.File,
        line: sourcecode.Line
    )(using
        library: Library
    )(prem1: K.Thm, prem2: K.Thm)(
        conclusion: Sequent
    ): ProofJudgement =
      val underlying = conclusion.underlying
      val missing = (differenceEq(prem1.right, underlying.right) ++ differenceEq(prem2.left, underlying.left)).nextOption()
      val inferred =
        missing match
          case Some(phi) => prove(underlying, prem1, prem2, phi).toOption
          case None =>
            prem1.right.iterator
              .filter(phi => prem2.left.contains(phi) || KF.contains(prem2.left, phi))
              .nextOption()
              .flatMap(phi => prove(underlying, prem1, prem2, phi).toOption)

      inferred match
        case Some(thm) => successful(thm, conclusion)
        case None => inferenceFailure("Could not infer the Cut pivot.", conclusion, "First premise" -> prem1, "Second premise" -> prem2)

  object LeftAnd extends PremiseSequentTactic:
    private def prove(conclusion: K.Sequent, premise: K.Thm, phi: KF.Expression, psi: KF.Expression)(using library: Library): K.LeftAnd.Result[K.Thm] =
      K.LeftAnd(using library.theory)(conclusion, premise, phi, psi)

    private def liftError(conclusion: Sequent, premise: K.Thm, phi: Expr[Prop], psi: Expr[Prop])(
        err: K.LeftAnd.ErrorType
    ): Failure =
      err match
        case _: K.LeftAnd.MissingFromPremise =>
          Failure(withParams("LeftAnd: RHS of premise is not contained in the conclusion.", "Premise" -> premise, "Conclusion" -> conclusion))
        case _: K.LeftAnd.ExtraneousInPremise =>
          Failure(
            withParams(
              "LeftAnd: LHS of premise contains a formula other than the provided or inferred conjuncts that is absent from the conclusion.",
              "Phi" -> phi,
              "Psi" -> psi,
              "Premise" -> premise,
              "Conclusion" -> conclusion
            )
          )
        case _: K.LeftAnd.MissingConjunction =>
          Failure(
            withParams("LeftAnd: conclusion does not contain the provided conjunction.", "Conjunction" -> (phi /\ psi), "Premise" -> premise, "Conclusion" -> conclusion)
          )
        case e: K.GeneralError => liftGeneralError("LeftAnd", e)

    def withParameters(using
        file: sourcecode.File,
        line: sourcecode.Line
    )(using
        library: Library
    )(phi: Expr[Prop], psi: Expr[Prop])(
        premise: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, premise, phi.underlying, psi.underlying)
        .mapLeft(liftError(conclusion, premise, phi, psi))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
      val underlying = conclusion.underlying

      val inferred = conclusion.left.collectFirstDefined:
        case phi /\ psi =>
          prove(underlying, premise, phi.underlying, psi.underlying).toOption
        case _ => None

      inferred match
        case Some(thm) => successful(thm, conclusion)
        case None => inferenceFailure("Could not infer conjuncts for LeftAnd.", conclusion, "Premise" -> premise)

  object LeftOr:
    private def prove(conclusion: K.Sequent, premises: Seq[K.Thm], disjuncts: Seq[KF.Expression])(using library: Library): K.LeftOr.Result[K.Thm] =
      K.LeftOr(using library.theory)(conclusion, premises, disjuncts)

    private def liftError(conclusion: Sequent, premises: Seq[K.Thm], disjuncts: Seq[Expr[Prop]])(
        err: K.LeftOr.ErrorType
    ): Failure =
      err match
        case _: K.LeftOr.EmptyPremises =>
          Failure("LeftOr: requires at least one premise.")
        case _: K.LeftOr.ArityMismatch =>
          Failure(withParams("LeftOr: disjunct and premise counts are mismatched.", "# Premises" -> premises.size, "# Disjuncts" -> disjuncts.size))
        case e: K.LeftOr.PremiseNotPreserved =>
          Failure(withParams("LeftOr: a formula in a premise is absent from the conclusion.", "Premise index" -> e.index, "Disjunct" -> disjuncts(e.index)))
        case _: K.LeftOr.MissingDisjunction =>
          Failure(withParams("LeftOr: the conclusion does not contain the disjunction.", "Disjuncts" -> disjuncts))
        case e: K.GeneralError => liftGeneralError("LeftOr", e)

    def withParameters(using
        file: sourcecode.File,
        line: sourcecode.Line
    )(using
        library: Library
    )(disjuncts: Seq[Expr[Prop]])(
        premises: Seq[K.Thm]
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, premises, disjuncts.map(_.underlying))
        .mapLeft(liftError(conclusion, premises, disjuncts))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(premises: Seq[K.Thm])(conclusion: Sequent): ProofJudgement =
      val underlying = conclusion.underlying
      if premises.isEmpty then inferenceFailure("LeftOr: requires at least one premise.", conclusion)
      else
        val extras = premises.map(premise => differenceEq(premise.left, underlying.left).nextOption())
        val inferred =
          if extras.forall(_.nonEmpty) then prove(underlying, premises, extras.flatten).toOption
          else
            extras.indexWhere(_.isEmpty) match
              case -1 => None
              case i => weakening(underlying, premises(i))

        inferred.fold(inferenceFailure("Could not infer disjuncts for LeftOr.", conclusion, "Premises" -> premises))(thm => successful(thm, conclusion))

    def apply(using
        file: sourcecode.File,
        line: sourcecode.Line
    )(using
        library: Library
    )(prem1: K.Thm, prem2: K.Thm, rest: K.Thm*)(
        conclusion: Sequent
    ): ProofJudgement =
      apply(using file, line)(using library)(prem1 +: prem2 +: rest)(conclusion)

  object LeftImplies:
    private def prove(conclusion: K.Sequent, prem1: K.Thm, prem2: K.Thm, phi: KF.Expression, psi: KF.Expression)(using
        library: Library
    ): K.LeftImplies.Result[K.Thm] =
      K.LeftImplies(using library.theory)(conclusion, prem1, prem2, phi, psi)

    private def liftError(conclusion: Sequent, prem1: K.Thm, prem2: K.Thm, phi: Expr[Prop], psi: Expr[Prop])(
        err: K.LeftImplies.ErrorType
    ): Failure =
      err match
        case _: K.LeftImplies.MissingFromFirst =>
          Failure(withParams("The first premise left side is not contained in the LeftImplies conclusion.", "Premise" -> prem1))
        case _: K.LeftImplies.MissingFromSecond =>
          Failure(withParams("The second premise right side is not contained in the LeftImplies conclusion.", "Premise" -> prem2))
        case _: K.LeftImplies.ExtraneousInFirst =>
          Failure(
            withParams("The first premise right side contains a formula other than the implication antecedent that is absent from the conclusion.", "Antecedent" -> phi)
          )
        case _: K.LeftImplies.ExtraneousInSecond =>
          Failure(
            withParams("The second premise left side contains a formula other than the implication consequent that is absent from the conclusion.", "Consequent" -> psi)
          )
        case _: K.LeftImplies.MissingImplication =>
          Failure(withParams("The LeftImplies conclusion does not contain the requested implication.", "Implication" -> implies(phi)(psi)))
        case e: K.GeneralError => liftGeneralError("LeftImplies", e)

    def withParameters(using
        file: sourcecode.File,
        line: sourcecode.Line
    )(using
        library: Library
    )(phi: Expr[Prop], psi: Expr[Prop])(
        prem1: K.Thm,
        prem2: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, prem1, prem2, phi.underlying, psi.underlying)
        .mapLeft(liftError(conclusion, prem1, prem2, phi, psi))
        .lift(conclusion)

    def apply(using
        file: sourcecode.File,
        line: sourcecode.Line
    )(using
        library: Library
    )(prem1: K.Thm, prem2: K.Thm)(
        conclusion: Sequent
    ): ProofJudgement =
      val underlying = conclusion.underlying

      val antecedent = differenceEq(prem1.right, underlying.right).nextOption()
      val consequent = differenceEq(prem2.left, underlying.left).nextOption()

      val inferred =
        (antecedent, consequent) match
          case (None, _) => weakening(underlying, prem1)
          case (_, None) => weakening(underlying, prem2)
          case (Some(phi), Some(psi)) => prove(underlying, prem1, prem2, phi, psi).toOption

      inferred match
        case Some(thm) => successful(thm, conclusion)
        case None => inferenceFailure("Could not infer the antecedent and consequent for LeftImplies.", conclusion, "First premise" -> prem1, "Second premise" -> prem2)

  object LeftIff extends PremiseSequentTactic:
    private def prove(conclusion: K.Sequent, premise: K.Thm, phi: KF.Expression, psi: KF.Expression)(using library: Library): K.LeftIff.Result[K.Thm] =
      K.LeftIff(using library.theory)(conclusion, premise, phi, psi)

    private def liftError(conclusion: Sequent, premise: K.Thm, phi: Expr[Prop], psi: Expr[Prop])(
        err: K.LeftIff.ErrorType
    ): Failure =
      err match
        case _: K.LeftIff.MissingFromPremise =>
          Failure(withParams("The premise right side is not contained in the LeftIff conclusion.", "Premise" -> premise))
        case _: K.LeftIff.ExtraneousInPremise =>
          Failure(
            withParams(
              "The premise left side contains a formula other than the two directions of the equivalence that is absent from the conclusion.",
              "Phi" -> phi,
              "Psi" -> psi
            )
          )
        case _: K.LeftIff.MissingIff =>
          Failure(withParams("The LeftIff conclusion does not contain the requested equivalence.", "Equivalence" -> iff(phi)(psi)))
        case e: K.GeneralError => liftGeneralError("LeftIff", e)

    def withParameters(using
        file: sourcecode.File,
        line: sourcecode.Line
    )(using
        library: Library
    )(phi: Expr[Prop], psi: Expr[Prop])(
        premise: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, premise, phi.underlying, psi.underlying)
        .mapLeft(liftError(conclusion, premise, phi, psi))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
      val underlying = conclusion.underlying
      val pivot = differenceEq(premise.left, underlying.left).nextOption()
      val inferred =
        pivot match
          case None => weakening(underlying, premise)
          case Some(KF.implies(phi, psi)) => prove(underlying, premise, phi, psi).toOption
          case _ => None
      inferred match
        case Some(thm) => successful(thm, conclusion)
        case None => inferenceFailure("Could not infer the equivalent formulas for LeftIff.", conclusion, "Premise" -> premise)

  object LeftNot extends PremiseSequentTactic:
    private def prove(conclusion: K.Sequent, premise: K.Thm, phi: KF.Expression)(using library: Library): K.LeftNot.Result[K.Thm] =
      K.LeftNot(using library.theory)(conclusion, premise, phi)

    private def liftError(conclusion: Sequent, premise: K.Thm, phi: Expr[Prop])(
        err: K.LeftNot.ErrorType
    ): Failure =
      err match
        case _: K.LeftNot.MissingFromPremise =>
          Failure(withParams("The premise left side is not contained in the LeftNot conclusion.", "Premise" -> premise))
        case _: K.LeftNot.ExtraneousInPremise =>
          Failure(withParams("The premise right side contains a formula other than the negated formula that is absent from the conclusion.", "Formula" -> phi))
        case _: K.LeftNot.MissingNegation =>
          Failure(withParams("The LeftNot conclusion does not contain the requested negation.", "Negation" -> neg(phi)))
        case e: K.GeneralError => liftGeneralError("LeftNot", e)

    def withParameters(using
        file: sourcecode.File,
        line: sourcecode.Line
    )(using
        library: Library
    )(phi: Expr[Prop])(premise: K.Thm)(
        conclusion: Sequent
    ): ProofJudgement =
      prove(conclusion.underlying, premise, phi.underlying)
        .mapLeft(liftError(conclusion, premise, phi))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
      val underlying = conclusion.underlying
      val pivot = differenceEq(premise.right, underlying.right).nextOption()
      val inferred =
        pivot match
          case None => weakening(underlying, premise)
          case Some(phi) => prove(underlying, premise, phi).toOption
      inferred match
        case Some(thm) => successful(thm, conclusion)
        case None => inferenceFailure("Could not infer the negated formula for LeftNot.", conclusion, "Premise" -> premise)

  object LeftForall extends PremiseSequentTactic:
    private def prove(conclusion: K.Sequent, premise: K.Thm, phi: KF.Expression, x: KF.Variable, term: KF.Expression)(using
        library: Library
    ): K.LeftForall.Result[K.Thm] =
      K.LeftForall(using library.theory)(conclusion, premise, phi, x, term)

    private def liftError(conclusion: Sequent, premise: K.Thm, phi: Expr[Prop], x: Variable[Ind], term: Expr[Ind])(
        err: K.LeftForall.ErrorType
    ): Failure =
      err match
        case _: K.LeftForall.MissingFromPremise =>
          Failure(withParams("The premise right side is not contained in the LeftForall conclusion.", "Premise" -> premise))
        case _: K.LeftForall.ExtraneousInPremise =>
          Failure(
            withParams(
              "The premise left side contains a formula other than the quantified instance that is absent from the conclusion.",
              "Body" -> phi,
              "Variable" -> x,
              "Term" -> term
            )
          )
        case _: K.LeftForall.MissingForall =>
          Failure(withParams("The LeftForall conclusion does not contain the requested universal formula.", "Formula" -> forall(x, phi)))
        case e: K.GeneralError => liftGeneralError("LeftForall", e)

    def withParameters(using
        file: sourcecode.File,
        line: sourcecode.Line
    )(using
        library: Library
    )(phi: Expr[Prop], x: Variable[Ind], term: Expr[Ind])(
        premise: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, premise, phi.underlying, x.underlying, term.underlying)
        .mapLeft(liftError(conclusion, premise, phi, x, term))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
      val underlying = conclusion.underlying
      val quantified = differenceEq(underlying.left, premise.left).nextOption()
      val instantiated = differenceEq(premise.left, underlying.left).nextOption()
      val inferred = (quantified, instantiated) match
        case (Some(KF.forall(KF.Lambda(x: KF.Variable, phi))), Some(instance)) =>
          localTermCandidates(instance, x).collectFirstDefined(term => prove(underlying, premise, phi, x, term).toOption)
        case (None, None) => weakening(underlying, premise)
        case (None, Some(instance)) =>
          underlying.left.iterator.collectFirstDefined:
            case KF.forall(KF.Lambda(x: KF.Variable, phi)) =>
              localTermCandidates(instance, x).collectFirstDefined(term => prove(underlying, premise, phi, x, term).toOption)
            case _ => None
        case _ => None

      inferred match
        case Some(thm) => successful(thm, conclusion)
        case None => inferenceFailure("Could not infer the universal formula or its instantiating term for LeftForall.", conclusion, "Premise" -> premise)

  object LeftExists extends PremiseSequentTactic:
    private def prove(conclusion: K.Sequent, premise: K.Thm, phi: KF.Expression, x: KF.Variable)(using library: Library): K.LeftExists.Result[K.Thm] =
      K.LeftExists(using library.theory)(conclusion, premise, phi, x)

    private def liftError(conclusion: Sequent, premise: K.Thm, phi: Expr[Prop], x: Variable[Ind])(
        err: K.LeftExists.ErrorType
    ): Failure =
      err match
        case _: K.LeftExists.MissingFromPremise =>
          Failure(withParams("The premise right side is not contained in the LeftExists conclusion.", "Premise" -> premise))
        case _: K.LeftExists.ExtraneousInPremise =>
          Failure(withParams("The premise left side contains a formula other than the existential body that is absent from the conclusion.", "Body" -> phi))
        case _: K.LeftExists.MissingExists =>
          Failure(withParams("The LeftExists conclusion does not contain the requested existential formula.", "Formula" -> exists(x, phi)))
        case _: K.LeftExists.VariableFree =>
          Failure(withParams("The existential variable is free in the LeftExists conclusion.", "Variable" -> x, "Conclusion" -> conclusion))
        case e: K.GeneralError => liftGeneralError("LeftExists", e)

    def withParameters(using
        file: sourcecode.File,
        line: sourcecode.Line
    )(using
        library: Library
    )(phi: Expr[Prop], x: Variable[Ind])(
        premise: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, premise, phi.underlying, x.underlying)
        .mapLeft(liftError(conclusion, premise, phi, x))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
      val underlying = conclusion.underlying
      val pivot = differenceEq(underlying.left, premise.left).nextOption()
      val body = differenceEq(premise.left, underlying.left).nextOption()
      val inferred = (pivot, body) match
        case (Some(KF.exists(KF.Lambda(x: KF.Variable, phi))), _) => prove(underlying, premise, phi, x).toOption
        case (None, None) => weakening(underlying, premise)
        case (None, Some(instance)) =>
          underlying.left.iterator.collectFirstDefined:
            case KF.exists(KF.Lambda(x: KF.Variable, phi)) if KF.isSame(phi, instance) =>
              prove(underlying, premise, phi, x).toOption
            case _ => None
        case _ => None
      inferred match
        case Some(thm) => successful(thm, conclusion)
        case None => inferenceFailure("Could not infer the existential formula for LeftExists.", conclusion, "Premise" -> premise)

  object RightAnd:
    private def prove(conclusion: K.Sequent, premises: Seq[K.Thm], conjuncts: Seq[KF.Expression])(using library: Library): K.RightAnd.Result[K.Thm] =
      K.RightAnd(using library.theory)(conclusion, premises, conjuncts)

    private def liftError(conclusion: Sequent, premises: Seq[K.Thm], conjuncts: Seq[Expr[Prop]])(
        err: K.RightAnd.ErrorType
    ): Failure =
      err match
        case _: K.RightAnd.EmptyPremises =>
          Failure("RightAnd requires at least one premise.")
        case _: K.RightAnd.ArityMismatch =>
          Failure(withParams("RightAnd requires one conjunct per premise.", "Premises" -> premises.size, "Conjuncts" -> conjuncts.size))
        case e: K.RightAnd.PremiseNotPreserved =>
          Failure(
            withParams("A RightAnd premise is not preserved by the conclusion apart from its conjunct.", "Premise index" -> e.index, "Conjunct" -> conjuncts(e.index))
          )
        case _: K.RightAnd.MissingConjunction =>
          Failure(withParams("The RightAnd conclusion does not contain the conjunction.", "Conjuncts" -> conjuncts))
        case e: K.GeneralError => liftGeneralError("RightAnd", e)

    def withParameters(using
        file: sourcecode.File,
        line: sourcecode.Line
    )(using
        library: Library
    )(conjuncts: Seq[Expr[Prop]])(
        premises: Seq[K.Thm]
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, premises, conjuncts.map(_.underlying))
        .mapLeft(liftError(conclusion, premises, conjuncts))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(premises: Seq[K.Thm])(conclusion: Sequent): ProofJudgement =
      val underlying = conclusion.underlying
      if premises.isEmpty then inferenceFailure("RightAnd requires at least one premise.", conclusion)
      else
        val extras = premises.map(premise => differenceEq(premise.right, underlying.right).nextOption())
        val inferred =
          if extras.forall(_.nonEmpty) then prove(underlying, premises, extras.flatten).toOption
          else
            extras.indexWhere(_.isEmpty) match
              case -1 => None
              case i => weakening(underlying, premises(i))

        inferred.fold(inferenceFailure("Could not infer conjuncts for RightAnd.", conclusion, "Premises" -> premises))(thm => successful(thm, conclusion))

    def apply(using
        file: sourcecode.File,
        line: sourcecode.Line
    )(using
        library: Library
    )(prem1: K.Thm, prem2: K.Thm, rest: K.Thm*)(
        conclusion: Sequent
    ): ProofJudgement =
      apply(using file, line)(using library)(prem1 +: prem2 +: rest)(conclusion)

  object RightOr extends PremiseSequentTactic:
    private def prove(conclusion: K.Sequent, premise: K.Thm, phi: KF.Expression, psi: KF.Expression)(using library: Library): K.RightOr.Result[K.Thm] =
      K.RightOr(using library.theory)(conclusion, premise, phi, psi)

    private def liftError(conclusion: Sequent, premise: K.Thm, phi: Expr[Prop], psi: Expr[Prop])(
        err: K.RightOr.ErrorType
    ): Failure =
      err match
        case _: K.RightOr.MissingFromPremise =>
          Failure(withParams("The premise left side is not contained in the RightOr conclusion.", "Premise" -> premise, "Conclusion" -> conclusion))
        case _: K.RightOr.ExtraneousInPremise =>
          Failure(
            withParams("The premise right side contains a formula other than the inferred disjuncts that is absent from the conclusion.", "Phi" -> phi, "Psi" -> psi)
          )
        case _: K.RightOr.MissingDisjunction =>
          Failure(withParams("The RightOr conclusion does not contain the requested disjunction.", "Disjunction" -> or(phi)(psi)))
        case e: K.GeneralError => liftGeneralError("RightOr", e)

    def withParameters(using
        file: sourcecode.File,
        line: sourcecode.Line
    )(using
        library: Library
    )(phi: Expr[Prop], psi: Expr[Prop])(
        premise: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, premise, phi.underlying, psi.underlying)
        .mapLeft(liftError(conclusion, premise, phi, psi))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
      val underlying = conclusion.underlying
      val pivot = differenceEq(underlying.right, premise.right).nextOption()
      val inferred = pivot match
        case Some(KF.or(phi, psi)) =>
          Iterator(phi -> psi, psi -> phi).collectFirstDefined { case (left, right) =>
            prove(underlying, premise, left, right).toOption
          }
        case None => weakening(underlying, premise)
        case _ => None

      inferred match
        case Some(thm) => successful(thm, conclusion)
        case None => inferenceFailure("Could not infer disjuncts for RightOr.", conclusion, "Premise" -> premise)

  object RightImplies extends PremiseSequentTactic:
    private def prove(conclusion: K.Sequent, premise: K.Thm, phi: KF.Expression, psi: KF.Expression)(using library: Library): K.RightImplies.Result[K.Thm] =
      K.RightImplies(using library.theory)(conclusion, premise, phi, psi)

    private def liftError(conclusion: Sequent, premise: K.Thm, phi: Expr[Prop], psi: Expr[Prop])(
        err: K.RightImplies.ErrorType
    ): Failure =
      err match
        case _: K.RightImplies.ExtraneousInLeft =>
          Failure(
            withParams("The RightImplies premise left side contains a formula other than the antecedent that is absent from the conclusion.", "Antecedent" -> phi)
          )
        case _: K.RightImplies.ExtraneousInRight =>
          Failure(
            withParams("The RightImplies premise right side contains a formula other than the consequent that is absent from the conclusion.", "Consequent" -> psi)
          )
        case _: K.RightImplies.MissingImplication =>
          Failure(withParams("The RightImplies conclusion does not contain the requested implication.", "Implication" -> implies(phi)(psi)))
        case e: K.GeneralError => liftGeneralError("RightImplies", e)

    def withParameters(using
        file: sourcecode.File,
        line: sourcecode.Line
    )(using
        library: Library
    )(phi: Expr[Prop], psi: Expr[Prop])(
        premise: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, premise, phi.underlying, psi.underlying)
        .mapLeft(liftError(conclusion, premise, phi, psi))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
      val underlying = conclusion.underlying
      val antecedent = differenceEq(premise.left, underlying.left).nextOption()
      val consequent = differenceEq(premise.right, underlying.right).nextOption()
      val inferred = (antecedent, consequent) match
        case (Some(phi), Some(psi)) => prove(underlying, premise, phi, psi).toOption
        case _ => None

      inferred match
        case Some(thm) => successful(thm, conclusion)
        case None => inferenceFailure("Could not infer the antecedent and consequent for RightImplies.", conclusion, "Premise" -> premise)

  object RightIff:
    private def prove(conclusion: K.Sequent, prem1: K.Thm, prem2: K.Thm, phi: KF.Expression, psi: KF.Expression)(using
        library: Library
    ): K.RightIff.Result[K.Thm] =
      K.RightIff(using library.theory)(conclusion, prem1, prem2, phi, psi)

    private def liftError(conclusion: Sequent, prem1: K.Thm, prem2: K.Thm, phi: Expr[Prop], psi: Expr[Prop])(
        err: K.RightIff.ErrorType
    ): Failure =
      err match
        case _: K.RightIff.MissingFromFirst =>
          Failure(withParams("The first RightIff premise left side is not contained in the conclusion.", "Premise" -> prem1))
        case _: K.RightIff.MissingFromSecond =>
          Failure(withParams("The second RightIff premise left side is not contained in the conclusion.", "Premise" -> prem2))
        case _: K.RightIff.ExtraneousInFirst =>
          Failure(
            withParams("The first RightIff premise right side contains a formula other than the forward implication.", "Forward implication" -> implies(phi)(psi))
          )
        case _: K.RightIff.ExtraneousInSecond =>
          Failure(
            withParams("The second RightIff premise right side contains a formula other than the backward implication.", "Backward implication" -> implies(psi)(phi))
          )
        case _: K.RightIff.MissingIff =>
          Failure(withParams("The RightIff conclusion does not contain the requested equivalence.", "Equivalence" -> iff(phi)(psi)))
        case e: K.GeneralError => liftGeneralError("RightIff", e)

    def withParameters(using
        file: sourcecode.File,
        line: sourcecode.Line
    )(using
        library: Library
    )(phi: Expr[Prop], psi: Expr[Prop])(
        prem1: K.Thm,
        prem2: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, prem1, prem2, phi.underlying, psi.underlying)
        .mapLeft(liftError(conclusion, prem1, prem2, phi, psi))
        .lift(conclusion)

    def apply(using
        file: sourcecode.File,
        line: sourcecode.Line
    )(using
        library: Library
    )(prem1: K.Thm, prem2: K.Thm)(
        conclusion: Sequent
    ): ProofJudgement =
      val underlying = conclusion.underlying
      val pivot = differenceEq(prem1.right, underlying.right).nextOption()
      val inferred = pivot match
        case Some(KF.implies(phi, psi)) => prove(underlying, prem1, prem2, phi, psi).toOption
        case None => weakening(underlying, prem1)
        case _ => None
      inferred match
        case Some(thm) => successful(thm, conclusion)
        case None => inferenceFailure("Could not infer the equivalent formulas for RightIff.", conclusion, "First premise" -> prem1, "Second premise" -> prem2)

  object RightNot extends PremiseSequentTactic:
    private def prove(conclusion: K.Sequent, premise: K.Thm, phi: KF.Expression)(using library: Library): K.RightNot.Result[K.Thm] =
      K.RightNot(using library.theory)(conclusion, premise, phi)

    private def liftError(conclusion: Sequent, premise: K.Thm, phi: Expr[Prop])(
        err: K.RightNot.ErrorType
    ): Failure =
      err match
        case _: K.RightNot.MissingFromPremise =>
          Failure(withParams("The premise right side is not contained in the RightNot conclusion.", "Premise" -> premise))
        case _: K.RightNot.ExtraneousInPremise =>
          Failure(withParams("The premise left side contains a formula other than the negated formula that is absent from the conclusion.", "Formula" -> phi))
        case _: K.RightNot.MissingNegation =>
          Failure(withParams("The RightNot conclusion does not contain the requested negation.", "Negation" -> neg(phi)))
        case e: K.GeneralError => liftGeneralError("RightNot", e)

    def withParameters(using
        file: sourcecode.File,
        line: sourcecode.Line
    )(using
        library: Library
    )(phi: Expr[Prop])(premise: K.Thm)(
        conclusion: Sequent
    ): ProofJudgement =
      prove(conclusion.underlying, premise, phi.underlying)
        .mapLeft(liftError(conclusion, premise, phi))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
      val underlying = conclusion.underlying
      val pivot = differenceEq(premise.left, underlying.left).nextOption()
      val inferred =
        pivot match
          case None => weakening(underlying, premise)
          case Some(phi) => prove(underlying, premise, phi).toOption
      inferred match
        case Some(thm) => successful(thm, conclusion)
        case None => inferenceFailure("Could not infer the negated formula for RightNot.", conclusion, "Premise" -> premise)

  object RightForall extends PremiseSequentTactic:
    private def prove(conclusion: K.Sequent, premise: K.Thm, phi: KF.Expression, x: KF.Variable)(using library: Library): K.RightForall.Result[K.Thm] =
      K.RightForall(using library.theory)(conclusion, premise, phi, x)

    private def liftError(conclusion: Sequent, premise: K.Thm, phi: Expr[Prop], x: Variable[Ind])(
        err: K.RightForall.ErrorType
    ): Failure =
      err match
        case _: K.RightForall.MissingFromPremise =>
          Failure(withParams("The premise left side is not contained in the RightForall conclusion.", "Premise" -> premise))
        case _: K.RightForall.ExtraneousInPremise =>
          Failure(withParams("The premise right side contains a formula other than the universal body that is absent from the conclusion.", "Body" -> phi))
        case _: K.RightForall.MissingForall =>
          Failure(withParams("The RightForall conclusion does not contain the requested universal formula.", "Formula" -> forall(x, phi)))
        case _: K.RightForall.VariableFree =>
          Failure(withParams("The universal variable is free in the RightForall conclusion.", "Variable" -> x, "Conclusion" -> conclusion))
        case e: K.GeneralError => liftGeneralError("RightForall", e)

    def withParameters(using
        file: sourcecode.File,
        line: sourcecode.Line
    )(using
        library: Library
    )(phi: Expr[Prop], x: Variable[Ind])(
        premise: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, premise, phi.underlying, x.underlying)
        .mapLeft(liftError(conclusion, premise, phi, x))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
      val underlying = conclusion.underlying
      val pivot = differenceEq(underlying.right, premise.right).nextOption()
      val body = differenceEq(premise.right, underlying.right).nextOption()
      val inferred = (pivot, body) match
        case (Some(KF.forall(KF.Lambda(x: KF.Variable, phi))), _) => prove(underlying, premise, phi, x).toOption
        case (None, None) => weakening(underlying, premise)
        case (None, Some(instance)) =>
          underlying.right.iterator.collectFirstDefined:
            case KF.forall(KF.Lambda(x: KF.Variable, phi)) if KF.isSame(phi, instance) =>
              prove(underlying, premise, phi, x).toOption
            case _ => None
        case _ => None
      inferred match
        case Some(thm) => successful(thm, conclusion)
        case None => inferenceFailure("Could not infer the universal formula for RightForall.", conclusion, "Premise" -> premise)

  object RightExists extends PremiseSequentTactic:
    private def prove(conclusion: K.Sequent, premise: K.Thm, phi: KF.Expression, x: KF.Variable, term: KF.Expression)(using
        library: Library
    ): K.RightExists.Result[K.Thm] =
      K.RightExists(using library.theory)(conclusion, premise, phi, x, term)

    private def liftError(conclusion: Sequent, premise: K.Thm, phi: Expr[Prop], x: Variable[Ind], term: Expr[Ind])(
        err: K.RightExists.ErrorType
    ): Failure =
      err match
        case _: K.RightExists.MissingFromPremise =>
          Failure(withParams("The premise left side is not contained in the RightExists conclusion.", "Premise" -> premise))
        case _: K.RightExists.ExtraneousInPremise =>
          Failure(
            withParams(
              "The premise right side contains a formula other than the existential instance that is absent from the conclusion.",
              "Body" -> phi,
              "Variable" -> x,
              "Term" -> term
            )
          )
        case _: K.RightExists.MissingExists =>
          Failure(withParams("The RightExists conclusion does not contain the requested existential formula.", "Formula" -> exists(x, phi)))
        case e: K.GeneralError => liftGeneralError("RightExists", e)

    def withParameters(using
        file: sourcecode.File,
        line: sourcecode.Line
    )(using
        library: Library
    )(phi: Expr[Prop], x: Variable[Ind], term: Expr[Ind])(
        premise: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, premise, phi.underlying, x.underlying, term.underlying)
        .mapLeft(liftError(conclusion, premise, phi, x, term))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
      val underlying = conclusion.underlying
      val quantified = differenceEq(underlying.right, premise.right).nextOption()
      val instantiated = differenceEq(premise.right, underlying.right).nextOption()
      val inferred = (quantified, instantiated) match
        case (Some(KF.exists(KF.Lambda(x: KF.Variable, phi))), Some(instance)) =>
          localTermCandidates(instance, x).collectFirstDefined(term => prove(underlying, premise, phi, x, term).toOption)
        case (None, None) => weakening(underlying, premise)
        case (None, Some(instance)) =>
          underlying.right.iterator.collectFirstDefined:
            case KF.exists(KF.Lambda(x: KF.Variable, phi)) =>
              localTermCandidates(instance, x).collectFirstDefined(term => prove(underlying, premise, phi, x, term).toOption)
            case _ => None
        case _ => None

      inferred match
        case Some(thm) => successful(thm, conclusion)
        case None => inferenceFailure("Could not infer the existential formula or its instantiating term for RightExists.", conclusion, "Premise" -> premise)

  object RightEpsilon extends PremiseSequentTactic:
    private def prove(conclusion: K.Sequent, premise: K.Thm, phi: KF.Expression, x: KF.Variable, term: KF.Expression)(using
        library: Library
    ): K.RightEpsilon.Result[K.Thm] =
      K.RightEpsilon(using library.theory)(conclusion, premise, phi, x, term)

    private def liftError(conclusion: Sequent, premise: K.Thm, phi: Expr[Prop], x: Variable[Ind], term: Expr[Ind])(
        err: K.RightEpsilon.ErrorType
    ): Failure =
      err match
        case _: K.RightEpsilon.MissingFromPremise =>
          Failure(withParams("The premise left side is not contained in the RightEpsilon conclusion.", "Premise" -> premise))
        case _: K.RightEpsilon.ExtraneousInPremise =>
          Failure(
            withParams(
              "The premise right side contains a formula other than the epsilon source instance that is absent from the conclusion.",
              "Body" -> phi,
              "Variable" -> x,
              "Term" -> term
            )
          )
        case _: K.RightEpsilon.MissingEpsilonInstance =>
          Failure(withParams("The RightEpsilon conclusion does not contain the epsilon instance.", "Body" -> phi, "Variable" -> x))
        case e: K.GeneralError => liftGeneralError("RightEpsilon", e)

    def withParameters(using
        file: sourcecode.File,
        line: sourcecode.Line
    )(using
        library: Library
    )(phi: Expr[Prop], x: Variable[Ind], term: Expr[Ind])(
        premise: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, premise, phi.underlying, x.underlying, term.underlying)
        .mapLeft(liftError(conclusion, premise, phi, x, term))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
      val underlying = conclusion.underlying
      val source = differenceEq(premise.right, underlying.right).nextOption()
      val target = differenceEq(underlying.right, premise.right).nextOption()
      val inferred = (source, target) match
        case (Some(instance), Some(result)) =>
          Helpers
            .subexpressions(Seq(result))
            .collectFirstDefined:
              case KF.epsilon(KF.Lambda(x: KF.Variable, phi)) =>
                localTermCandidates(instance, x).collectFirstDefined(term => prove(underlying, premise, phi, x, term).toOption)
              case _ => None
        case _ => None
      inferred match
        case Some(thm) => successful(thm, conclusion)
        case None => inferenceFailure("Could not infer the epsilon formula or source term for RightEpsilon.", conclusion, "Premise" -> premise)

  object Weakening extends PremiseSequentTactic:
    private def liftError(conclusion: Sequent, premise: K.Thm)(err: K.Weakening.ErrorType): Failure =
      err match
        case _: K.Weakening.NotImplying =>
          Failure(withParams("Weakening premise does not imply the conclusion.", "Premise" -> premise, "Conclusion" -> conclusion))
        case e: K.GeneralError => liftGeneralError("Weakening", e)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
      K.Weakening(using library.theory)(conclusion.underlying, premise)
        .mapLeft(liftError(conclusion, premise))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(premise: K.Thm)(conclusion: Sequent): ProofJudgement =
      apply(using file, line)(using library)(conclusion, premise)

  object LeftRefl extends PremiseSequentTactic:
    private def prove(conclusion: K.Sequent, premise: K.Thm, equality: KF.Expression)(using library: Library): K.LeftRefl.Result[K.Thm] =
      K.LeftRefl(using library.theory)(conclusion, premise, equality)

    private def liftError(conclusion: Sequent, premise: K.Thm, equality: Any)(err: K.LeftRefl.ErrorType): Failure =
      err match
        case _: K.LeftRefl.NotAnEquality =>
          Failure(withParams("LeftRefl parameter is not an equality.", "Expression" -> equality))
        case _: K.LeftRefl.EqualityNotReflexive =>
          Failure(withParams("LeftRefl equality is not reflexive up to the active equality.", "Equality" -> equality))
        case _: K.LeftRefl.MissingFromPremise =>
          Failure(withParams("The premise right side is not contained in the LeftRefl conclusion.", "Premise" -> premise))
        case _: K.LeftRefl.ExtraneousInPremise =>
          Failure(
            withParams("The premise left side contains a formula other than the reflexive equality that is absent from the conclusion.", "Equality" -> equality)
          )
        case e: K.GeneralError => liftGeneralError("LeftRefl", e)

    def withParameters(using
        file: sourcecode.File,
        line: sourcecode.Line
    )(using
        library: Library
    )(equality: Expr[Prop])(
        premise: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, premise, equality.underlying)
        .mapLeft(liftError(conclusion, premise, equality))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
      val underlying = conclusion.underlying
      differenceEq(premise.left, underlying.left).nextOption().flatMap(eq => prove(underlying, premise, eq).toOption) match
        case Some(thm) => successful(thm, conclusion)
        case None => inferenceFailure("Could not infer a reflexive equality for LeftRefl.", conclusion, "Premise" -> premise)

  object RightRefl extends SequentTactic:
    private def prove(conclusion: K.Sequent, equality: KF.Expression)(using library: Library): K.RightRefl.Result[K.Thm] =
      K.RightRefl(using library.theory)(conclusion, equality)

    private def liftError(conclusion: Sequent, equality: Any)(err: K.RightRefl.ErrorType): Failure =
      err match
        case _: K.RightRefl.NotAnEquality =>
          Failure(withParams("RightRefl parameter is not an equality.", "Expression" -> equality))
        case _: K.RightRefl.EqualityNotReflexive =>
          Failure(withParams("RightRefl equality is not reflexive up to the active equality.", "Equality" -> equality))
        case _: K.RightRefl.MissingEquality =>
          Failure(withParams("The RightRefl conclusion does not contain the requested equality.", "Equality" -> equality))
        case e: K.GeneralError => liftGeneralError("RightRefl", e)

    def withParameters(using
        file: sourcecode.File,
        line: sourcecode.Line
    )(using
        library: Library
    )(equality: Expr[Prop])(
        conclusion: Sequent
    ): ProofJudgement =
      prove(conclusion.underlying, equality.underlying)
        .mapLeft(liftError(conclusion, equality))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent): ProofJudgement =
      val underlying = conclusion.underlying
      val candidates = underlying.right.iterator.collect:
        case eq @ KF.equality(_, _) => eq
      val inferred = candidates.collectFirstDefined(eq => prove(underlying, eq).toOption)
      inferred.fold(inferenceFailure("Could not infer a reflexive equality for RightRefl.", conclusion))(thm => successful(thm, conclusion))

  /**
   * Share parameter recovery between left and right substitution.
   */
  sealed abstract class SubstTactic private[BasicStep] (onLeft: Boolean):
    private val name = if onLeft then "LeftSubst" else "RightSubst"

    private def prove(
        conclusion: K.Sequent,
        premise: K.Thm,
        comparisons: Seq[K.Thm],
        replacements: Seq[(KF.Expression, KF.Expression, Seq[KF.Variable])],
        context: (Seq[KF.Variable], KF.Expression)
    )(using library: Library): K.LeftSubst.Result[K.Thm] =
      if onLeft then K.LeftSubst(using library.theory)(conclusion, premise, comparisons, replacements, context)
      else K.RightSubst(using library.theory)(conclusion, premise, comparisons, replacements, context)

    private def lift(result: lisa.utils.kernel.Substitution.Result, conclusion: Sequent): ProofJudgement =
      result.mapLeft(message => Failure(withParams(s"$name: $message", "Conclusion" -> conclusion))).lift(conclusion)

    /**
     * Apply the kernel rule with one pointwise comparison proof per replacement.
     */
    def withParameters(using
        file: sourcecode.File,
        line: sourcecode.Line
    )(using
        library: Library
    )(
        replacements: Seq[(Expr[?], Expr[?], Seq[Variable[?]])],
        context: (Seq[Variable[?]], Expr[Prop])
    )(premise: K.Thm, comparisons: Seq[K.Thm])(conclusion: Sequent): ProofJudgement =
      val pairs = replacements.map((source, target, arguments) => (source.underlying, target.underlying, arguments.map(_.underlying)))
      val holes = context._1.map(_.underlying) -> context._2.underlying
      prove(conclusion.underlying, premise, comparisons, pairs, holes)
        .mapLeft {
          case error: K.GeneralError => liftGeneralError(name, error)
          case error => Failure(withParams(s"$name: $error", "Conclusion" -> conclusion))
        }
        .lift(conclusion)

    private def assumed(
        conclusion: K.Sequent,
        premise: K.Thm,
        equalities: Seq[(KF.Expression, KF.Expression)],
        context: (Seq[KF.Variable], KF.Expression)
    )(using library: Library): lisa.utils.kernel.Substitution.Result =
      import lisa.utils.kernel.Substitution.{assumeComparison, freshArguments, liftedEqualities}
      given K.Theory = library.theory
      if equalities.exists((s, t) => s.sort != t.sort || (!s.sort.isFunctional && !s.sort.isPredicate)) then Left("Expected matching first-order function or predicate sorts.")
      else
        val assumptions = liftedEqualities(equalities).map(e => conclusion.left.find(_ == e).orElse(conclusion.left.find(KF.isSame(_, e))).getOrElse(e))
        val replacements = equalities
          .zip(assumptions)
          .map:
            case ((s, t), assumption) => (s, t, freshArguments(s, t, assumption.freeVariables))
        val comparisons = replacements
          .zip(assumptions)
          .foldLeft(Right(Vector.empty[K.Thm]): Either[String, Vector[K.Thm]]):
            case (result, (replacement, assumption)) =>
              for
                accumulated <- result
                comparison <- assumeComparison(assumption, replacement)
              yield accumulated :+ comparison
        comparisons.flatMap(proofs => prove(conclusion, premise, proofs, replacements, context).left.map(_.toString))

    /**
     * Derive simultaneous substitution, assuming the lifted equalities on the left.
     */
    def apply(using
        file: sourcecode.File,
        line: sourcecode.Line
    )(using
        library: Library
    )(
        equalities: Seq[(Expr[?], Expr[?])],
        lambdaPhi: (Seq[Variable[?]], Expr[Prop])
    )(premise: K.Thm)(conclusion: Sequent): ProofJudgement =
      val pairs = equalities.map((s, t) => s.underlying -> t.underlying)
      val context = lambdaPhi._1.map(_.underlying) -> lambdaPhi._2.underlying
      lift(assumed(conclusion.underlying, premise, pairs, context), conclusion)

    /**
     * Recover one replacement from a proved equality or lifted pointwise comparison.
     */
    def apply(using
        file: sourcecode.File,
        line: sourcecode.Line
    )(using
        library: Library
    )(
        comparison: Thm,
        context: (Variable[?], Expr[Prop])
    )(premise: K.Thm)(conclusion: Sequent): ProofJudgement =
      val pair = comparison.right.headOption.filter(_ => comparison.right.size == 1).flatMap(f => unliftEquality(f.underlying))
      pair match
        case Some((source, target)) =>
          import lisa.utils.kernel.Substitution.{assumeComparison, freshArguments}
          given K.Theory = library.theory
          val taken = comparison.kernel.left.flatMap(_.freeVariables) ++ comparison.kernel.right.flatMap(_.freeVariables)
          val arguments = freshArguments(source, target, taken)
          val replacement = (source, target, arguments)
          val pointwise =
            if arguments.isEmpty then Right(comparison.kernel)
            else
              for
                bridge <- assumeComparison(comparison.right.head.underlying, replacement)
                instantiated <- K.Cut(K.Sequent(comparison.kernel.left, bridge.right), comparison.kernel, bridge, comparison.right.head.underlying).left.map(_.toString)
              yield instantiated
          val result = pointwise.flatMap(proof => prove(conclusion.underlying, premise, Seq(proof), Seq(replacement), Seq(context._1.underlying) -> context._2.underlying).left.map(_.toString))
          lift(result, conclusion)
        case None => inferenceFailure(s"$name requires a proof of one equality or equivalence.", conclusion)

  object LeftSubst extends SubstTactic(true)
  object RightSubst extends SubstTactic(false)

  val LeftSubstEq: LeftSubst.type = LeftSubst
  val RightSubstEq: RightSubst.type = RightSubst
  val LeftSubstIff: LeftSubst.type = LeftSubst
  val RightSubstIff: RightSubst.type = RightSubst

  object InstSchema:
    private def prove(conclusion: K.Sequent, premise: K.Thm, subst: Map[KF.Variable, KF.Expression])(using library: Library): K.InstSchema.Result[K.Thm] =
      K.InstSchema(using library.theory)(conclusion, premise, subst)

    private def liftError(conclusion: Sequent, premise: K.Thm, subst: Map[Variable[?], Expr[?]])(
        err: K.InstSchema.ErrorType
    ): Failure =
      err match
        case _: K.InstSchema.MissingLeftInstantiation =>
          Failure(withParams("InstSchema conclusion is missing an instantiated left formula.", "Premise" -> premise, "Substitution" -> subst))
        case _: K.InstSchema.MissingRightInstantiation =>
          Failure(withParams("InstSchema conclusion is missing an instantiated right formula.", "Premise" -> premise, "Substitution" -> subst))
        case e: K.GeneralError => liftGeneralError("InstSchema", e)

    def withParameters(using
        file: sourcecode.File,
        line: sourcecode.Line
    )(using
        library: Library
    )(subst: Map[Variable[?], Expr[?]])(
        premise: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      val substK = subst.map { case (v, e) => v.underlying -> e.underlying }
      prove(conclusion.underlying, premise, substK)
        .mapLeft(liftError(conclusion, premise, subst))
        .lift(conclusion)

    def apply(using
        file: sourcecode.File,
        line: sourcecode.Line
    )(using
        library: Library
    )(subst: SubstPair*)(
        premise: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      val builder = Map.newBuilder[Variable[?], Expr[?]]
      subst.foreach(pair => builder += ((pair._1, pair._2)))
      withParameters(using file, line)(builder.result())(premise)(conclusion)
