package lisa.utilcfs.prooflib

import lisa.kernelcf.fol.{FOL => KF}
import lisa.kernelcf.{proof => K}
import lisa.utilcfs.collection.Extensions.{*, given}
import lisa.utilcfs.fol.FOL.*
import lisa.utilcfs.prooflib.Helpers.*
import lisa.utilcfs.prooflib.ProofHelpers.*

object BasicStep:

  ///////////////////////////////////////////////////////////////////////////////
  // Error reporting helpers
  ///////////////////////////////////////////////////////////////////////////////

  case class FrontKernelMismatch(reason: String) extends Exception:
    def msg = s"[FATAL] Front-end and kernel mismatch: $reason"

  case object UnreachableErrorException extends Exception:
    def msg = "[FATAL] This error path should be unreachable."

  private def theoryMismatch(file: sourcecode.File, line: sourcecode.Line)(step: String, expected: K.Theory, actual: K.Theory): ProofError =
    SoftError(withParams(s"$step: premises and conclusion had mismatched underlying theories.", "Expected" -> expected, "Actual" -> actual), file, line)

  private def liftGeneralError(file: sourcecode.File, line: sourcecode.Line)(step: String, err: K.GeneralError): ProofError =
    err match
      case e: K.TheoryMismatch => theoryMismatch(file, line)(step, e.expected, e.actual)
      case e: K.SortMismatch =>
        SoftError(
          withParams(s"$step: an expression has the wrong sort.", "Expected" -> e.expected, "Actual" -> e.actual, "Expression" -> e.expression),
          file,
          line
        )

  private def inferenceFailure(file: sourcecode.File, line: sourcecode.Line)(message: String, conclusion: Sequent, params: (String, Any)*)(using Library): ProofJudgement =
    ProofCarrier(
      Set(SoftError(withParams(message, ("Conclusion", conclusion) +: params*), file, line)),
      conclusion,
      None,
      ()
    )

  ///////////////////////////////////////////////////////////////////////////////
  // Proof construction helpers
  ///////////////////////////////////////////////////////////////////////////////

  private def successful(thm: K.Thm)(using Library): ProofJudgement =
    ProofJudgement(thm)

  /**
    * Weakening helper. Does not handle errors like [[Weakening.apply]].
    * Intended to be used inside tactics for quickly unfolding a kernel
    * weakening step.
    */
  private inline def weakening(conclusion: K.Sequent, premise: K.Thm)(using library: Library): Option[K.Thm] =
    K.Weakening(using library.theory)(conclusion, premise).toOption

  private def localTermCandidates(instance: KF.Expression, variable: KF.Variable): Iterator[KF.Expression] =
    Iterator.single(variable: KF.Expression) ++ termsIn(Seq(instance)).iterator

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
    private def liftError(err: K.Sorry.ErrorType): ProofError = 
      summon[K.Sorry.ErrorType =:= Nothing]
      err

    def apply(using sourcecode.File, sourcecode.Line)(using library: Library)(conclusion: Sequent): ProofJudgement =
      val underlying = conclusion.underlying
      K.Sorry(using library.theory)(underlying)
        .mapLeft(liftError)
        .lift(conclusion)

  object Axiom extends SequentTactic:
    private def liftError(err: K.Axiom.ErrorType): ProofError = 
      summon[K.Axiom.ErrorType =:= Nothing]
      err

    def apply(using sourcecode.File, sourcecode.Line)(using library: Library)(conclusion: Sequent): ProofJudgement =
      val underlying = conclusion.underlying
      K.Axiom(using library.theory)(underlying)
        .mapLeft(liftError)
        .lift(conclusion)

  object Hypothesis extends SequentTactic:
    private def liftError(file: sourcecode.File, line: sourcecode.Line)(conclusion: Sequent, pivot: Expr[Prop])(err: K.Hypothesis.ErrorType): ProofError = 
      err match
        // step-specific errors
        case _: K.Hypothesis.MissingFromLeft =>
          assert(!conclusion.left.containsEq(pivot), s"Pivot $pivot is in the left side of the conclusion $conclusion, despite the kernel reporting it as missing.")
          val base = s"Hypothesis pivot is missing from the left side of the conclusion"
          SoftError(withParams(base, "Pivot" -> pivot, "Conclusion" -> conclusion), file, line)
        case _: K.Hypothesis.MissingFromRight =>
          assert(!conclusion.right.containsEq(pivot), s"Pivot $pivot is in the right side of the conclusion $conclusion, despite the kernel reporting it as missing.")
          val base = s"Hypothesis pivot is missing from the right side of the conclusion"
          SoftError(withParams(base, "Pivot" -> pivot, "Conclusion" -> conclusion), file, line)
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
        .mapLeft(liftError(file, line)(conclusion, pivot))
        .lift(conclusion)
        
    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent): ProofJudgement =
      val pivot =
        // default to syntactic match
        conclusion.left.find(conclusion.right.contains).orElse:
          // try falling back to weaker eq match
          conclusion.left.find(phi => conclusion.right.containsEq(phi))

      pivot match
        case Some(phi) => withParameters(using file, line)(phi)(conclusion)
        case None =>
          val error = SoftError(
            withParams(
              "Could not infer a Hypothesis pivot occurring on both sides of the conclusion.",
              "Conclusion" -> conclusion
            ),
            file,
            line
          )
          ProofCarrier(Set(error), conclusion, None, ())

  object Restate extends SequentTactic, PremiseSequentTactic:
    private def liftError(file: sourcecode.File, line: sourcecode.Line)(conclusion: Sequent, premise: K.Thm)(err: K.Restate.ErrorType): ProofError =
      err match
        case _: K.Restate.NotImplying =>
          SoftError(withParams("Restate premise is not OL-equivalent to the conclusion.", "Premise" -> premise, "Conclusion" -> conclusion), file, line)
        case e: K.GeneralError => liftGeneralError(file, line)("Restate", e)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
      K.Restate(using library.theory)(conclusion.underlying, premise)
        .mapLeft(liftError(file, line)(conclusion, premise))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent): ProofJudgement =
      Tautology(using file, line)(using library)(conclusion)

    def from(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(premise: K.Thm)(conclusion: Sequent): ProofJudgement =
      apply(using file, line)(using library)(conclusion, premise)

  object RestateTrue extends SequentTactic:
    private def liftError(file: sourcecode.File, line: sourcecode.Line)(conclusion: Sequent)(err: K.RestateTrue.ErrorType): ProofError =
      err match
        case _: K.RestateTrue.NotTrivial =>
          SoftError(withParams("RestateTrue conclusion is not OL-equivalent to truth.", "Conclusion" -> conclusion), file, line)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent): ProofJudgement =
      K.RestateTrue(using library.theory)(conclusion.underlying)
        .mapLeft(liftError(file, line)(conclusion))
        .lift(conclusion)

  object Cut:
    private def prove(conclusion: K.Sequent, prem1: K.Thm, prem2: K.Thm, phi: KF.Expression)(using library: Library): K.Cut.Result[K.Thm] =
      K.Cut(using library.theory)(conclusion, prem1, prem2, phi)

    private def liftError(file: sourcecode.File, line: sourcecode.Line)(conclusion: Sequent, prem1: K.Thm, prem2: K.Thm, phi: Expr[Prop])(
        err: K.Cut.ErrorType
    ): ProofError =
      err match
        case _: K.Cut.MissingFromFirst =>
          SoftError(withParams("Cut: LHS of first premise is not contained in the conclusion.", "Premise" -> prem1, "Conclusion" -> conclusion), file, line)
        case _: K.Cut.MissingFromSecond =>
          SoftError(withParams("Cut: RHS of second premise is not contained in the conclusion.", "Premise" -> prem2, "Conclusion" -> conclusion), file, line)
        case _: K.Cut.ExtraneousInFirst =>
          SoftError(withParams("Cut: RHS of first premise contains a formula other than the pivot that is absent from the conclusion.", "Pivot" -> phi, "First premise" -> prem1.statement, "Conclusion" -> conclusion), file, line)
        case _: K.Cut.ExtraneousInSecond =>
          SoftError(withParams("Cut: LHS of second premise contains a formula other than the pivot that is absent from the conclusion.", "Pivot" -> phi, "Second premise" -> prem2.statement, "Conclusion" -> conclusion), file, line)
        case e: K.GeneralError => liftGeneralError(file, line)("Cut", e)

    def withParameters(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(phi: Expr[Prop])(
        prem1: K.Thm,
        prem2: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, prem1, prem2, phi.underlying)
        .mapLeft(liftError(file, line)(conclusion, prem1, prem2, phi))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(prem1: K.Thm, prem2: K.Thm)(
        conclusion: Sequent
    ): ProofJudgement =
      val underlying = conclusion.underlying
      val missing = (differenceEq(prem1.right, underlying.right) ++ differenceEq(prem2.left, underlying.left)).nextOption()
      val inferred =
        missing match
          case Some(phi) => prove(underlying, prem1, prem2, phi).toOption
          case None =>
            prem1.right.iterator.filter(phi => prem2.left.contains(phi) || K.Helpers.containsEq(prem2.left)(phi)).nextOption()
              .flatMap(phi => prove(underlying, prem1, prem2, phi).toOption)

      inferred match
        case Some(thm) => successful(thm)
        case None => inferenceFailure(file, line)("Could not infer the Cut pivot.", conclusion, "First premise" -> prem1, "Second premise" -> prem2)

  object LeftAnd extends PremiseSequentTactic:
    private def prove(conclusion: K.Sequent, premise: K.Thm, phi: KF.Expression, psi: KF.Expression)(using library: Library): K.LeftAnd.Result[K.Thm] =
      K.LeftAnd(using library.theory)(conclusion, premise, phi, psi)

    private def liftError(file: sourcecode.File, line: sourcecode.Line)(conclusion: Sequent, premise: K.Thm, phi: Expr[Prop], psi: Expr[Prop])(
        err: K.LeftAnd.ErrorType
    ): ProofError =
      err match
        case _: K.LeftAnd.MissingFromPremise =>
          SoftError(withParams("LeftAnd: RHS of premise is not contained in the conclusion.", "Premise" -> premise, "Conclusion" -> conclusion), file, line)
        case _: K.LeftAnd.ExtraneousInPremise =>
          SoftError(withParams("LeftAnd: LHS of premise contains a formula other than the provided or inferred conjuncts that is absent from the conclusion.", "Phi" -> phi, "Psi" -> psi, "Premise" -> premise, "Conclusion" -> conclusion), file, line)
        case _: K.LeftAnd.MissingConjunction =>
          SoftError(withParams("LeftAnd: conclusion does not contain the provided conjunction.", "Conjunction" -> (phi /\ psi), "Premise" -> premise, "Conclusion" -> conclusion), file, line)
        case e: K.GeneralError => liftGeneralError(file, line)("LeftAnd", e)

    def withParameters(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(phi: Expr[Prop], psi: Expr[Prop])(
        premise: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, premise, phi.underlying, psi.underlying)
        .mapLeft(liftError(file, line)(conclusion, premise, phi, psi))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
      val underlying = conclusion.underlying

      val inferred = conclusion.left.collectFirstDefined:
        case phi /\ psi =>
          prove(underlying, premise, phi.underlying, psi.underlying).toOption
        case _ => None

      inferred match
        case Some(thm) => successful(thm)
        case None => inferenceFailure(file, line)("Could not infer conjuncts for LeftAnd.", conclusion, "Premise" -> premise)

  object LeftOr:
    private def prove(conclusion: K.Sequent, premises: Seq[K.Thm], disjuncts: Seq[KF.Expression])(using library: Library): K.LeftOr.Result[K.Thm] =
      K.LeftOr(using library.theory)(conclusion, premises, disjuncts)

    private def liftError(file: sourcecode.File, line: sourcecode.Line)(conclusion: Sequent, premises: Seq[K.Thm], disjuncts: Seq[Expr[Prop]])(
        err: K.LeftOr.ErrorType
    ): ProofError =
      err match
        case _: K.LeftOr.EmptyPremises =>
          SoftError("LeftOr: requires at least one premise.", file, line)
        case _: K.LeftOr.ArityMismatch =>
          SoftError(withParams("LeftOr: disjunct and premise counts are mismatched.", "# Premises" -> premises.size, "# Disjuncts" -> disjuncts.size), file, line)
        case e: K.LeftOr.PremiseNotPreserved =>
          SoftError(withParams("LeftOr: a formula in a premise is absent from the conclusion.", "Premise index" -> e.index, "Disjunct" -> disjuncts(e.index)), file, line)
        case _: K.LeftOr.MissingDisjunction =>
          SoftError(withParams("LeftOr: the conclusion does not contain the disjunction.", "Disjuncts" -> disjuncts), file, line)
        case e: K.GeneralError => liftGeneralError(file, line)("LeftOr", e)

    def withParameters(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(disjuncts: Seq[Expr[Prop]])(
        premises: Seq[K.Thm]
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, premises, disjuncts.map(_.underlying))
        .mapLeft(liftError(file, line)(conclusion, premises, disjuncts))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(premises: Seq[K.Thm])(conclusion: Sequent): ProofJudgement =
      val underlying = conclusion.underlying
      if premises.isEmpty then
        inferenceFailure(file, line)("LeftOr: requires at least one premise.", conclusion)
      else
        val extras = premises.map(premise => differenceEq(premise.left, underlying.left).nextOption())
        val inferred =
          if extras.forall(_.nonEmpty) then prove(underlying, premises, extras.flatten).toOption
          else extras.indexWhere(_.isEmpty) match
            case -1 => None
            case i => weakening(underlying, premises(i))

        inferred.fold(inferenceFailure(file, line)("Could not infer disjuncts for LeftOr.", conclusion, "Premises" -> premises))(successful)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(prem1: K.Thm, prem2: K.Thm, rest: K.Thm*)(
        conclusion: Sequent
    ): ProofJudgement =
      apply(using file, line)(using library)(prem1 +: prem2 +: rest)(conclusion)

  object LeftImplies:
    private def prove(conclusion: K.Sequent, prem1: K.Thm, prem2: K.Thm, phi: KF.Expression, psi: KF.Expression)(using
        library: Library
    ): K.LeftImplies.Result[K.Thm] =
      K.LeftImplies(using library.theory)(conclusion, prem1, prem2, phi, psi)

    private def liftError(file: sourcecode.File, line: sourcecode.Line)(conclusion: Sequent, prem1: K.Thm, prem2: K.Thm, phi: Expr[Prop], psi: Expr[Prop])(
        err: K.LeftImplies.ErrorType
    ): ProofError =
      err match
        case _: K.LeftImplies.MissingFromFirst =>
          SoftError(withParams("The first premise left side is not contained in the LeftImplies conclusion.", "Premise" -> prem1), file, line)
        case _: K.LeftImplies.MissingFromSecond =>
          SoftError(withParams("The second premise right side is not contained in the LeftImplies conclusion.", "Premise" -> prem2), file, line)
        case _: K.LeftImplies.ExtraneousInFirst =>
          SoftError(withParams("The first premise right side contains a formula other than the implication antecedent that is absent from the conclusion.", "Antecedent" -> phi), file, line)
        case _: K.LeftImplies.ExtraneousInSecond =>
          SoftError(withParams("The second premise left side contains a formula other than the implication consequent that is absent from the conclusion.", "Consequent" -> psi), file, line)
        case _: K.LeftImplies.MissingImplication =>
          SoftError(withParams("The LeftImplies conclusion does not contain the requested implication.", "Implication" -> implies(phi)(psi)), file, line)
        case e: K.GeneralError => liftGeneralError(file, line)("LeftImplies", e)

    def withParameters(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(phi: Expr[Prop], psi: Expr[Prop])(
        prem1: K.Thm,
        prem2: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, prem1, prem2, phi.underlying, psi.underlying)
        .mapLeft(liftError(file, line)(conclusion, prem1, prem2, phi, psi))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(prem1: K.Thm, prem2: K.Thm)(
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
        case Some(thm) => successful(thm)
        case None => inferenceFailure(file, line)("Could not infer the antecedent and consequent for LeftImplies.", conclusion, "First premise" -> prem1, "Second premise" -> prem2)

  object LeftIff extends PremiseSequentTactic:
    private def prove(conclusion: K.Sequent, premise: K.Thm, phi: KF.Expression, psi: KF.Expression)(using library: Library): K.LeftIff.Result[K.Thm] =
      K.LeftIff(using library.theory)(conclusion, premise, phi, psi)

    private def liftError(file: sourcecode.File, line: sourcecode.Line)(conclusion: Sequent, premise: K.Thm, phi: Expr[Prop], psi: Expr[Prop])(
        err: K.LeftIff.ErrorType
    ): ProofError =
      err match
        case _: K.LeftIff.MissingFromPremise =>
          SoftError(withParams("The premise right side is not contained in the LeftIff conclusion.", "Premise" -> premise), file, line)
        case _: K.LeftIff.ExtraneousInPremise =>
          SoftError(withParams("The premise left side contains a formula other than the two directions of the equivalence that is absent from the conclusion.", "Phi" -> phi, "Psi" -> psi), file, line)
        case _: K.LeftIff.MissingIff =>
          SoftError(withParams("The LeftIff conclusion does not contain the requested equivalence.", "Equivalence" -> iff(phi)(psi)), file, line)
        case e: K.GeneralError => liftGeneralError(file, line)("LeftIff", e)

    def withParameters(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(phi: Expr[Prop], psi: Expr[Prop])(
        premise: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, premise, phi.underlying, psi.underlying)
        .mapLeft(liftError(file, line)(conclusion, premise, phi, psi))
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
        case Some(thm) => successful(thm)
        case None => inferenceFailure(file, line)("Could not infer the equivalent formulas for LeftIff.", conclusion, "Premise" -> premise)

  object LeftNot extends PremiseSequentTactic:
    private def prove(conclusion: K.Sequent, premise: K.Thm, phi: KF.Expression)(using library: Library): K.LeftNot.Result[K.Thm] =
      K.LeftNot(using library.theory)(conclusion, premise, phi)

    private def liftError(file: sourcecode.File, line: sourcecode.Line)(conclusion: Sequent, premise: K.Thm, phi: Expr[Prop])(
        err: K.LeftNot.ErrorType
    ): ProofError =
      err match
        case _: K.LeftNot.MissingFromPremise =>
          SoftError(withParams("The premise left side is not contained in the LeftNot conclusion.", "Premise" -> premise), file, line)
        case _: K.LeftNot.ExtraneousInPremise =>
          SoftError(withParams("The premise right side contains a formula other than the negated formula that is absent from the conclusion.", "Formula" -> phi), file, line)
        case _: K.LeftNot.MissingNegation =>
          SoftError(withParams("The LeftNot conclusion does not contain the requested negation.", "Negation" -> neg(phi)), file, line)
        case e: K.GeneralError => liftGeneralError(file, line)("LeftNot", e)

    def withParameters(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(phi: Expr[Prop])(premise: K.Thm)(
        conclusion: Sequent
    ): ProofJudgement =
      prove(conclusion.underlying, premise, phi.underlying)
        .mapLeft(liftError(file, line)(conclusion, premise, phi))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
      val underlying = conclusion.underlying
      val pivot = differenceEq(premise.right, underlying.right).nextOption()
      val inferred =
        pivot match
          case None => weakening(underlying, premise)
          case Some(phi) => prove(underlying, premise, phi).toOption
      inferred match
        case Some(thm) => successful(thm)
        case None => inferenceFailure(file, line)("Could not infer the negated formula for LeftNot.", conclusion, "Premise" -> premise)

  object LeftForall extends PremiseSequentTactic:
    private def prove(conclusion: K.Sequent, premise: K.Thm, phi: KF.Expression, x: KF.Variable, term: KF.Expression)(using
        library: Library
    ): K.LeftForall.Result[K.Thm] =
      K.LeftForall(using library.theory)(conclusion, premise, phi, x, term)

    private def liftError(file: sourcecode.File, line: sourcecode.Line)(conclusion: Sequent, premise: K.Thm, phi: Expr[Prop], x: Variable[Ind], term: Expr[Ind])(
        err: K.LeftForall.ErrorType
    ): ProofError =
      err match
        case _: K.LeftForall.MissingFromPremise =>
          SoftError(withParams("The premise right side is not contained in the LeftForall conclusion.", "Premise" -> premise), file, line)
        case _: K.LeftForall.ExtraneousInPremise =>
          SoftError(withParams("The premise left side contains a formula other than the quantified instance that is absent from the conclusion.", "Body" -> phi, "Variable" -> x, "Term" -> term), file, line)
        case _: K.LeftForall.MissingForall =>
          SoftError(withParams("The LeftForall conclusion does not contain the requested universal formula.", "Formula" -> forall(x, phi)), file, line)
        case e: K.GeneralError => liftGeneralError(file, line)("LeftForall", e)

    def withParameters(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(phi: Expr[Prop], x: Variable[Ind], term: Expr[Ind])(
        premise: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, premise, phi.underlying, x.underlying, term.underlying)
        .mapLeft(liftError(file, line)(conclusion, premise, phi, x, term))
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
        case Some(thm) => successful(thm)
        case None => inferenceFailure(file, line)("Could not infer the universal formula or its instantiating term for LeftForall.", conclusion, "Premise" -> premise)

  object LeftExists extends PremiseSequentTactic:
    private def prove(conclusion: K.Sequent, premise: K.Thm, phi: KF.Expression, x: KF.Variable)(using library: Library): K.LeftExists.Result[K.Thm] =
      K.LeftExists(using library.theory)(conclusion, premise, phi, x)

    private def liftError(file: sourcecode.File, line: sourcecode.Line)(conclusion: Sequent, premise: K.Thm, phi: Expr[Prop], x: Variable[Ind])(
        err: K.LeftExists.ErrorType
    ): ProofError =
      err match
        case _: K.LeftExists.MissingFromPremise =>
          SoftError(withParams("The premise right side is not contained in the LeftExists conclusion.", "Premise" -> premise), file, line)
        case _: K.LeftExists.ExtraneousInPremise =>
          SoftError(withParams("The premise left side contains a formula other than the existential body that is absent from the conclusion.", "Body" -> phi), file, line)
        case _: K.LeftExists.MissingExists =>
          SoftError(withParams("The LeftExists conclusion does not contain the requested existential formula.", "Formula" -> exists(x, phi)), file, line)
        case _: K.LeftExists.VariableFree =>
          SoftError(withParams("The existential variable is free in the LeftExists conclusion.", "Variable" -> x, "Conclusion" -> conclusion), file, line)
        case e: K.GeneralError => liftGeneralError(file, line)("LeftExists", e)

    def withParameters(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(phi: Expr[Prop], x: Variable[Ind])(
        premise: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, premise, phi.underlying, x.underlying)
        .mapLeft(liftError(file, line)(conclusion, premise, phi, x))
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
            case KF.exists(KF.Lambda(x: KF.Variable, phi)) if K.Helpers.expEq(phi, instance) =>
              prove(underlying, premise, phi, x).toOption
            case _ => None
        case _ => None
      inferred match
        case Some(thm) => successful(thm)
        case None => inferenceFailure(file, line)("Could not infer the existential formula for LeftExists.", conclusion, "Premise" -> premise)

  object RightAnd:
    private def prove(conclusion: K.Sequent, premises: Seq[K.Thm], conjuncts: Seq[KF.Expression])(using library: Library): K.RightAnd.Result[K.Thm] =
      K.RightAnd(using library.theory)(conclusion, premises, conjuncts)

    private def liftError(file: sourcecode.File, line: sourcecode.Line)(conclusion: Sequent, premises: Seq[K.Thm], conjuncts: Seq[Expr[Prop]])(
        err: K.RightAnd.ErrorType
    ): ProofError =
      err match
        case _: K.RightAnd.EmptyPremises =>
          SoftError("RightAnd requires at least one premise.", file, line)
        case _: K.RightAnd.ArityMismatch =>
          SoftError(withParams("RightAnd requires one conjunct per premise.", "Premises" -> premises.size, "Conjuncts" -> conjuncts.size), file, line)
        case e: K.RightAnd.PremiseNotPreserved =>
          SoftError(withParams("A RightAnd premise is not preserved by the conclusion apart from its conjunct.", "Premise index" -> e.index, "Conjunct" -> conjuncts(e.index)), file, line)
        case _: K.RightAnd.MissingConjunction =>
          SoftError(withParams("The RightAnd conclusion does not contain the conjunction.", "Conjuncts" -> conjuncts), file, line)
        case e: K.GeneralError => liftGeneralError(file, line)("RightAnd", e)

    def withParameters(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conjuncts: Seq[Expr[Prop]])(
        premises: Seq[K.Thm]
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, premises, conjuncts.map(_.underlying))
        .mapLeft(liftError(file, line)(conclusion, premises, conjuncts))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(premises: Seq[K.Thm])(conclusion: Sequent): ProofJudgement =
      val underlying = conclusion.underlying
      if premises.isEmpty then
        inferenceFailure(file, line)("RightAnd requires at least one premise.", conclusion)
      else
        val extras = premises.map(premise => differenceEq(premise.right, underlying.right).nextOption())
        val inferred =
          if extras.forall(_.nonEmpty) then prove(underlying, premises, extras.flatten).toOption
          else extras.indexWhere(_.isEmpty) match
            case -1 => None
            case i => weakening(underlying, premises(i))

        inferred.fold(inferenceFailure(file, line)("Could not infer conjuncts for RightAnd.", conclusion, "Premises" -> premises))(successful)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(prem1: K.Thm, prem2: K.Thm, rest: K.Thm*)(
        conclusion: Sequent
    ): ProofJudgement =
      apply(using file, line)(using library)(prem1 +: prem2 +: rest)(conclusion)

  object RightOr extends PremiseSequentTactic:
    private def prove(conclusion: K.Sequent, premise: K.Thm, phi: KF.Expression, psi: KF.Expression)(using library: Library): K.RightOr.Result[K.Thm] =
      K.RightOr(using library.theory)(conclusion, premise, phi, psi)

    private def liftError(file: sourcecode.File, line: sourcecode.Line)(conclusion: Sequent, premise: K.Thm, phi: Expr[Prop], psi: Expr[Prop])(
        err: K.RightOr.ErrorType
    ): ProofError =
      err match
        case _: K.RightOr.MissingFromPremise =>
          SoftError(withParams("The premise left side is not contained in the RightOr conclusion.", "Premise" -> premise, "Conclusion" -> conclusion), file, line)
        case _: K.RightOr.ExtraneousInPremise =>
          SoftError(withParams("The premise right side contains a formula other than the inferred disjuncts that is absent from the conclusion.", "Phi" -> phi, "Psi" -> psi), file, line)
        case _: K.RightOr.MissingDisjunction =>
          SoftError(withParams("The RightOr conclusion does not contain the requested disjunction.", "Disjunction" -> or(phi)(psi)), file, line)
        case e: K.GeneralError => liftGeneralError(file, line)("RightOr", e)

    def withParameters(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(phi: Expr[Prop], psi: Expr[Prop])(
        premise: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, premise, phi.underlying, psi.underlying)
        .mapLeft(liftError(file, line)(conclusion, premise, phi, psi))
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
        case Some(thm) => successful(thm)
        case None => inferenceFailure(file, line)("Could not infer disjuncts for RightOr.", conclusion, "Premise" -> premise)

  object RightImplies extends PremiseSequentTactic:
    private def prove(conclusion: K.Sequent, premise: K.Thm, phi: KF.Expression, psi: KF.Expression)(using library: Library): K.RightImplies.Result[K.Thm] =
      K.RightImplies(using library.theory)(conclusion, premise, phi, psi)

    private def liftError(file: sourcecode.File, line: sourcecode.Line)(conclusion: Sequent, premise: K.Thm, phi: Expr[Prop], psi: Expr[Prop])(
        err: K.RightImplies.ErrorType
    ): ProofError =
      err match
        case _: K.RightImplies.ExtraneousInLeft =>
          SoftError(withParams("The RightImplies premise left side contains a formula other than the antecedent that is absent from the conclusion.", "Antecedent" -> phi), file, line)
        case _: K.RightImplies.ExtraneousInRight =>
          SoftError(withParams("The RightImplies premise right side contains a formula other than the consequent that is absent from the conclusion.", "Consequent" -> psi), file, line)
        case _: K.RightImplies.MissingImplication =>
          SoftError(withParams("The RightImplies conclusion does not contain the requested implication.", "Implication" -> implies(phi)(psi)), file, line)
        case e: K.GeneralError => liftGeneralError(file, line)("RightImplies", e)

    def withParameters(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(phi: Expr[Prop], psi: Expr[Prop])(
        premise: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, premise, phi.underlying, psi.underlying)
        .mapLeft(liftError(file, line)(conclusion, premise, phi, psi))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
      val underlying = conclusion.underlying
      val antecedent = differenceEq(premise.left, underlying.left).nextOption()
      val consequent = differenceEq(premise.right, underlying.right).nextOption()
      val inferred = (antecedent, consequent) match
        case (Some(phi), Some(psi)) => prove(underlying, premise, phi, psi).toOption
        case _ => None

      inferred match
        case Some(thm) => successful(thm)
        case None => inferenceFailure(file, line)("Could not infer the antecedent and consequent for RightImplies.", conclusion, "Premise" -> premise)

  object RightIff:
    private def prove(conclusion: K.Sequent, prem1: K.Thm, prem2: K.Thm, phi: KF.Expression, psi: KF.Expression)(using
        library: Library
    ): K.RightIff.Result[K.Thm] =
      K.RightIff(using library.theory)(conclusion, prem1, prem2, phi, psi)

    private def liftError(file: sourcecode.File, line: sourcecode.Line)(conclusion: Sequent, prem1: K.Thm, prem2: K.Thm, phi: Expr[Prop], psi: Expr[Prop])(
        err: K.RightIff.ErrorType
    ): ProofError =
      err match
        case _: K.RightIff.MissingFromFirst =>
          SoftError(withParams("The first RightIff premise left side is not contained in the conclusion.", "Premise" -> prem1), file, line)
        case _: K.RightIff.MissingFromSecond =>
          SoftError(withParams("The second RightIff premise left side is not contained in the conclusion.", "Premise" -> prem2), file, line)
        case _: K.RightIff.ExtraneousInFirst =>
          SoftError(withParams("The first RightIff premise right side contains a formula other than the forward implication.", "Forward implication" -> implies(phi)(psi)), file, line)
        case _: K.RightIff.ExtraneousInSecond =>
          SoftError(withParams("The second RightIff premise right side contains a formula other than the backward implication.", "Backward implication" -> implies(psi)(phi)), file, line)
        case _: K.RightIff.MissingIff =>
          SoftError(withParams("The RightIff conclusion does not contain the requested equivalence.", "Equivalence" -> iff(phi)(psi)), file, line)
        case e: K.GeneralError => liftGeneralError(file, line)("RightIff", e)

    def withParameters(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(phi: Expr[Prop], psi: Expr[Prop])(
        prem1: K.Thm,
        prem2: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, prem1, prem2, phi.underlying, psi.underlying)
        .mapLeft(liftError(file, line)(conclusion, prem1, prem2, phi, psi))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(prem1: K.Thm, prem2: K.Thm)(
        conclusion: Sequent
    ): ProofJudgement =
      val underlying = conclusion.underlying
      val pivot = differenceEq(prem1.right, underlying.right).nextOption()
      val inferred = pivot match
        case Some(KF.implies(phi, psi)) => prove(underlying, prem1, prem2, phi, psi).toOption
        case None => weakening(underlying, prem1)
        case _ => None
      inferred match
        case Some(thm) => successful(thm)
        case None => inferenceFailure(file, line)("Could not infer the equivalent formulas for RightIff.", conclusion, "First premise" -> prem1, "Second premise" -> prem2)

  object RightNot extends PremiseSequentTactic:
    private def prove(conclusion: K.Sequent, premise: K.Thm, phi: KF.Expression)(using library: Library): K.RightNot.Result[K.Thm] =
      K.RightNot(using library.theory)(conclusion, premise, phi)

    private def liftError(file: sourcecode.File, line: sourcecode.Line)(conclusion: Sequent, premise: K.Thm, phi: Expr[Prop])(
        err: K.RightNot.ErrorType
    ): ProofError =
      err match
        case _: K.RightNot.MissingFromPremise =>
          SoftError(withParams("The premise right side is not contained in the RightNot conclusion.", "Premise" -> premise), file, line)
        case _: K.RightNot.ExtraneousInPremise =>
          SoftError(withParams("The premise left side contains a formula other than the negated formula that is absent from the conclusion.", "Formula" -> phi), file, line)
        case _: K.RightNot.MissingNegation =>
          SoftError(withParams("The RightNot conclusion does not contain the requested negation.", "Negation" -> neg(phi)), file, line)
        case e: K.GeneralError => liftGeneralError(file, line)("RightNot", e)

    def withParameters(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(phi: Expr[Prop])(premise: K.Thm)(
        conclusion: Sequent
    ): ProofJudgement =
      prove(conclusion.underlying, premise, phi.underlying)
        .mapLeft(liftError(file, line)(conclusion, premise, phi))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
      val underlying = conclusion.underlying
      val pivot = differenceEq(premise.left, underlying.left).nextOption()
      val inferred =
        pivot match
          case None => weakening(underlying, premise)
          case Some(phi) => prove(underlying, premise, phi).toOption
      inferred match
        case Some(thm) => successful(thm)
        case None => inferenceFailure(file, line)("Could not infer the negated formula for RightNot.", conclusion, "Premise" -> premise)

  object RightForall extends PremiseSequentTactic:
    private def prove(conclusion: K.Sequent, premise: K.Thm, phi: KF.Expression, x: KF.Variable)(using library: Library): K.RightForall.Result[K.Thm] =
      K.RightForall(using library.theory)(conclusion, premise, phi, x)

    private def liftError(file: sourcecode.File, line: sourcecode.Line)(conclusion: Sequent, premise: K.Thm, phi: Expr[Prop], x: Variable[Ind])(
        err: K.RightForall.ErrorType
    ): ProofError =
      err match
        case _: K.RightForall.MissingFromPremise =>
          SoftError(withParams("The premise left side is not contained in the RightForall conclusion.", "Premise" -> premise), file, line)
        case _: K.RightForall.ExtraneousInPremise =>
          SoftError(withParams("The premise right side contains a formula other than the universal body that is absent from the conclusion.", "Body" -> phi), file, line)
        case _: K.RightForall.MissingForall =>
          SoftError(withParams("The RightForall conclusion does not contain the requested universal formula.", "Formula" -> forall(x, phi)), file, line)
        case _: K.RightForall.VariableFree =>
          SoftError(withParams("The universal variable is free in the RightForall conclusion.", "Variable" -> x, "Conclusion" -> conclusion), file, line)
        case e: K.GeneralError => liftGeneralError(file, line)("RightForall", e)

    def withParameters(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(phi: Expr[Prop], x: Variable[Ind])(
        premise: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, premise, phi.underlying, x.underlying)
        .mapLeft(liftError(file, line)(conclusion, premise, phi, x))
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
            case KF.forall(KF.Lambda(x: KF.Variable, phi)) if K.Helpers.expEq(phi, instance) =>
              prove(underlying, premise, phi, x).toOption
            case _ => None
        case _ => None
      inferred match
        case Some(thm) => successful(thm)
        case None => inferenceFailure(file, line)("Could not infer the universal formula for RightForall.", conclusion, "Premise" -> premise)

  object RightExists extends PremiseSequentTactic:
    private def prove(conclusion: K.Sequent, premise: K.Thm, phi: KF.Expression, x: KF.Variable, term: KF.Expression)(using
        library: Library
    ): K.RightExists.Result[K.Thm] =
      K.RightExists(using library.theory)(conclusion, premise, phi, x, term)

    private def liftError(file: sourcecode.File, line: sourcecode.Line)(conclusion: Sequent, premise: K.Thm, phi: Expr[Prop], x: Variable[Ind], term: Expr[Ind])(
        err: K.RightExists.ErrorType
    ): ProofError =
      err match
        case _: K.RightExists.MissingFromPremise =>
          SoftError(withParams("The premise left side is not contained in the RightExists conclusion.", "Premise" -> premise), file, line)
        case _: K.RightExists.ExtraneousInPremise =>
          SoftError(withParams("The premise right side contains a formula other than the existential instance that is absent from the conclusion.", "Body" -> phi, "Variable" -> x, "Term" -> term), file, line)
        case _: K.RightExists.MissingExists =>
          SoftError(withParams("The RightExists conclusion does not contain the requested existential formula.", "Formula" -> exists(x, phi)), file, line)
        case e: K.GeneralError => liftGeneralError(file, line)("RightExists", e)

    def withParameters(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(phi: Expr[Prop], x: Variable[Ind], term: Expr[Ind])(
        premise: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, premise, phi.underlying, x.underlying, term.underlying)
        .mapLeft(liftError(file, line)(conclusion, premise, phi, x, term))
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
        case Some(thm) => successful(thm)
        case None => inferenceFailure(file, line)("Could not infer the existential formula or its instantiating term for RightExists.", conclusion, "Premise" -> premise)

  object RightEpsilon extends PremiseSequentTactic:
    private def prove(conclusion: K.Sequent, premise: K.Thm, phi: KF.Expression, x: KF.Variable, term: KF.Expression)(using
        library: Library
    ): K.RightEpsilon.Result[K.Thm] =
      K.RightEpsilon(using library.theory)(conclusion, premise, phi, x, term)

    private def liftError(file: sourcecode.File, line: sourcecode.Line)(conclusion: Sequent, premise: K.Thm, phi: Expr[Prop], x: Variable[Ind], term: Expr[Ind])(
        err: K.RightEpsilon.ErrorType
    ): ProofError =
      err match
        case _: K.RightEpsilon.MissingFromPremise =>
          SoftError(withParams("The premise left side is not contained in the RightEpsilon conclusion.", "Premise" -> premise), file, line)
        case _: K.RightEpsilon.ExtraneousInPremise =>
          SoftError(withParams("The premise right side contains a formula other than the epsilon source instance that is absent from the conclusion.", "Body" -> phi, "Variable" -> x, "Term" -> term), file, line)
        case _: K.RightEpsilon.MissingEpsilonInstance =>
          SoftError(withParams("The RightEpsilon conclusion does not contain the epsilon instance.", "Body" -> phi, "Variable" -> x), file, line)
        case e: K.GeneralError => liftGeneralError(file, line)("RightEpsilon", e)

    def withParameters(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(phi: Expr[Prop], x: Variable[Ind], term: Expr[Ind])(
        premise: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, premise, phi.underlying, x.underlying, term.underlying)
        .mapLeft(liftError(file, line)(conclusion, premise, phi, x, term))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
      val underlying = conclusion.underlying
      val source = differenceEq(premise.right, underlying.right).nextOption()
      val target = differenceEq(underlying.right, premise.right).nextOption()
      val inferred = (source, target) match
        case (Some(instance), Some(result)) =>
          Helpers.subexpressions(Seq(result)).collectFirstDefined:
            case KF.epsilon(KF.Lambda(x: KF.Variable, phi)) =>
              localTermCandidates(instance, x).collectFirstDefined(term => prove(underlying, premise, phi, x, term).toOption)
            case _ => None
        case _ => None
      inferred match
        case Some(thm) => successful(thm)
        case None => inferenceFailure(file, line)("Could not infer the epsilon formula or source term for RightEpsilon.", conclusion, "Premise" -> premise)

  object Weakening extends PremiseSequentTactic:
    private def liftError(file: sourcecode.File, line: sourcecode.Line)(conclusion: Sequent, premise: K.Thm)(err: K.Weakening.ErrorType): ProofError =
      err match
        case _: K.Weakening.NotImplying =>
          SoftError(withParams("Weakening premise does not imply the conclusion.", "Premise" -> premise, "Conclusion" -> conclusion), file, line)
        case e: K.GeneralError => liftGeneralError(file, line)("Weakening", e)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
      K.Weakening(using library.theory)(conclusion.underlying, premise)
        .mapLeft(liftError(file, line)(conclusion, premise))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(premise: K.Thm)(conclusion: Sequent): ProofJudgement =
      apply(using file, line)(using library)(conclusion, premise)

  object LeftRefl extends PremiseSequentTactic:
    private def prove(conclusion: K.Sequent, premise: K.Thm, equality: KF.Expression)(using library: Library): K.LeftRefl.Result[K.Thm] =
      K.LeftRefl(using library.theory)(conclusion, premise, equality)

    private def liftError(file: sourcecode.File, line: sourcecode.Line)(conclusion: Sequent, premise: K.Thm, equality: Any)(err: K.LeftRefl.ErrorType): ProofError =
      err match
        case _: K.LeftRefl.NotAnEquality =>
          SoftError(withParams("LeftRefl parameter is not an equality.", "Expression" -> equality), file, line)
        case _: K.LeftRefl.EqualityNotReflexive =>
          SoftError(withParams("LeftRefl equality is not reflexive up to the active equality.", "Equality" -> equality), file, line)
        case _: K.LeftRefl.MissingFromPremise =>
          SoftError(withParams("The premise right side is not contained in the LeftRefl conclusion.", "Premise" -> premise), file, line)
        case _: K.LeftRefl.ExtraneousInPremise =>
          SoftError(withParams("The premise left side contains a formula other than the reflexive equality that is absent from the conclusion.", "Equality" -> equality), file, line)
        case e: K.GeneralError => liftGeneralError(file, line)("LeftRefl", e)

    def withParameters(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(equality: Expr[Prop])(
        premise: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      prove(conclusion.underlying, premise, equality.underlying)
        .mapLeft(liftError(file, line)(conclusion, premise, equality))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
      val underlying = conclusion.underlying
      differenceEq(premise.left, underlying.left).nextOption().flatMap(eq => prove(underlying, premise, eq).toOption) match
        case Some(thm) => successful(thm)
        case None => inferenceFailure(file, line)("Could not infer a reflexive equality for LeftRefl.", conclusion, "Premise" -> premise)

  object RightRefl extends SequentTactic:
    private def prove(conclusion: K.Sequent, equality: KF.Expression)(using library: Library): K.RightRefl.Result[K.Thm] =
      K.RightRefl(using library.theory)(conclusion, equality)

    private def liftError(file: sourcecode.File, line: sourcecode.Line)(conclusion: Sequent, equality: Any)(err: K.RightRefl.ErrorType): ProofError =
      err match
        case _: K.RightRefl.NotAnEquality =>
          SoftError(withParams("RightRefl parameter is not an equality.", "Expression" -> equality), file, line)
        case _: K.RightRefl.EqualityNotReflexive =>
          SoftError(withParams("RightRefl equality is not reflexive up to the active equality.", "Equality" -> equality), file, line)
        case _: K.RightRefl.MissingEquality =>
          SoftError(withParams("The RightRefl conclusion does not contain the requested equality.", "Equality" -> equality), file, line)
        case e: K.GeneralError => liftGeneralError(file, line)("RightRefl", e)

    def withParameters(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(equality: Expr[Prop])(
        conclusion: Sequent
    ): ProofJudgement =
      prove(conclusion.underlying, equality.underlying)
        .mapLeft(liftError(file, line)(conclusion, equality))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent): ProofJudgement =
      val underlying = conclusion.underlying
      val candidates = underlying.right.iterator.collect:
        case eq @ KF.equality(_, _) => eq
      val inferred = candidates.collectFirstDefined(eq => prove(underlying, eq).toOption)
      inferred.fold(inferenceFailure(file, line)("Could not infer a reflexive equality for RightRefl.", conclusion))(successful)

  object LeftSubstEq extends PremiseSequentTactic:
    private def prove(conclusion: K.Sequent, premise: K.Thm, equalities: Seq[(KF.Expression, KF.Expression)], lambdaPhi: (Seq[KF.Variable], KF.Expression))(using
        library: Library
    ): K.LeftSubstEq.Result[K.Thm] =
      K.LeftSubstEq(using library.theory)(conclusion, premise, equalities, lambdaPhi)

    private def liftError(file: sourcecode.File, line: sourcecode.Line)(
        conclusion: Sequent,
        premise: K.Thm,
        equalities: Seq[(Expr[?], Expr[?])],
        lambdaPhi: (Seq[Variable[?]], Expr[Prop])
    )(err: K.LeftSubstEq.ErrorType): ProofError =
      err match
        case _: K.LeftSubstEq.ArityMismatch =>
          SoftError(withParams("LeftSubstEq equality count does not match lambda argument count.", "Equalities" -> equalities, "Lambda" -> lambdaPhi), file, line)
        case _: K.LeftSubstEq.SubstitutionSortNotAllowed =>
          SoftError(withParams("LeftSubstEq lambda argument sort is not substitutable.", "Lambda" -> lambdaPhi), file, line)
        case _: K.LeftSubstEq.MissingFromPremise =>
          SoftError(withParams("The premise right side is not contained in the LeftSubstEq conclusion.", "Premise" -> premise), file, line)
        case _: K.LeftSubstEq.ExtraneousInPremise =>
          SoftError(withParams("The premise left side contains a formula other than φ(s) that is absent from the conclusion.", "Equalities" -> equalities, "Lambda" -> lambdaPhi), file, line)
        case _: K.LeftSubstEq.MissingLiftedEquality =>
          SoftError(withParams("The LeftSubstEq conclusion is missing a lifted equality.", "Equalities" -> equalities), file, line)
        case _: K.LeftSubstEq.MissingSubstitutedFormula =>
          SoftError(withParams("The LeftSubstEq conclusion is missing φ(t).", "Equalities" -> equalities, "Lambda" -> lambdaPhi), file, line)
        case e: K.GeneralError => liftGeneralError(file, line)("LeftSubstEq", e)

    def withParameters(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(
        equalities: Seq[(Expr[?], Expr[?])],
        lambdaPhi: (Seq[Variable[?]], Expr[Prop])
    )(premise: K.Thm)(conclusion: Sequent): ProofJudgement =
      val equalitiesK = equalities.map { case (s, t) => s.underlying -> t.underlying }
      val lambdaPhiK = (lambdaPhi._1.map(_.underlying), lambdaPhi._2.underlying)
      prove(conclusion.underlying, premise, equalitiesK, lambdaPhiK)
        .mapLeft(liftError(file, line)(conclusion, premise, equalities, lambdaPhi))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
      val underlying = conclusion.underlying
      val candidates = singleSubstEqCandidates(
        differenceEq(premise.left, underlying.left),
        differenceEq(underlying.left, premise.left),
        underlying.left
      )
      val inferred = candidates.collectFirstDefined { case (equalities, lambdaPhi) =>
        prove(underlying, premise, equalities, lambdaPhi).toOption
      }

      inferred match
        case Some(thm) => successful(thm)
        case None => inferenceFailure(file, line)("Could not infer LeftSubstEq equalities and lambda parameters.", conclusion, "Premise" -> premise)

  object RightSubstEq extends PremiseSequentTactic:
    private def prove(conclusion: K.Sequent, premise: K.Thm, equalities: Seq[(KF.Expression, KF.Expression)], lambdaPhi: (Seq[KF.Variable], KF.Expression))(using
        library: Library
    ): K.RightSubstEq.Result[K.Thm] =
      K.RightSubstEq(using library.theory)(conclusion, premise, equalities, lambdaPhi)

    private def liftError(file: sourcecode.File, line: sourcecode.Line)(
        conclusion: Sequent,
        premise: K.Thm,
        equalities: Seq[(Expr[?], Expr[?])],
        lambdaPhi: (Seq[Variable[?]], Expr[Prop])
    )(err: K.RightSubstEq.ErrorType): ProofError =
      err match
        case _: K.RightSubstEq.ArityMismatch =>
          SoftError(withParams("RightSubstEq equality count does not match lambda argument count.", "Equalities" -> equalities, "Lambda" -> lambdaPhi), file, line)
        case _: K.RightSubstEq.SubstitutionSortNotAllowed =>
          SoftError(withParams("RightSubstEq lambda argument sort is not substitutable.", "Lambda" -> lambdaPhi), file, line)
        case _: K.RightSubstEq.MissingFromPremise =>
          SoftError(withParams("The premise left side is not contained in the RightSubstEq conclusion.", "Premise" -> premise), file, line)
        case _: K.RightSubstEq.MissingLiftedEquality =>
          SoftError(withParams("The RightSubstEq conclusion is missing a lifted equality.", "Equalities" -> equalities), file, line)
        case _: K.RightSubstEq.ExtraneousInPremise =>
          SoftError(withParams("The premise right side contains a formula other than φ(s) that is absent from the conclusion.", "Equalities" -> equalities, "Lambda" -> lambdaPhi), file, line)
        case _: K.RightSubstEq.MissingSubstitutedFormula =>
          SoftError(withParams("The RightSubstEq conclusion is missing φ(t).", "Equalities" -> equalities, "Lambda" -> lambdaPhi), file, line)
        case e: K.GeneralError => liftGeneralError(file, line)("RightSubstEq", e)

    def withParameters(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(
        equalities: Seq[(Expr[?], Expr[?])],
        lambdaPhi: (Seq[Variable[?]], Expr[Prop])
    )(premise: K.Thm)(conclusion: Sequent): ProofJudgement =
      val equalitiesK = equalities.map { case (s, t) => s.underlying -> t.underlying }
      val lambdaPhiK = (lambdaPhi._1.map(_.underlying), lambdaPhi._2.underlying)
      prove(conclusion.underlying, premise, equalitiesK, lambdaPhiK)
        .mapLeft(liftError(file, line)(conclusion, premise, equalities, lambdaPhi))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
      val underlying = conclusion.underlying
      val candidates = singleSubstEqCandidates(
        differenceEq(premise.right, underlying.right),
        differenceEq(underlying.right, premise.right),
        underlying.left
      )
      val inferred = candidates.collectFirstDefined { case (equalities, lambdaPhi) =>
        prove(underlying, premise, equalities, lambdaPhi).toOption
      }

      inferred match
        case Some(thm) => successful(thm)
        case None => inferenceFailure(file, line)("Could not infer RightSubstEq equalities and lambda parameters.", conclusion, "Premise" -> premise)

  val LeftSubstIff: LeftSubstEq.type = LeftSubstEq
  val RightSubstIff: RightSubstEq.type = RightSubstEq

  object InstSchema:
    private def prove(conclusion: K.Sequent, premise: K.Thm, subst: Map[KF.Variable, KF.Expression])(using library: Library): K.InstSchema.Result[K.Thm] =
      K.InstSchema(using library.theory)(conclusion, premise, subst)

    private def liftError(file: sourcecode.File, line: sourcecode.Line)(conclusion: Sequent, premise: K.Thm, subst: Map[Variable[?], Expr[?]])(
        err: K.InstSchema.ErrorType
    ): ProofError =
      err match
        case _: K.InstSchema.MissingLeftInstantiation =>
          SoftError(withParams("InstSchema conclusion is missing an instantiated left formula.", "Premise" -> premise, "Substitution" -> subst), file, line)
        case _: K.InstSchema.MissingRightInstantiation =>
          SoftError(withParams("InstSchema conclusion is missing an instantiated right formula.", "Premise" -> premise, "Substitution" -> subst), file, line)
        case e: K.GeneralError => liftGeneralError(file, line)("InstSchema", e)

    def withParameters(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(subst: Map[Variable[?], Expr[?]])(
        premise: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      val substK = subst.map { case (v, e) => v.underlying -> e.underlying }
      prove(conclusion.underlying, premise, substK)
        .mapLeft(liftError(file, line)(conclusion, premise, subst))
        .lift(conclusion)

    def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(subst: SubstPair*)(
        premise: K.Thm
    )(conclusion: Sequent): ProofJudgement =
      val builder = Map.newBuilder[Variable[?], Expr[?]]
      subst.foreach(pair => builder += ((pair._1, pair._2)))
      withParameters(using file, line)(builder.result())(premise)(conclusion)
