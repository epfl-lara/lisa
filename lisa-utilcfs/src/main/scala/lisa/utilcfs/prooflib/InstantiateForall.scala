package lisa.utilcfs.prooflib

import lisa.utilcfs.fol.FOL.*
import lisa.utilcfs.prooflib.Helpers.*
import lisa.utilcfs.prooflib.ProofHelpers.{PremiseSequentTactic, SequentTactic}

/**
 * Instantiate universal quantifier.
 *
 * The premise is a proof of φ, with φ of the form ∀x.ψ.
 *
 * t is the term to instantiate the quantifier with.
 *
 * <pre>
 * Γ ⊢ ∀x.ψ, Δ
 * -------------------------
 * Γ |- ψ[t/x], Δ
 * </pre>
 *
 * Returns a proof containing the instantiation steps.
 */
object InstantiateForall extends SequentTactic, PremiseSequentTactic, DerivedFromPremises:
  private def instantiate(formula: Expr[Prop], term: Expr[?]): Option[(Expr[Prop], Variable[Ind], Expr[Ind])] =
    (formula, term) match
      case (forall(x, inner), t: Expr[Ind] @unchecked) => Some((inner, x, t))
      case _ => None

  private def invalid(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, message: String): ProofJudgement =
    ProofCarrier(Set(SoftError(message, file, line)), conclusion, None, ())

  private def instantiateOnce(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(
      target: Sequent,
      premise: Thm,
      formula: Expr[Prop],
      term: Expr[?]
  ): ProofJudgement =
    instantiate(formula, term) match
      case None =>
        invalid(target, "Input formula is not universally quantified, or the term is not individual-sorted.")
      case Some((body, x, t)) =>
        val instance = body.substitute(x := t)
        val bridge = formula |- instance

        /**
         * instance = ψ[t/x]
         *
         * s1     = Γ ⊢ ∀x.ψ, Δ        Premise
         * target = Γ ⊢ ψ[t/x], Δ      Result
         *
         * p0     = ψ[t/x] ⊢ ψ[t/x]    Hypothesis
         * p1     = ∀x.ψ ⊢ ψ[t/x]      LeftForall p0
         * p2     = Γ ⊢ ψ[t/x], Δ      Cut s1, p1
         */
        val p0 = BasicStep.Hypothesis(instance |- instance)
        if !p0.isValid then p0
        else
          val p1 = BasicStep.LeftForall.withParameters(body, x, t)(p0.destruct._1.kernel)(bridge)
          if !p1.isValid then p1
          else
            val cutTarget = Sequent(premise.left, (premise.right - formula) + instance)
            val p2 = BasicStep.Cut.withParameters(formula)(premise.kernel, p1.destruct._1.kernel)(cutTarget)
            if !p2.isValid || cutTarget == target then p2
            else BasicStep.Weakening(target, p2.destruct._1.kernel)

  private def forallFormulas(statement: Sequent): Set[Expr[Prop]] =
    statement.right.collect { case f @ forall(_, _) => f }

  private def inferredInstances(using library: Library)(conclusion: Sequent, premise: Thm, formula: Expr[Prop])(using sourcecode.File, sourcecode.Line): Iterator[ProofJudgement] =
    formula match
      case forall(x, _) =>
        val candidates = (conclusion.right.iterator ++ conclusion.left.iterator)
          .flatMap(target => localTermCandidates(target.underlying, x.underlying))
        candidates.map(term => instantiateOnce(conclusion, premise, formula, liftExpression(term).asInstanceOf[Expr[Ind]]))
      case _ => Iterator.empty

  def prove(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premises: Seq[Thm]): ProofJudgement =
    premises match
      case Seq(premise, _*) =>
        forallFormulas(premise.statement).iterator
          .flatMap(formula => inferredInstances(conclusion, premise, formula))
          .find(_.isValid)
          .getOrElse(invalid(conclusion, "Could not infer a universal instantiation."))
      case _ =>
        invalid(conclusion, "InstantiateForall requires a premise.")

  final class WithFormula(formula: Expr[Prop], terms: Seq[Expr[?]])(using file: sourcecode.File, line: sourcecode.Line, library: Library) extends ((Sequent, Thm) => ProofJudgement):
    def apply(premise: Thm): Sequent => ProofJudgement =
      conclusion => apply(conclusion, premise)

    def apply(conclusion: Sequent, premise: Thm): ProofJudgement =
      instantiateTerms(conclusion, premise, Some(formula), terms)

  final class WithTerms(terms: Seq[Expr[?]])(using file: sourcecode.File, line: sourcecode.Line, library: Library) extends ((Sequent, Thm) => ProofJudgement):
    def apply(premise: Thm): Sequent => ProofJudgement =
      conclusion => apply(conclusion, premise)

    def apply(premises: Thm*): Sequent => ProofJudgement =
      conclusion => InstantiateForall.prove(conclusion, premises)

    def apply(conclusion: Sequent, premise: Thm): ProofJudgement =
      instantiateTerms(conclusion, premise, None, terms)

  private def instantiateTerms(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(
      conclusion: Sequent,
      premise: Thm,
      requestedFormula: Option[Expr[Prop]],
      terms: Seq[Expr[?]]
  ): ProofJudgement =
    if terms.isEmpty then InstantiateForall.prove(conclusion, Seq(premise))
    else
      var current = premise
      var currentFormula = requestedFormula
      var failure: Option[ProofJudgement] = None
      val iterator = terms.iterator
      while iterator.hasNext && failure.isEmpty do
        val term = iterator.next()
        val formulas = currentFormula.filter(current.statement.right.containsEq).map(Set(_)).getOrElse(forallFormulas(current.statement))
        val target =
          if iterator.hasNext then
            formulas.headOption
              .flatMap(instantiate(_, term).map((body, x, t) => (current.statement ->> forall(x, body)) +>> body.substitute(x := t)))
              .getOrElse(conclusion)
          else conclusion
        formulas.iterator
          .map(formula => instantiateOnce(target, current, formula, term))
          .find(_.isValid) match
          case Some(judgement) =>
            current = judgement.destruct._1
            currentFormula = None
          case None =>
            failure = Some(invalid(conclusion, "Could not instantiate the requested universal formula."))
      failure.getOrElse(BasicStep.Restate(conclusion, current.kernel))

  def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(formula: Expr[Prop], terms: Expr[?]*): WithFormula =
    WithFormula(formula, terms)

  def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(terms: Expr[?]*): WithTerms =
    WithTerms(terms)
