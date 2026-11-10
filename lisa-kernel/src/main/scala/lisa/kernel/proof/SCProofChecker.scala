package lisa.kernel.proof

import lisa.kernel.fol.FOL._
import lisa.kernel.proof.SCProofCheckerJudgement._
import lisa.kernel.proof.SequentCalculus._

object SCProofChecker {

  /**
   * The chosen equality for general checks in proof steps.
   *
   * Syntactic equality is expected to be sound, but strong algorithms
   * are fine and increase the expressiveness of steps.
   */
  @inline
  private def expEq(s: Expression, t: Expression): Boolean =
    // s == t // syntactic eq
    isSame(s, t) // OL eq
    // or some other weaker eq...

  /**
   * Checks whether a formula is contained in a set wrt either syntactic or
   * expEq equality.
   */
  @inline
  private def containsEq(set: Set[Expression], formula: Expression): Boolean =
    set.contains(formula) || set.exists(expEq(_, formula))

  @inline
  private def containsAsSimple(set: Set[SimpleExpression])(expr: Expression): Boolean =
    set.contains(simpleReducedForm(expr))

  /**
   * Chosen subset check for sets of formulas. Can be weakeened to allow more
   * than syntactic equality.
   */
  @inline
  private def subset(subset: Set[Expression], superset: Set[Expression]): Boolean =
    subset.subsetOf(superset) || subset.forall(containsAsSimple(superset.map(simpleReducedForm)))

  /**
   * Checks whether `set` is contained in `target` *syntactically*  except for
   * removing a formula `expEq` to `exception``.
   */
  @inline
  private def allContainedExcept(set: Set[Expression], target: Set[Expression], exception: Expression): Boolean = {
    lazy val simplifiedTarget = target.map(simpleReducedForm)
    set.forall(formula => target.contains(formula) || formula == exception || containsAsSimple(simplifiedTarget)(formula) || expEq(formula, exception))
  }

  /**
   * Checks whether `set` is contained in `target` *syntactically* except for
   * removing formulas `expEq` to `exception1` or `exception2`.
   */
  @inline
  private def allContainedExceptEither(set: Set[Expression], target: Set[Expression], exception1: Expression, exception2: Expression): Boolean = {
    val simplifiedTarget = target.map(simpleReducedForm)
    set.forall(formula => containsAsSimple(simplifiedTarget)(formula) || expEq(formula, exception1) || expEq(formula, exception2))
  }

  private def sortMismatch(
      expected: Sort,
      actual: Sort,
      step: SCProofStep
  ): SCInvalidProof = {
    val expectedString = expected match {
      case Prop => "a formula (of sort Prop)"
      case Ind => "a term (of sort Ind)"
      case s => s"an expression of sort ($s)"
    }
    SCInvalidProof(SCProof(step), Nil, s"Expected $expectedString, but found sort ($actual).")
  }

  private def error(step: SCProofStep, message: String): SCInvalidProof = {
    SCInvalidProof(SCProof(step), Nil, message)
  }

  private def variableIsFreeInSequent(sequent: Sequent, variable: Variable): Boolean = {
    sequent.left.exists(_.freeVariables.contains(variable)) || sequent.right.exists(_.freeVariables.contains(variable))
  }

  private def argumentSorts(sort: Sort): List[Sort] = sort match {
    case Arrow(from, to) => from :: argumentSorts(to)
    case _ => Nil
  }

  private def checkDerivedSubstitution(step: SCProofStep, derived: Either[String, SCProof]): SCProofCheckerJudgement = derived match {
    case Left(message) => error(step, message)
    case Right(proof) => checkSCProof(proof) match {
      case SCInvalidProof(_, _, message) => error(step, message)
      case SCValidProof(_, usesSorry) => SCValidProof(SCProof(step), usesSorry)
    }
  }

  private def checkComparison(
      step: SCProofStep,
      statement: Sequent,
      comparison: Sequent,
      replacement: (Expression, Expression, Seq[Variable]),
      variable: Variable
  ): Option[SCInvalidProof] = {
    val (source, target, arguments) = replacement
    if (source.sort != variable.sort) Some(sortMismatch(variable.sort, source.sort, step))
    else if (target.sort != variable.sort) Some(sortMismatch(variable.sort, target.sort, step))
    else if (arguments.map(_.sort) != argumentSorts(variable.sort)) Some(error(step, "Comparison arguments have incorrect sorts or arity."))
    else if (arguments.toSet.size != arguments.size) Some(error(step, "Comparison arguments must be distinct."))
    else {
      val appliedSource = arguments.foldLeft(source: Expression)(_(_))
      val appliedTarget = arguments.foldLeft(target: Expression)(_(_))
      val equation = if (appliedSource.sort == Prop) iff(appliedSource)(appliedTarget) else equality(appliedSource)(appliedTarget)
      val residual = comparison.right - equation
      val notFresh = arguments.exists(v =>
        source.freeVariables.contains(v) || target.freeVariables.contains(v) ||
          comparison.left.exists(_.freeVariables.contains(v)) || residual.exists(_.freeVariables.contains(v))
      )
      if (notFresh) Some(error(step, "Comparison arguments must be fresh in the compared expressions and residual comparison contexts."))
      else if (!comparison.right.contains(equation)) Some(error(step, "Comparison proof does not contain the specified equality or equivalence."))
      else if (!subset(comparison.left, statement.left) || !subset(residual, statement.right)) Some(error(step, "Conclusion drops part of the comparison context."))
      else None
    }
  }

  private def checkSubstitution(
      step: SCProofStep,
      statement: Sequent,
      premise: Sequent,
      comparisons: Seq[Sequent],
      replacements: Seq[(Expression, Expression, Seq[Variable])],
      context: (Seq[Variable], Expression),
      onLeft: Boolean
  ): SCProofCheckerJudgement = {
    val (variables, body) = context
    if (body.sort != Prop) sortMismatch(Prop, body.sort, step)
    else if (variables.size != replacements.size || comparisons.size != replacements.size)
      error(step, "Substitution requires one context variable and comparison proof per replacement.")
    else {
      val invalid = replacements.zip(variables).zip(comparisons).iterator.map {
        case ((replacement, variable), comparison) => checkComparison(step, statement, comparison, replacement, variable)
      }.collectFirst { case Some(failure) => failure }
      invalid.getOrElse {
        val before = substituteVariables(body, variables.zip(replacements.map(_._1)).toMap)
        val after = substituteVariables(body, variables.zip(replacements.map(_._2)).toMap)
        val from = if (onLeft) premise.left else premise.right
        val to = if (onLeft) statement.left else statement.right
        val untouched = if (onLeft) subset(premise.right, statement.right) else subset(premise.left, statement.left)
        if (!untouched || !allContainedExcept(from, to, before)) error(step, "Conclusion drops an untouched premise formula.")
        else if (!containsEq(to, after)) error(step, "Conclusion is missing the substituted formula.")
        else SCValidProof(SCProof(step))
      }
    }
  }

  /**
   * This function verifies that a single SCProofStep is correctly applied. It verifies that the step only refers to sequents with a lower number,
   * and that the type, premises and parameters of the proof step correspond to the claimed conclusion.
   *
   * @param no         The number of the given proof step. Needed to verify that the proof step doesn't refer to steps occuring later in the proof.
   * @param step       The proof step (object) whose correctness needs to be checked.
   * @param references A function that associates sequents to a range of positive and negative integers that the proof step may refer to. Typically,
   *                   a proof's [[SCProof.getSequent]] function.
   * @return           A Judgement about the correctness of the proof step.
   */
  def checkSingleSCStep(no: Int, step: SCProofStep, references: Int => Sequent, importsSize: Int): SCProofCheckerJudgement = {
    val ref = references
    val false_premise = step.premises.find(i => i >= no)
    val false_premise2 = step.premises.find(i => i < -importsSize)

    val r: SCProofCheckerJudgement =
      if (false_premise.nonEmpty)
        SCInvalidProof(SCProof(step), Nil, s"Step #$no cannot refer to a higher number #${false_premise.get} as a premise.")
      else if (false_premise2.nonEmpty)
        SCInvalidProof(SCProof(step), Nil, s"Steps cannot refer to step #${false_premise2.get}, imports only contains ${importsSize} elements.")
      else
        step match {

          /*
           *    Γ |- Δ
           * ------------
           *    Γ |- Δ
           */
          case Restate(s, t1) =>
            if (isSameSequent(ref(t1), s)) SCValidProof(SCProof(step)) else SCInvalidProof(SCProof(step), Nil, s"The premise does not trivially imply the conclusion.")

          /*
           *
           * ------------
           *    Γ |- Γ
           */
          case RestateTrue(s) =>
            val truth = Sequent(Set(), Set(top))
            if (isSameSequent(s, truth)) SCValidProof(SCProof(step)) else SCInvalidProof(SCProof(step), Nil, s"The desired conclusion is not a trivial tautology")

          /*
           *
           * --------------
           *   Γ, φ |- φ, Δ
           */
          case Hypothesis(Sequent(left, right), phi) =>
            // sort check
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            // logical checks
            else if (containsEq(left, phi))
              if (containsEq(right, phi)) SCValidProof(SCProof(step))
              else SCInvalidProof(SCProof(step), Nil, s"Right-hand side does not contain formula φ")
            else SCInvalidProof(SCProof(step), Nil, s"Left-hand side does not contain formula φ")

          /*
           *  Γ |- Δ, φ    φ, Σ |- Π
           * ------------------------
           *       Γ, Σ |- Δ, Π
           */
          case Cut(b, t1, t2, phi) =>
            // sort check
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            // logical checks
            else {
              val prem1 = ref(t1)
              val prem2 = ref(t2)

              if (!subset(prem1.left, b.left))
                error(step, "Left-hand side of first premise is not contained in the conclusion.")
              else if (!subset(prem2.right, b.right))
                error(step, "Right-hand side of second premise is not contained in the conclusion.")
              else if (!allContainedExcept(prem1.right, b.right, phi))
                error(step, "Right-hand side of first premise contains a formula absent from the conclusion other than the cut pivot.")
              else if (!allContainedExcept(prem2.left, b.left, phi))
                error(step, "Left-hand side of second premise contains a formula absent from the conclusion other than the cut pivot.")
              else
                SCValidProof(SCProof(step))
            }

          // Left rules
          /*
           *   Γ, φ |- Δ                 Γ, φ, ψ |- Δ
           * --------------     or     -------------
           *  Γ, φ∧ψ |- Δ               Γ, φ∧ψ |- Δ
           */
          case LeftAnd(b, t1, phi, psi) =>
            // sort checks
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            else if (psi.sort != Prop)
              sortMismatch(Prop, psi.sort, step)
            // logical checks
            else {
              val prem1 = ref(t1)
              val phiAndPsi = and(phi)(psi)
              if (!subset(prem1.right, b.right))
                error(step, "Right-hand side of the premise is not contained in the conclusion.")
              else if (!allContainedExceptEither(prem1.left, b.left, phi, psi))
                error(step, "Left-hand side of premise contains a formula absent from the conclusion other than φ or ψ.")
              else if (!containsEq(b.left, phiAndPsi))
                error(step, "Left-hand side of conclusion does not contain φ ∧ ψ.")
              else
                SCValidProof(SCProof(step))
            }

          /*
           *  Γ, φ |- Δ    Σ, ψ |- Π
           * ------------------------
           *    Γ, Σ, φ∨ψ |- Δ, Π
           */
          case LeftOr(b, ts, disjuncts) =>
            // sort checks
            val illSortedDisjunct = disjuncts.find(_.sort != Prop)
            if (illSortedDisjunct.nonEmpty) {
              val culprit = illSortedDisjunct.get
              sortMismatch(Prop, culprit.sort, step)
            } else if (ts.isEmpty) {
              error(step, "LeftOr requires at least one premise.")
            } else if (ts.size != disjuncts.size) {
              error(step, s"Number of premises (${ts.size}) is not the same as number of disjuncts (${disjuncts.size}).")
            }
            // logical checks
            else {
              val invalidPremise = ts.iterator.zip(disjuncts.iterator).zipWithIndex.find { case ((t, disjunct), _) =>
                val prem = ref(t)
                !subset(prem.right, b.right) || !allContainedExcept(prem.left, b.left, disjunct)
              }

              if (invalidPremise.nonEmpty) {
                val idx = invalidPremise.get._2
                error(step, s"Premise #$idx is not preserved by the conclusion except for its corresponding disjunct.")
              } else {
                val newDisjunct = disjuncts.reduce(or(_)(_))
                if (!containsEq(b.left, newDisjunct))
                  error(step, "Left-hand side of conclusion does not contain the disjunction.")
                else
                  SCValidProof(SCProof(step))
              }
            }

          /*
           *  Γ |- φ, Δ    Σ, ψ |- Π
           * ------------------------
           *    Γ, Σ, φ⇒ψ |- Δ, Π
           */
          case LeftImplies(b, t1, t2, phi, psi) =>
            // sort checks
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            else if (psi.sort != Prop)
              sortMismatch(Prop, psi.sort, step)
            // logical checks
            else {
              val prem1 = ref(t1)
              val prem2 = ref(t2)
              val phiImpPsi = implies(phi)(psi)

              if (!subset(prem1.left, b.left))
                error(step, "Left-hand side of first premise is not contained in the conclusion.")
              else if (!subset(prem2.right, b.right))
                error(step, "Right-hand side of second premise is not contained in the conclusion.")
              else if (!allContainedExcept(prem1.right, b.right, phi))
                error(step, "Right-hand side of first premise contains a formula absent from the conclusion other than φ.")
              else if (!allContainedExcept(prem2.left, b.left, psi))
                error(step, "Left-hand side of second premise contains a formula absent from the conclusion other than ψ.")
              else if (!containsEq(b.left, phiImpPsi))
                error(step, "Left-hand side of conclusion does not contain φ⇒ψ.")
              else
                SCValidProof(SCProof(step))
            }

          /*
           *  Γ, φ⇒ψ |- Δ               Γ, φ⇒ψ, ψ⇒φ |- Δ
           * --------------    or     ---------------
           *  Γ, φ⇔ψ |- Δ              Γ, φ⇔ψ |- Δ
           */
          case LeftIff(b, t1, phi, psi) =>
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            else if (psi.sort != Prop)
              sortMismatch(Prop, psi.sort, step)
            else {
              val prem1 = ref(t1)
              val phiImpPsi = implies(phi)(psi)
              val psiImpPhi = implies(psi)(phi)
              val phiIffPsi = iff(phi)(psi)

              if (!subset(prem1.right, b.right))
                error(step, "Right-hand side of premise is not contained in the conclusion.")
              else if (!allContainedExceptEither(prem1.left, b.left, phiImpPsi, psiImpPhi))
                error(step, "Left-hand side of premise contains a formula absent from the conclusion other than φ⇒ψ or ψ⇒φ.")
              else if (!containsEq(b.left, phiIffPsi))
                error(step, "Left-hand side of conclusion does not contain φ⇔ψ.")
              else
                SCValidProof(SCProof(step))
            }

          /*
           *   Γ |- φ, Δ
           * --------------
           *   Γ, ¬φ |- Δ
           */
          case LeftNot(b, t1, phi) =>
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            else {
              val prem1 = ref(t1)
              val nPhi = neg(phi)

              if (!subset(prem1.left, b.left))
                error(step, "Left-hand side of premise is not contained in the conclusion.")
              else if (!allContainedExcept(prem1.right, b.right, phi))
                error(step, "Right-hand side of premise contains a formula absent from the conclusion other than φ.")
              else if (!containsEq(b.left, nPhi))
                error(step, "Left-hand side of conclusion does not contain ¬φ.")
              else
                SCValidProof(SCProof(step))
            }

          /*
           *   Γ, φ[t/x] |- Δ
           * -------------------
           *  Γ, ∀x. φ |- Δ
           */
          case LeftForall(b, t1, phi, x, t) =>
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            else if (x.sort != Ind)
              sortMismatch(Ind, x.sort, step)
            else if (t.sort != Ind)
              sortMismatch(Ind, t.sort, step)
            else {
              val prem1 = ref(t1)
              // due to alpha-eq + capture avoidance, these should always be
              // compared with originals via OLEq
              val quantified = forall(Lambda(x, phi))
              val instantiated = substituteVariables(phi, Map(x -> t))

              if (!subset(prem1.right, b.right))
                error(step, "Right-hand side of premise is not contained in the conclusion.")
              else if (!allContainedExcept(prem1.left, b.left, instantiated))
                error(step, "Left-hand side of premise contains a formula absent from the conclusion other than φ[t/x].")
              else if (!containsEq(b.left, quantified))
                error(step, "Left-hand side of conclusion does not contain ∀x. φ.")
              else
                SCValidProof(SCProof(step))
            }

          /*
           *    Γ, φ |- Δ
           * ------------------- if x is not free in the resulting sequent
           *  Γ, ∃x. φ |- Δ
           */
          case LeftExists(b, t1, phi, x) =>
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            else if (x.sort != Ind)
              sortMismatch(Ind, x.sort, step)
            else {
              val prem1 = ref(t1)
              // due to alpha-eq + capture avoidance, these should always be
              // compared with originals via OLEq
              val quantified = exists(Lambda(x, phi))

              if (!subset(prem1.right, b.right))
                error(step, "Right-hand side of premise is not contained in the conclusion.")
              else if (!allContainedExcept(prem1.left, b.left, phi))
                error(step, "Left-hand side of premise contains a formula absent from the conclusion other than φ.")
              else if (!containsEq(b.left, quantified))
                error(step, "Left-hand side of conclusion does not contain ∃x. φ.")
              else if (variableIsFreeInSequent(b, x))
                error(step, "Variable x is free in the resulting sequent.")
              else
                SCValidProof(SCProof(step))
            }

          // Right rules
          /*
           *  Γ |- φ, Δ    Σ |- ψ, Π
           * ------------------------
           *    Γ, Σ |- φ∧ψ, Π, Δ
           */
          case RightAnd(b, ts, conjuncts) =>
            val illSortedConjunct = conjuncts.find(_.sort != Prop)
            if (illSortedConjunct.nonEmpty) {
              val culprit = illSortedConjunct.get
              sortMismatch(Prop, culprit.sort, step)
            } else if (ts.isEmpty) {
              error(step, "RightAnd requires at least one premise.")
            } else if (ts.size != conjuncts.size) {
              error(step, s"Number of premises (${ts.size}) is not the same as number of conjuncts (${conjuncts.size}).")
            } else {
              val invalidPremise = ts.iterator.zip(conjuncts.iterator).zipWithIndex.find { case ((t, conjunct), _) =>
                val prem = ref(t)
                !subset(prem.left, b.left) || !allContainedExcept(prem.right, b.right, conjunct)
              }

              if (invalidPremise.nonEmpty) {
                val idx = invalidPremise.get._2
                error(step, s"Premise #$idx is not preserved by the conclusion except for its corresponding conjunct.")
              } else {
                val conjunction = conjuncts.reduce(and(_)(_))
                if (!containsEq(b.right, conjunction))
                  error(step, "Right-hand side of conclusion does not contain the conjunction.")
                else
                  SCValidProof(SCProof(step))
              }
            }

          /*
           *   Γ |- φ, Δ                Γ |- φ, ψ, Δ
           * --------------    or    ---------------
           *  Γ |- φ∨ψ, Δ              Γ |- φ∨ψ, Δ
           */
          case RightOr(b, t1, phi, psi) =>
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            else if (psi.sort != Prop)
              sortMismatch(Prop, psi.sort, step)
            else {
              val prem1 = ref(t1)
              val phiOrPsi = or(phi)(psi)

              if (!subset(prem1.left, b.left))
                error(step, "Left-hand side of premise is not contained in the conclusion.")
              else if (!allContainedExceptEither(prem1.right, b.right, phi, psi))
                error(step, "Right-hand side of premise contains a formula absent from the conclusion other than φ or ψ.")
              else if (!containsEq(b.right, phiOrPsi))
                error(step, "Right-hand side of conclusion does not contain φ∨ψ.")
              else
                SCValidProof(SCProof(step))
            }

          /*
           *  Γ, φ |- ψ, Δ
           * --------------
           *  Γ |- φ⇒ψ, Δ
           */
          case RightImplies(b, t1, phi, psi) =>
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            else if (psi.sort != Prop)
              sortMismatch(Prop, psi.sort, step)
            else {
              val prem1 = ref(t1)
              val phiImpPsi = implies(phi)(psi)

              if (!allContainedExcept(prem1.left, b.left, phi))
                error(step, "Left-hand side of premise contains a formula absent from the conclusion other than φ.")
              else if (!allContainedExcept(prem1.right, b.right, psi))
                error(step, "Right-hand side of premise contains a formula absent from the conclusion other than ψ.")
              else if (!containsEq(b.right, phiImpPsi))
                error(step, "Right-hand side of conclusion does not contain φ⇒ψ.")
              else
                SCValidProof(SCProof(step))
            }

          /*
           *  Γ |- φ⇒ψ, Δ    Σ |- ψ⇒φ, Π
           * ----------------------------
           *      Γ, Σ |- φ⇔ψ, Π, Δ
           */
          case RightIff(b, t1, t2, phi, psi) =>
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            else if (psi.sort != Prop)
              sortMismatch(Prop, psi.sort, step)
            else {
              val prem1 = ref(t1)
              val prem2 = ref(t2)
              val phiImpPsi = implies(phi)(psi)
              val psiImpPhi = implies(psi)(phi)
              val phiIffPsi = iff(phi)(psi)

              if (!subset(prem1.left, b.left))
                error(step, "Left-hand side of first premise is not contained in the conclusion.")
              else if (!subset(prem2.left, b.left))
                error(step, "Left-hand side of second premise is not contained in the conclusion.")
              else if (!allContainedExcept(prem1.right, b.right, phiImpPsi))
                error(step, "Right-hand side of first premise contains a formula absent from the conclusion other than φ⇒ψ.")
              else if (!allContainedExcept(prem2.right, b.right, psiImpPhi))
                error(step, "Right-hand side of second premise contains a formula absent from the conclusion other than ψ⇒φ.")
              else if (!containsEq(b.right, phiIffPsi))
                error(step, "Right-hand side of conclusion does not contain φ⇔ψ.")
              else
                SCValidProof(SCProof(step))
            }

          /*
           *  Γ, φ |- Δ
           * --------------
           *   Γ |- ¬φ, Δ
           */
          case RightNot(b, t1, phi) =>
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            else {
              val prem1 = ref(t1)
              val nPhi = neg(phi)

              if (!subset(prem1.right, b.right))
                error(step, "Right-hand side of premise is not contained in the conclusion.")
              else if (!allContainedExcept(prem1.left, b.left, phi))
                error(step, "Left-hand side of premise contains a formula absent from the conclusion other than φ.")
              else if (!containsEq(b.right, nPhi))
                error(step, "Right-hand side of conclusion does not contain ¬φ.")
              else
                SCValidProof(SCProof(step))
            }

          /*
           *    Γ |- φ, Δ
           * ------------------- if x is not free in the resulting sequent
           *  Γ |- ∀x. φ, Δ
           */
          case RightForall(b, t1, phi, x) =>
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            else if (x.sort != Ind)
              sortMismatch(Ind, x.sort, step)
            else {
              val prem1 = ref(t1)
              // due to alpha-eq + capture avoidance, these should always be
              // compared with originals via OLEq
              val quantified = forall(Lambda(x, phi))

              if (!subset(prem1.left, b.left))
                error(step, "Left-hand side of premise is not contained in the conclusion.")
              else if (!allContainedExcept(prem1.right, b.right, phi))
                error(step, "Right-hand side of premise contains a formula absent from the conclusion other than φ.")
              else if (!containsEq(b.right, quantified))
                error(step, "Right-hand side of conclusion does not contain ∀x. φ.")
              else if (variableIsFreeInSequent(b, x))
                error(step, "Variable x is free in the resulting sequent.")
              else
                SCValidProof(SCProof(step))
            }

          /*
           *   Γ |- φ[t/x], Δ
           * -------------------
           *  Γ |- ∃x. φ, Δ
           */
          case RightExists(b, t1, phi, x, t) =>
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            else if (x.sort != Ind)
              sortMismatch(Ind, x.sort, step)
            else if (t.sort != Ind)
              sortMismatch(Ind, t.sort, step)
            else {
              val prem1 = ref(t1)
              // due to alpha-eq + capture avoidance, these should always be
              // compared with originals via OLEq
              val quantified = exists(Lambda(x, phi))
              val instantiated = substituteVariables(phi, Map(x -> t))

              if (!subset(prem1.left, b.left))
                error(step, "Left-hand side of premise is not contained in the conclusion.")
              else if (!allContainedExcept(prem1.right, b.right, instantiated))
                error(step, "Right-hand side of premise contains a formula absent from the conclusion other than φ[t/x].")
              else if (!containsEq(b.right, quantified))
                error(step, "Right-hand side of conclusion does not contain ∃x. φ.")
              else
                SCValidProof(SCProof(step))
            }

          /*
           *       Γ |- φ[t/x], Δ
           * --------------------------
           *     Γ|- φ[(εx. φ)/x], Δ
           */
          case RightEpsilon(b, t1, phi, x, t) =>
            if (phi.sort != Prop)
              sortMismatch(Prop, phi.sort, step)
            else if (x.sort != Ind)
              sortMismatch(Ind, x.sort, step)
            else if (t.sort != Ind)
              sortMismatch(Ind, t.sort, step)
            else {
              val prem1 = ref(t1)
              // due to alpha-eq + capture avoidance, these should always be
              // compared with originals via OLEq
              val epsilonTerm = epsilon(Lambda(x, phi))
              val expectedTop = substituteVariables(phi, Map(x -> t))
              val expectedBot = substituteVariables(phi, Map(x -> epsilonTerm))

              if (!subset(prem1.left, b.left))
                error(step, "Left-hand side of premise is not contained in the conclusion.")
              else if (!allContainedExcept(prem1.right, b.right, expectedTop))
                error(step, "Right-hand side of premise contains a formula absent from the conclusion other than φ[t/x].")
              else if (!containsEq(b.right, expectedBot))
                error(step, "Right-hand side of conclusion does not contain φ[(εx. φ)/x].")
              else
                SCValidProof(SCProof(step))
            }

          // Structural rules
          /*
           *     Γ |- Δ
           * --------------
           *   Γ, Σ |- Δ
           */
          case Weakening(b, t1) =>
            val premise = ref(t1)
            val syntactic = premise.left.subsetOf(b.left) && premise.right.subsetOf(b.right)
            if (syntactic || isImplyingSequent(premise, b))
              SCValidProof(SCProof(step))
            else SCInvalidProof(SCProof(step), Nil, "Conclusion cannot be trivially derived from premise.")

          // Equality Rules
          /*
           *  Γ, s=s |- Δ
           * --------------
           *     Γ |- Δ
           */
          case LeftRefl(b, t1, phi) =>
            phi match {
              case equality(left, right) =>
                val prem1 = ref(t1)

                if (!expEq(left, right))
                  error(step, "Given equality is not reflexive.")
                else if (!subset(prem1.right, b.right))
                  error(step, "Right-hand side of premise is not contained in the conclusion.")
                else if (!allContainedExcept(prem1.left, b.left, phi))
                  error(step, "Left-hand side of premise contains a formula absent from the conclusion other than the given equality.")
                else
                  SCValidProof(SCProof(step))
              case _ => error(step, "Given formula is not an equality.")
            }

          /*
           *
           * ---------------
           *   Γ |- s=s, Δ
           */
          case RightRefl(b, phi) =>
            phi match {
              case equality(left, right) =>
                if (!expEq(left, right))
                  error(step, "Given equality is not reflexive.")
                else if (!containsEq(b.right, phi))
                  error(step, "Right-hand side of conclusion does not contain the reflexive equality.")
                else
                  SCValidProof(SCProof(step))
              case _ => error(step, "Given formula is not an equality.")
            }

          case LeftSubstEq(b, t1, equals, context) =>
            checkDerivedSubstitution(step, Substitution.simultaneous(b, ref(t1), equals, context, onLeft = true))
          case RightSubstEq(b, t1, equals, context) =>
            checkDerivedSubstitution(step, Substitution.simultaneous(b, ref(t1), equals, context, onLeft = false))
          case LeftSubst(b, t1, comparisons, replacements, context) =>
            checkSubstitution(step, b, ref(t1), comparisons.map(ref), replacements, context, onLeft = true)
          case RightSubst(b, t1, comparisons, replacements, context) =>
            checkSubstitution(step, b, ref(t1), comparisons.map(ref), replacements, context, onLeft = false)

          /*
           *         Γ |- Δ
           * --------------------------
           *     Γ[ψ/?p] |- Δ[ψ/?p]
           */
          case InstSchema(bot, t1, subst) =>
            val sortMismatchSubstitution = subst.find { case (v, e) => e.sort != v.sort }

            if (sortMismatchSubstitution.nonEmpty) {
              val (v, e) = sortMismatchSubstitution.get
              sortMismatch(v.sort, e.sort, step)
            } else {
              val prem = ref(t1)

              // These checks need to retain OL (at least α-eq), as substitution may rename binders deep in the term.
              if (!prem.left.forall(formula => containsEq(bot.left, substituteVariables(formula, subst))))
                error(step, "Left-hand side of premise after instantiation is not contained in left-hand side of conclusion.")
              else if (!prem.right.forall(formula => containsEq(bot.right, substituteVariables(formula, subst))))
                error(step, "Right-hand side of premise after instantiation is not contained in right-hand side of conclusion.")
              else
                SCValidProof(SCProof(step))
            }

          case SCSubproof(sp, premises) =>
            if (premises.size != sp.imports.size)
              error(step, s"Number of premises (${premises.size}) is not the same as number of imports (${sp.imports.size}).")
            else {
              val invalid = premises.zipWithIndex.find { case (premiseNo, importIndex) =>
                !isSameSequent(ref(premiseNo), sp.imports(importIndex))
              }

              if (invalid.nonEmpty) {
                val (premiseNo, importIndex) = invalid.get
                error(step, s"Premise step #$premiseNo is not the same as import #$importIndex of the subproof.")
              } else
                checkSCProof(sp)
            }

          /*
           *
           * --------------
           *     |- s=s
           */
          case Sorry(b) =>
            SCValidProof(SCProof(step), usesSorry = true)

        }
    r
  }

  /**
   * Verifies if a given pure SequentCalculus is conditionally correct, as the imported sequents are assumed.
   * If the proof is not correct, the function will report the faulty line and a brief explanation.
   *
   * @param proof A SC proof to check
   * @return SCValidProof(SCProof(step)) if the proof is correct, else SCInvalidProof with the path to the incorrect proof step
   *         and an explanation.
   */
  def checkSCProof(proof: SCProof): SCProofCheckerJudgement = {
    var isSorry = false
    val possibleError = proof.steps.view.zipWithIndex
      .map { case (step, no) =>
        checkSingleSCStep(no, step, (i: Int) => proof.getSequent(i), proof.imports.size) match {
          case SCInvalidProof(_, path, message) => SCInvalidProof(proof, no +: path, message)
          case SCValidProof(_, sorry) =>
            isSorry = isSorry || sorry
            SCValidProof(proof, sorry)
        }
      }
      .find(j => !j.isValid)
    if (possibleError.isEmpty) SCValidProof(proof, isSorry)
    else possibleError.get
  }

}
