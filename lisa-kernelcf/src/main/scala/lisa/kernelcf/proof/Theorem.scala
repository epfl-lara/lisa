package lisa.kernelcf.proof

import lisa.kernelcf.fol.FOL.*

///////////////////////////////////////////////////////////////////////////////
// Basic Proof Objects
///////////////////////////////////////////////////////////////////////////////

/**
  * A proven statement and its metadata.
  * 
  * New objects can only be constructed in the current module
  * by proof-checking functions.
  * 
  * `Thm`s from different `theory`s are incompatible. 
  *
  * @param statement the statement this `Thm` is a witness of
  * @param rule the (last) rule used to justify this statement
  * @param theory the (running) theory under which this statement was proven
  * @param axioms the cumulative set of axioms used in the justification of this `Thm`
  * @param usesSorry whether this `Thm` transitively depends on a trusted `Sorry` step
  */
case class Thm private [proof] (
  statement: Sequent,
  rule: Step,
  theory: Theory,
  axioms: Set[Sequent],
  usesSorry: Boolean = false
):
  inline def left: Set[Expression] = statement.left
  inline def right: Set[Expression] = statement.right

sealed trait ProofError

sealed trait GeneralError extends ProofError
case class SortMismatch(step: Step, expected: Sort, actual: Sort, expression: Expression) extends GeneralError
case class TheoryMismatch(step: Step, expected: Theory, actual: Theory) extends GeneralError

sealed trait Step: 
  protected given Step = this
  type ErrorType <: ProofError
  type Result[+T] = Either[ErrorType, T]


///////////////////////////////////////////////////////////////////////////////
// Equality and Set Helpers
///////////////////////////////////////////////////////////////////////////////
object Helpers:

  /**
   * The chosen equality for general checks in proof steps.
   *
   * Syntactic equality is expected to be sound, but strong algorithms
   * are fine and increase the expressiveness of steps.
   */
  inline def expEq(s: Expression, t: Expression): Boolean =
    // s == t // syntactic eq
    isSame(s, t) // OL eq
    // or some other eq...

  extension (set: Set[Expression])
    inline def containsEq(formula: Expression): Boolean =
      set.contains(formula) || set.exists(expEq(_, formula))

    inline def subsetOfEq(target: Set[Expression]): Boolean =
      set.forall(target.map(simpleReducedForm).containsSimple)

    inline def containedExcept(target: Set[Expression], exception: Expression): Boolean =
      val simplifiedTarget = target.map(simpleReducedForm)
      set.forall(formula => simplifiedTarget.containsSimple(formula) || expEq(formula, exception))

    inline def containedExceptEither(target: Set[Expression], exception1: Expression, exception2: Expression): Boolean =
      set.forall(formula => target.contains(formula) || expEq(formula, exception1) || expEq(formula, exception2))

  extension (set: Set[SimpleExpression])
    inline private def containsSimple(expr: Expression): Boolean =
      set.contains(simpleReducedForm(expr))

import Helpers.*

///////////////////////////////////////////////////////////////////////////////
// Proof Check Helpers
///////////////////////////////////////////////////////////////////////////////

private def theorem(using theory: Theory, rule: Step)(statement: Sequent, premises: Iterable[Thm] = Nil, axioms: Set[Sequent] = Set.empty, usesSorry: Boolean = false): Either[GeneralError, Thm] =
  val sorry = usesSorry || premises.exists(_.usesSorry)
  val allAxioms = premises.foldLeft(axioms)(_ `union` _.axioms)
  
  // the last check for any theorem, its premises must be from the same theory context
  val violatingPremise = premises.find(prem => !(theory eq prem.theory))

  if violatingPremise.isDefined then
    Left: 
      TheoryMismatch(rule, theory, violatingPremise.get.theory)
  else
    Right:
      Thm(
        statement,
        rule,
        theory,
        allAxioms,
        sorry
      )

private inline def requireSort[E, T](using step: Step)(e: Expression, expected: Sort)(body: => Either[E, T]): Either[SortMismatch | E, T] =
  if e.sort == expected then body else Left(SortMismatch(step, expected, e.sort, e))

private inline def requireFormula[E, T](using step: Step)(e: Expression)(body: => Either[E, T]): Either[SortMismatch | E, T] =
  requireSort(e, Prop)(body)

private inline def requireTerm[E, T](using step: Step)(e: Expression)(body: => Either[E, T]): Either[SortMismatch | E, T] =
  requireSort(e, Ind)(body)

private def variableIsFreeInSequent(sequent: Sequent, variable: Variable): Boolean =
  sequent.left.exists(_.freeVariables.contains(variable)) || sequent.right.exists(_.freeVariables.contains(variable))

/**
  * Helper for [[LeftSubstEq]] and [[RightSubstEq]].
  */
private def liftedEqualities(equalities: Seq[(Expression, Expression)]): Seq[Expression] =
  def liftEquality(s: Expression, t: Expression): Expression =
    val maxId = (s.freeVariables ++ t.freeVariables).map(_.id.no).maxOption.getOrElse(0) + 1
    val vars = (maxId until (maxId + s.sort.depth)).map(i => Variable(Identifier("x", i), Ind))
    val sApplied = vars.foldLeft(s)((f, arg) => f(arg))
    val tApplied = vars.foldLeft(t)((f, arg) => f(arg))
    val base =
      if sApplied.sort == Prop then iff(sApplied)(tApplied)
      else equality(sApplied)(tApplied)
    vars.foldRight(base) { case (arg, acc) => forall(Lambda(arg, acc)) }

  equalities.map(liftEquality)

///////////////////////////////////////////////////////////////////////////////
// Proof Steps
///////////////////////////////////////////////////////////////////////////////

case object Sorry extends Step:
  type ErrorType = Nothing // Sorry does not throw its own errors
 
  def apply(using theory: Theory)(statement: Sequent): Result[Thm] = 
    Right(Thm(statement, this, theory, Set.empty, usesSorry = true))
  
case object Axiom extends Step:
  type ErrorType = Nothing // Axiom does not throw its own errors

  def apply(using theory: Theory)(statement: Sequent): Result[Thm] = 
    Right(Thm(statement, this, theory, Set(statement)))

case object Definition extends Step:
  type ErrorType = DefinitionError

  sealed trait DefinitionError extends ProofError
  case class AlreadyDefined(cst: Constant) extends DefinitionError
  case class ExpressionNotInTheory(exp: Expression) extends DefinitionError
  case class ContainsSchematic(exp: Expression) extends DefinitionError
  case class VariableSortMismatch(variable: Variable, expected: Sort, actual: Sort) extends DefinitionError
  case class ArityMismatch(cst: Constant, expected: Int, actual: Int) extends DefinitionError
  case class DefinitionSortMismatch(expected: Sort, actual: Sort, exp: Expression) extends DefinitionError

  def apply(using theory: Theory)(cst: Constant, vars: Seq[Variable], exp: Expression): Result[Thm] = 
    if theory.defines(cst) then
      Left(AlreadyDefined(cst))
    else if !theory.contains(exp) then
      Left(ExpressionNotInTheory(exp))
    else if exp.freeVariables.nonEmpty then
      Left(ContainsSchematic(exp))
    else if cst.sort.depth != vars.length then
      Left(ArityMismatch(cst, cst.sort.depth, vars.length))
    else if flatTypeParameters(cst.sort) != vars.map(_.sort) then
      val violation = flatTypeParameters(cst.sort).zip(vars).find { case (expected, variable) => expected != variable.sort }
      val (expected, variable) = violation.get
      Left(VariableSortMismatch(variable, expected, variable.sort))
    else if cst.sort != exp.sort then
      Left(DefinitionSortMismatch(cst.sort, exp.sort, exp))
    else
      val appliedCst = vars.foldLeft(cst: Expression)((f, arg) => f(arg))
      val appliedExp = vars.foldLeft(exp)((f, arg) => f(arg))
      val formula = 
        if appliedCst.sort == Prop then iff(appliedCst)(appliedExp)
        else equality(appliedCst)(appliedExp)
      val sequent = Sequent(Set.empty, Set(formula))

      val definition = Thm(sequent, this, theory, Set.empty)

      // MUTABLY update the theory
      theory.registerDefinition(cst, definition)

      Right(definition)

/**
  *    Γ |- Δ
  * ------------
  *    Γ |- Δ
  */
case object Restate extends Step:
  type ErrorType = RestateError | GeneralError

  sealed trait RestateError extends ProofError
  case class NotImplying(premise: Thm, statement: Sequent) extends RestateError

  def apply(using theory: Theory)(statement: Sequent, premise: Thm): Result[Thm] =
    if isSameSequent(premise.statement, statement) then theorem(statement, Seq(premise))
    else Left(NotImplying(premise, statement))

/**
  *
  * ------------
  *    Γ |- Γ
  */
case object RestateTrue extends Step:
  type ErrorType = RestateTrueError

  sealed trait RestateTrueError extends ProofError
  case class NotTrivial(statement: Sequent) extends RestateTrueError

  def apply(using theory: Theory)(statement: Sequent): Result[Thm] =
    if isSameSequent(statement, Sequent(Set.empty, Set(top))) then 
      Right(Thm(statement, this, theory, Set.empty))
    else Left(NotTrivial(statement))

/**
  * --------------
  *   Γ, φ |- φ, Δ
  */
case object Hypothesis extends Step:
  type ErrorType = HypothesisError | GeneralError

  sealed trait HypothesisError extends ProofError
  case class MissingFromLeft(statement: Sequent, phi: Expression) extends HypothesisError
  case class MissingFromRight(statement: Sequent, phi: Expression) extends HypothesisError

  def apply(using theory: Theory)(statement: Sequent, φ: Expression): Result[Thm] = 
    requireFormula(φ):
      val Sequent(left, right) = statement
      if !left.containsEq(φ) then
        Left(MissingFromLeft(statement, φ))
      else if !right.containsEq(φ) then
        Left(MissingFromRight(statement, φ))
      else
        theorem(statement)

/**
  *  Γ |- Δ, φ    φ, Σ |- Π
  * ------------------------
  *       Γ, Σ |- Δ, Π
  */
case object Cut extends Step:
  type ErrorType = CutError | GeneralError

  sealed trait CutError extends ProofError
  case class MissingFromFirst(premise: Thm, statement: Sequent) extends CutError
  case class MissingFromSecond(premise: Thm, statement: Sequent) extends CutError
  case class ExtraneousInFirst(premise: Thm, statement: Sequent, pivot: Expression) extends CutError
  case class ExtraneousInSecond(premise: Thm, statement: Sequent, pivot: Expression) extends CutError

  def apply(using theory: Theory)(statement: Sequent, prem1: Thm, prem2: Thm, φ: Expression): Result[Thm] =
    requireFormula(φ):
      if !prem1.left.subsetOfEq(statement.left) then Left(MissingFromFirst(prem1, statement))
      else if !prem2.right.subsetOfEq(statement.right) then Left(MissingFromSecond(prem2, statement))
      else if !prem1.right.containedExcept(statement.right, φ) then Left(ExtraneousInFirst(prem1, statement, φ))
      else if !prem2.left.containedExcept(statement.left, φ) then Left(ExtraneousInSecond(prem2, statement, φ))
      else theorem(statement, Seq(prem1, prem2))

/**
  *   Γ, φ |- Δ                Γ, φ, ψ |- Δ
  * --------------     or     --------------
  *  Γ, φ∧ψ |- Δ               Γ, φ∧ψ |- Δ
  */
case object LeftAnd extends Step:
  type ErrorType = LeftAndError | GeneralError

  sealed trait LeftAndError extends ProofError
  case class MissingFromPremise(premise: Thm, statement: Sequent) extends LeftAndError
  case class ExtraneousInPremise(premise: Thm, statement: Sequent, phi: Expression, psi: Expression) extends LeftAndError
  case class MissingConjunction(statement: Sequent, conjunction: Expression) extends LeftAndError

  def apply(using theory: Theory)(statement: Sequent, premise: Thm, φ: Expression, ψ: Expression): Result[Thm] =
    requireFormula(φ):
      requireFormula(ψ):
        val φAndψ = and(φ)(ψ)
        if !premise.right.subsetOfEq(statement.right) then Left(MissingFromPremise(premise, statement))
        else if !premise.left.containedExceptEither(statement.left, φ, ψ) then Left(ExtraneousInPremise(premise, statement, φ, ψ))
        else if !statement.left.containsEq(φAndψ) then Left(MissingConjunction(statement, φAndψ))
        else theorem(statement, Seq(premise))

/**
  *  Γ, φ |- Δ    Σ, ψ |- Π    ...
  * --------------------------------
  *    Γ, Σ, φ∨ψ∨... |- Δ, Π
  */
case object LeftOr extends Step:
  type ErrorType = LeftOrError | GeneralError

  sealed trait LeftOrError extends ProofError
  case class EmptyPremises(statement: Sequent) extends LeftOrError
  case class ArityMismatch(statement: Sequent, premises: Seq[Thm], disjuncts: Seq[Expression]) extends LeftOrError
  case class PremiseNotPreserved(premise: Thm, statement: Sequent, disjunct: Expression, index: Int) extends LeftOrError
  case class MissingDisjunction(statement: Sequent, disjunction: Expression) extends LeftOrError

  def apply(using theory: Theory)(statement: Sequent, premises: Seq[Thm], disjuncts: Seq[Expression]): Result[Thm] =
    disjuncts.find(_.sort != Prop) match
      case Some(disjunct) => Left(SortMismatch(this, Prop, disjunct.sort, disjunct))
      case None if premises.isEmpty => Left(EmptyPremises(statement))
      case None if premises.size != disjuncts.size => Left(ArityMismatch(statement, premises, disjuncts))
      case None =>
        premises.iterator.zip(disjuncts.iterator).zipWithIndex.find { case ((premise, disjunct), _) =>
          !premise.right.subsetOfEq(statement.right) || !premise.left.containedExcept(statement.left, disjunct)
        } match
          case Some(((premise, disjunct), index)) => Left(PremiseNotPreserved(premise, statement, disjunct, index))
          case None =>
            val disjunction = disjuncts.reduce(or(_)(_))
            if statement.left.containsEq(disjunction) then theorem(statement, premises)
            else Left(MissingDisjunction(statement, disjunction))

/**
  *  Γ |- φ, Δ    Σ, ψ |- Π
  * ------------------------
  *    Γ, Σ, φ⇒ψ |- Δ, Π
  */
case object LeftImplies extends Step:
  type ErrorType = LeftImpliesError | GeneralError

  sealed trait LeftImpliesError extends ProofError
  case class MissingFromFirst(premise: Thm, statement: Sequent) extends LeftImpliesError
  case class MissingFromSecond(premise: Thm, statement: Sequent) extends LeftImpliesError
  case class ExtraneousInFirst(premise: Thm, statement: Sequent, phi: Expression) extends LeftImpliesError
  case class ExtraneousInSecond(premise: Thm, statement: Sequent, psi: Expression) extends LeftImpliesError
  case class MissingImplication(statement: Sequent, implication: Expression) extends LeftImpliesError

  def apply(using theory: Theory)(statement: Sequent, prem1: Thm, prem2: Thm, φ: Expression, ψ: Expression): Result[Thm] =
    requireFormula(φ):
      requireFormula(ψ):
        val φImpψ = implies(φ)(ψ)
        if !prem1.left.subsetOfEq(statement.left) then Left(MissingFromFirst(prem1, statement))
        else if !prem2.right.subsetOfEq(statement.right) then Left(MissingFromSecond(prem2, statement))
        else if !prem1.right.containedExcept(statement.right, φ) then Left(ExtraneousInFirst(prem1, statement, φ))
        else if !prem2.left.containedExcept(statement.left, ψ) then Left(ExtraneousInSecond(prem2, statement, ψ))
        else if !statement.left.containsEq(φImpψ) then Left(MissingImplication(statement, φImpψ))
        else theorem(statement, Seq(prem1, prem2))

/**
  *  Γ, φ⇒ψ |- Δ               Γ, φ⇒ψ, ψ⇒φ |- Δ
  * --------------    or     --------------------
  *  Γ, φ⇔ψ |- Δ                 Γ, φ⇔ψ |- Δ
  */
case object LeftIff extends Step:
  type ErrorType = LeftIffError | GeneralError

  sealed trait LeftIffError extends ProofError
  case class MissingFromPremise(premise: Thm, statement: Sequent) extends LeftIffError
  case class ExtraneousInPremise(premise: Thm, statement: Sequent, leftImplication: Expression, rightImplication: Expression) extends LeftIffError
  case class MissingIff(statement: Sequent, iffFormula: Expression) extends LeftIffError

  def apply(using theory: Theory)(statement: Sequent, premise: Thm, φ: Expression, ψ: Expression): Result[Thm] =
    requireFormula(φ):
      requireFormula(ψ):
        val φImpψ = implies(φ)(ψ)
        val ψImpφ = implies(ψ)(φ)
        val φIffψ = iff(φ)(ψ)
        if !premise.right.subsetOfEq(statement.right) then Left(MissingFromPremise(premise, statement))
        else if !premise.left.containedExceptEither(statement.left, φImpψ, ψImpφ) then Left(ExtraneousInPremise(premise, statement, φImpψ, ψImpφ))
        else if !statement.left.containsEq(φIffψ) then Left(MissingIff(statement, φIffψ))
        else theorem(statement, Seq(premise))

/**
  *   Γ |- φ, Δ
  * --------------
  *   Γ, ¬φ |- Δ
  */
case object LeftNot extends Step:
  type ErrorType = LeftNotError | GeneralError

  sealed trait LeftNotError extends ProofError
  case class MissingFromPremise(premise: Thm, statement: Sequent) extends LeftNotError
  case class ExtraneousInPremise(premise: Thm, statement: Sequent, phi: Expression) extends LeftNotError
  case class MissingNegation(statement: Sequent, negation: Expression) extends LeftNotError

  def apply(using theory: Theory)(statement: Sequent, premise: Thm, φ: Expression): Result[Thm] =
    requireFormula(φ):
      val nφ = neg(φ)
      if !premise.left.subsetOfEq(statement.left) then Left(MissingFromPremise(premise, statement))
      else if !premise.right.containedExcept(statement.right, φ) then Left(ExtraneousInPremise(premise, statement, φ))
      else if !statement.left.containsEq(nφ) then Left(MissingNegation(statement, nφ))
      else theorem(statement, Seq(premise))

/**
  *   Γ, φ[t/x] |- Δ
  * -------------------
  *  Γ, ∀x. φ |- Δ
  */
case object LeftForall extends Step:
  type ErrorType = LeftForallError | GeneralError

  sealed trait LeftForallError extends ProofError
  case class MissingFromPremise(premise: Thm, statement: Sequent) extends LeftForallError
  case class ExtraneousInPremise(premise: Thm, statement: Sequent, instantiated: Expression) extends LeftForallError
  case class MissingForall(statement: Sequent, quantified: Expression) extends LeftForallError

  def apply(using theory: Theory)(statement: Sequent, premise: Thm, φ: Expression, x: Variable, t: Expression): Result[Thm] =
    requireFormula(φ):
      requireTerm(x):
        requireTerm(t):
          val quantified = forall(Lambda(x, φ))
          val instantiated = substituteVariables(φ, Map(x -> t))
          if !premise.right.subsetOfEq(statement.right) then Left(MissingFromPremise(premise, statement))
          else if !premise.left.containedExcept(statement.left, instantiated) then Left(ExtraneousInPremise(premise, statement, instantiated))
          else if !statement.left.containsEq(quantified) then Left(MissingForall(statement, quantified))
          else theorem(statement, Seq(premise))

/**
  *    Γ, φ |- Δ
  * ------------------- if x is not free in the resulting sequent
  *  Γ, ∃x. φ |- Δ
  */
case object LeftExists extends Step:
  type ErrorType = LeftExistsError | GeneralError

  sealed trait LeftExistsError extends ProofError
  case class MissingFromPremise(premise: Thm, statement: Sequent) extends LeftExistsError
  case class ExtraneousInPremise(premise: Thm, statement: Sequent, phi: Expression) extends LeftExistsError
  case class MissingExists(statement: Sequent, quantified: Expression) extends LeftExistsError
  case class VariableFree(statement: Sequent, variable: Variable) extends LeftExistsError

  def apply(using theory: Theory)(statement: Sequent, premise: Thm, φ: Expression, x: Variable): Result[Thm] =
    requireFormula(φ):
      requireTerm(x):
        val quantified = exists(Lambda(x, φ))
        if !premise.right.subsetOfEq(statement.right) then Left(MissingFromPremise(premise, statement))
        else if !premise.left.containedExcept(statement.left, φ) then Left(ExtraneousInPremise(premise, statement, φ))
        else if !statement.left.containsEq(quantified) then Left(MissingExists(statement, quantified))
        else if variableIsFreeInSequent(statement, x) then Left(VariableFree(statement, x))
        else theorem(statement, Seq(premise))

/**
  *  Γ |- φ, Δ    Σ |- ψ, Π     ...
  * ------------------------------------
  *    Γ, Σ |- φ∧ψ∧..., Π, Δ
  */
case object RightAnd extends Step:
  type ErrorType = RightAndError | GeneralError

  sealed trait RightAndError extends ProofError
  case class EmptyPremises(statement: Sequent) extends RightAndError
  case class ArityMismatch(statement: Sequent, premises: Seq[Thm], conjuncts: Seq[Expression]) extends RightAndError
  case class PremiseNotPreserved(premise: Thm, statement: Sequent, conjunct: Expression, index: Int) extends RightAndError
  case class MissingConjunction(statement: Sequent, conjunction: Expression) extends RightAndError

  def apply(using theory: Theory)(statement: Sequent, premises: Seq[Thm], conjuncts: Seq[Expression]): Result[Thm] =
    conjuncts.find(_.sort != Prop) match
      case Some(conjunct) => Left(SortMismatch(this, Prop, conjunct.sort, conjunct))
      case None if premises.isEmpty => Left(EmptyPremises(statement))
      case None if premises.size != conjuncts.size => Left(ArityMismatch(statement, premises, conjuncts))
      case None =>
        premises.iterator.zip(conjuncts.iterator).zipWithIndex.find { case ((premise, conjunct), _) =>
          !premise.left.subsetOfEq(statement.left) || !premise.right.containedExcept(statement.right, conjunct)
        } match
          case Some(((premise, conjunct), index)) => Left(PremiseNotPreserved(premise, statement, conjunct, index))
          case None =>
            val conjunction = conjuncts.reduce(and(_)(_))
            if statement.right.containsEq(conjunction) then theorem(statement, premises)
            else Left(MissingConjunction(statement, conjunction))

/**
  *   Γ |- φ, Δ                Γ |- φ, ψ, Δ
  * --------------    or    ---------------
  *  Γ |- φ∨ψ, Δ              Γ |- φ∨ψ, Δ
  */
case object RightOr extends Step:
  type ErrorType = RightOrError | GeneralError

  sealed trait RightOrError extends ProofError
  case class MissingFromPremise(premise: Thm, statement: Sequent) extends RightOrError
  case class ExtraneousInPremise(premise: Thm, statement: Sequent, phi: Expression, psi: Expression) extends RightOrError
  case class MissingDisjunction(statement: Sequent, disjunction: Expression) extends RightOrError

  def apply(using theory: Theory)(statement: Sequent, premise: Thm, φ: Expression, ψ: Expression): Result[Thm] =
    requireFormula(φ):
      requireFormula(ψ):
        val φOrψ = or(φ)(ψ)
        if !premise.left.subsetOfEq(statement.left) then Left(MissingFromPremise(premise, statement))
        else if !premise.right.containedExceptEither(statement.right, φ, ψ) then Left(ExtraneousInPremise(premise, statement, φ, ψ))
        else if !statement.right.containsEq(φOrψ) then Left(MissingDisjunction(statement, φOrψ))
        else theorem(statement, Seq(premise))

/**
  *  Γ, φ |- ψ, Δ
  * --------------
  *  Γ |- φ⇒ψ, Δ
  */
case object RightImplies extends Step:
  type ErrorType = RightImpliesError | GeneralError

  sealed trait RightImpliesError extends ProofError
  case class ExtraneousInLeft(premise: Thm, statement: Sequent, phi: Expression) extends RightImpliesError
  case class ExtraneousInRight(premise: Thm, statement: Sequent, psi: Expression) extends RightImpliesError
  case class MissingImplication(statement: Sequent, implication: Expression) extends RightImpliesError

  def apply(using theory: Theory)(statement: Sequent, premise: Thm, φ: Expression, ψ: Expression): Result[Thm] =
    requireFormula(φ):
      requireFormula(ψ):
        val φImpψ = implies(φ)(ψ)
        if !premise.left.containedExcept(statement.left, φ) then Left(ExtraneousInLeft(premise, statement, φ))
        else if !premise.right.containedExcept(statement.right, ψ) then Left(ExtraneousInRight(premise, statement, ψ))
        else if !statement.right.containsEq(φImpψ) then Left(MissingImplication(statement, φImpψ))
        else theorem(statement, Seq(premise))

/**
  *  Γ |- φ⇒ψ, Δ    Σ |- ψ⇒φ, Π
  * ----------------------------
  *      Γ, Σ |- φ⇔ψ, Π, Δ
  */
case object RightIff extends Step:
  type ErrorType = RightIffError | GeneralError

  sealed trait RightIffError extends ProofError
  case class MissingFromFirst(premise: Thm, statement: Sequent) extends RightIffError
  case class MissingFromSecond(premise: Thm, statement: Sequent) extends RightIffError
  case class ExtraneousInFirst(premise: Thm, statement: Sequent, leftImplication: Expression) extends RightIffError
  case class ExtraneousInSecond(premise: Thm, statement: Sequent, rightImplication: Expression) extends RightIffError
  case class MissingIff(statement: Sequent, iffFormula: Expression) extends RightIffError

  def apply(using theory: Theory)(statement: Sequent, prem1: Thm, prem2: Thm, φ: Expression, ψ: Expression): Result[Thm] =
    requireFormula(φ):
      requireFormula(ψ):
        val φImpψ = implies(φ)(ψ)
        val ψImpφ = implies(ψ)(φ)
        val φIffψ = iff(φ)(ψ)
        if !prem1.left.subsetOfEq(statement.left) then Left(MissingFromFirst(prem1, statement))
        else if !prem2.left.subsetOfEq(statement.left) then Left(MissingFromSecond(prem2, statement))
        else if !prem1.right.containedExcept(statement.right, φImpψ) then Left(ExtraneousInFirst(prem1, statement, φImpψ))
        else if !prem2.right.containedExcept(statement.right, ψImpφ) then Left(ExtraneousInSecond(prem2, statement, ψImpφ))
        else if !statement.right.containsEq(φIffψ) then Left(MissingIff(statement, φIffψ))
        else theorem(statement, Seq(prem1, prem2))

/**
  *  Γ, φ |- Δ
  * --------------
  *   Γ |- ¬φ, Δ
  */
case object RightNot extends Step:
  type ErrorType = RightNotError | GeneralError

  sealed trait RightNotError extends ProofError
  case class MissingFromPremise(premise: Thm, statement: Sequent) extends RightNotError
  case class ExtraneousInPremise(premise: Thm, statement: Sequent, phi: Expression) extends RightNotError
  case class MissingNegation(statement: Sequent, negation: Expression) extends RightNotError

  def apply(using theory: Theory)(statement: Sequent, premise: Thm, φ: Expression): Result[Thm] =
    requireFormula(φ):
      val nφ = neg(φ)
      if !premise.right.subsetOfEq(statement.right) then Left(MissingFromPremise(premise, statement))
      else if !premise.left.containedExcept(statement.left, φ) then Left(ExtraneousInPremise(premise, statement, φ))
      else if !statement.right.containsEq(nφ) then Left(MissingNegation(statement, nφ))
      else theorem(statement, Seq(premise))

/**
  *    Γ |- φ, Δ
  * ------------------- if x is not free in the resulting sequent
  *  Γ |- ∀x. φ, Δ
  */
case object RightForall extends Step:
  type ErrorType = RightForallError | GeneralError

  sealed trait RightForallError extends ProofError
  case class MissingFromPremise(premise: Thm, statement: Sequent) extends RightForallError
  case class ExtraneousInPremise(premise: Thm, statement: Sequent, phi: Expression) extends RightForallError
  case class MissingForall(statement: Sequent, quantified: Expression) extends RightForallError
  case class VariableFree(statement: Sequent, variable: Variable) extends RightForallError

  def apply(using theory: Theory)(statement: Sequent, premise: Thm, φ: Expression, x: Variable): Result[Thm] =
    requireFormula(φ):
      requireTerm(x):
        val quantified = forall(Lambda(x, φ))
        if !premise.left.subsetOfEq(statement.left) then Left(MissingFromPremise(premise, statement))
        else if !premise.right.containedExcept(statement.right, φ) then Left(ExtraneousInPremise(premise, statement, φ))
        else if !statement.right.containsEq(quantified) then Left(MissingForall(statement, quantified))
        else if variableIsFreeInSequent(statement, x) then Left(VariableFree(statement, x))
        else theorem(statement, Seq(premise))

/**
  *   Γ |- φ[t/x], Δ
  * -------------------
  *  Γ |- ∃x. φ, Δ
  */
case object RightExists extends Step:
  type ErrorType = RightExistsError | GeneralError

  sealed trait RightExistsError extends ProofError
  case class MissingFromPremise(premise: Thm, statement: Sequent) extends RightExistsError
  case class ExtraneousInPremise(premise: Thm, statement: Sequent, instantiated: Expression) extends RightExistsError
  case class MissingExists(statement: Sequent, quantified: Expression) extends RightExistsError

  def apply(using theory: Theory)(statement: Sequent, premise: Thm, φ: Expression, x: Variable, t: Expression): Result[Thm] =
    requireFormula(φ):
      requireTerm(x):
        requireTerm(t):
          val quantified = exists(Lambda(x, φ))
          val instantiated = substituteVariables(φ, Map(x -> t))
          if !premise.left.subsetOfEq(statement.left) then Left(MissingFromPremise(premise, statement))
          else if !premise.right.containedExcept(statement.right, instantiated) then Left(ExtraneousInPremise(premise, statement, instantiated))
          else if !statement.right.containsEq(quantified) then Left(MissingExists(statement, quantified))
          else theorem(statement, Seq(premise))

/**
  *       Γ |- φ[t/x], Δ
  * -------------------------- if y is not free in φ
  *    Γ|- φ[(εx. φ)/x],  Δ
  */
case object RightEpsilon extends Step:
  type ErrorType = RightEpsilonError | GeneralError

  sealed trait RightEpsilonError extends ProofError
  case class MissingFromPremise(premise: Thm, statement: Sequent) extends RightEpsilonError
  case class ExtraneousInPremise(premise: Thm, statement: Sequent, expectedFormula: Expression) extends RightEpsilonError
  case class MissingEpsilonInstance(statement: Sequent, expectedFormula: Expression) extends RightEpsilonError

  def apply(using theory: Theory)(statement: Sequent, premise: Thm, φ: Expression, x: Variable, t: Expression): Result[Thm] =
    requireFormula(φ):
      requireTerm(x):
        requireTerm(t):
          val epsilonTerm = epsilon(Lambda(x, φ))
          val expectedTop = substituteVariables(φ, Map(x -> t))
          val expectedBot = substituteVariables(φ, Map(x -> epsilonTerm))
          if !premise.left.subsetOfEq(statement.left) then Left(MissingFromPremise(premise, statement))
          else if !premise.right.containedExcept(statement.right, expectedTop) then Left(ExtraneousInPremise(premise, statement, expectedTop))
          else if !statement.right.containsEq(expectedBot) then Left(MissingEpsilonInstance(statement, expectedBot))
          else theorem(statement, Seq(premise))

/**
  *     Γ |- Δ
  * --------------
  *   Γ, Σ |- Δ, Π
  */
case object Weakening extends Step:
  type ErrorType = WeakeningError | GeneralError

  sealed trait WeakeningError extends ProofError
  case class NotImplying(premise: Thm, statement: Sequent) extends WeakeningError

  def apply(using theory: Theory)(statement: Sequent, premise: Thm): Result[Thm] =
    if isImplyingSequent(premise.statement, statement) then theorem(statement, Seq(premise))
    else Left(NotImplying(premise, statement))

/**
  *  Γ, s=s |- Δ
  * --------------
  *     Γ |- Δ
  */
case object LeftRefl extends Step:
  type ErrorType = LeftReflError | GeneralError

  sealed trait LeftReflError extends ProofError
  case class NotAnEquality(expression: Expression) extends LeftReflError
  case class EqualityNotReflexive(equality: Expression, left: Expression, right: Expression) extends LeftReflError
  case class MissingFromPremise(premise: Thm, statement: Sequent) extends LeftReflError
  case class ExtraneousInPremise(premise: Thm, statement: Sequent, equality: Expression) extends LeftReflError

  def apply(using theory: Theory)(statement: Sequent, premise: Thm, φ: Expression): Result[Thm] =
    φ match
      case equality(left, right) =>
        if !expEq(left, right) then Left(EqualityNotReflexive(φ, left, right))
        else if !premise.right.subsetOfEq(statement.right) then Left(MissingFromPremise(premise, statement))
        else if !premise.left.containedExcept(statement.left, φ) then Left(ExtraneousInPremise(premise, statement, φ))
        else theorem(statement, Seq(premise))
      case _ => Left(NotAnEquality(φ))

/**
  *
  * --------------
  *     |- s=s
  */
case object RightRefl extends Step:
  type ErrorType = RightReflError | GeneralError

  sealed trait RightReflError extends ProofError
  case class NotAnEquality(expression: Expression) extends RightReflError
  case class EqualityNotReflexive(equality: Expression, left: Expression, right: Expression) extends RightReflError
  case class MissingEquality(statement: Sequent, equality: Expression) extends RightReflError

  def apply(using theory: Theory)(statement: Sequent, φ: Expression): Result[Thm] =
    φ match
      case equality(left, right) =>
        if !expEq(left, right) then Left(EqualityNotReflexive(φ, left, right))
        else if !statement.right.containsEq(φ) then Left(MissingEquality(statement, φ))
        else theorem(statement)
      case _ => Left(NotAnEquality(φ))

/**
  *                     Γ, φ(s) |- Δ
  * -----------------------------------------------------
  *   Γ, ∀x,...,z. (s x ... z)=(t x ... z), φ(t) |- Δ
  */
case object LeftSubstEq extends Step:
  type ErrorType = LeftSubstEqError | GeneralError

  sealed trait LeftSubstEqError extends ProofError
  case class ArityMismatch(statement: Sequent, equalities: Seq[(Expression, Expression)], lambdaArgs: Seq[Variable]) extends LeftSubstEqError
  case class SubstitutionSortNotAllowed(argument: Variable) extends LeftSubstEqError
  case class MissingFromPremise(premise: Thm, statement: Sequent) extends LeftSubstEqError
  case class ExtraneousInPremise(premise: Thm, statement: Sequent, expectedFormula: Expression) extends LeftSubstEqError
  case class MissingLiftedEquality(statement: Sequent, equality: Expression) extends LeftSubstEqError
  case class MissingSubstitutedFormula(statement: Sequent, substitutedFormula: Expression) extends LeftSubstEqError

  def apply(using theory: Theory)(statement: Sequent, premise: Thm, equals: Seq[(Expression, Expression)], lambdaφ: (Seq[Variable], Expression)): Result[Thm] =
    val (sList, tList) = equals.unzip
    val (φArgs, φBody) = lambdaφ
    if φBody.sort != Prop then Left(SortMismatch(this, Prop, φBody.sort, φBody))
    else if φArgs.size != sList.size then Left(ArityMismatch(statement, equals, φArgs))
    else
      val violation = equals.zip(φArgs).find { case ((s, t), arg) =>
        s.sort != arg.sort || t.sort != arg.sort || (!arg.sort.isFunctional && !arg.sort.isPredicate)
      }
      violation match
        case Some(((s, _), arg)) if s.sort != arg.sort => Left(SortMismatch(this, arg.sort, s.sort, s))
        case Some(((s, t), arg)) if t.sort != arg.sort => Left(SortMismatch(this, arg.sort, t.sort, t))
        case Some((_, arg)) => Left(SubstitutionSortNotAllowed(arg))
        case None =>
          val φs = substituteVariables(φBody, (φArgs zip sList).toMap)
          val φt = substituteVariables(φBody, (φArgs zip tList).toMap)
          val equalities = liftedEqualities(equals)
          if !premise.right.subsetOfEq(statement.right) then Left(MissingFromPremise(premise, statement))
          else if !premise.left.containedExcept(statement.left, φs) then Left(ExtraneousInPremise(premise, statement, φs))
          else
            equalities.find(!statement.left.containsEq(_)) match
              case Some(eq) => Left(MissingLiftedEquality(statement, eq))
              case None if !statement.left.containsEq(φt) => Left(MissingSubstitutedFormula(statement, φt))
              case None => theorem(statement, Seq(premise))

/**
  *                     Γ |- φ(s), Δ
  * ------------------------------------------------------
  *     Γ, ∀x,...,z. (s x ... z)=(t x ... z) |- φ(t), Δ
  */
case object RightSubstEq extends Step:
  type ErrorType = RightSubstEqError | GeneralError

  sealed trait RightSubstEqError extends ProofError
  case class ArityMismatch(statement: Sequent, equalities: Seq[(Expression, Expression)], lambdaArgs: Seq[Variable]) extends RightSubstEqError
  case class SubstitutionSortNotAllowed(argument: Variable) extends RightSubstEqError
  case class MissingFromPremise(premise: Thm, statement: Sequent) extends RightSubstEqError
  case class MissingLiftedEquality(statement: Sequent, equality: Expression) extends RightSubstEqError
  case class ExtraneousInPremise(premise: Thm, statement: Sequent, expectedFormula: Expression) extends RightSubstEqError
  case class MissingSubstitutedFormula(statement: Sequent, substitutedFormula: Expression) extends RightSubstEqError

  def apply(using theory: Theory)(statement: Sequent, premise: Thm, equals: Seq[(Expression, Expression)], lambdaφ: (Seq[Variable], Expression)): Result[Thm] =
    val (sList, tList) = equals.unzip
    val (φArgs, φBody) = lambdaφ
    if φBody.sort != Prop then Left(SortMismatch(this, Prop, φBody.sort, φBody))
    else if φArgs.size != sList.size then Left(ArityMismatch(statement, equals, φArgs))
    else
      val violation = equals.zip(φArgs).find { case ((s, t), arg) =>
        s.sort != arg.sort || t.sort != arg.sort || (!arg.sort.isFunctional && !arg.sort.isPredicate)
      }
      violation match
        case Some(((s, _), arg)) if s.sort != arg.sort => Left(SortMismatch(this, arg.sort, s.sort, s))
        case Some(((s, t), arg)) if t.sort != arg.sort => Left(SortMismatch(this, arg.sort, t.sort, t))
        case Some((_, arg)) => Left(SubstitutionSortNotAllowed(arg))
        case None =>
          val φs = substituteVariables(φBody, (φArgs zip sList).toMap)
          val φt = substituteVariables(φBody, (φArgs zip tList).toMap)
          val equalities = liftedEqualities(equals)
          if !premise.left.subsetOfEq(statement.left) then Left(MissingFromPremise(premise, statement))
          else
            equalities.find(!statement.left.containsEq(_)) match
              case Some(eq) => Left(MissingLiftedEquality(statement, eq))
              case None if !premise.right.containedExcept(statement.right, φs) => Left(ExtraneousInPremise(premise, statement, φs))
              case None if !statement.right.containsEq(φt) => Left(MissingSubstitutedFormula(statement, φt))
              case None => theorem(statement, Seq(premise))

/**
  *         Γ |- Δ
  * --------------------------
  *     Γ[ψ/?p] |- Δ[ψ/?p]
  */
case object InstSchema extends Step:
  type ErrorType = InstSchemaError | GeneralError

  sealed trait InstSchemaError extends ProofError
  case class MissingLeftInstantiation(premise: Thm, statement: Sequent, original: Expression, instantiated: Expression) extends InstSchemaError
  case class MissingRightInstantiation(premise: Thm, statement: Sequent, original: Expression, instantiated: Expression) extends InstSchemaError

  def apply(using theory: Theory)(statement: Sequent, premise: Thm, subst: Map[Variable, Expression]): Result[Thm] =
    subst.find { case (v, e) => e.sort != v.sort } match
      case Some((v, e)) => Left(SortMismatch(this, v.sort, e.sort, e))
      case None =>
        premise.left.find(formula => !statement.left.containsEq(substituteVariables(formula, subst))) match
          case Some(formula) => Left(MissingLeftInstantiation(premise, statement, formula, substituteVariables(formula, subst)))
          case None =>
            premise.right.find(formula => !statement.right.containsEq(substituteVariables(formula, subst))) match
              case Some(formula) => Left(MissingRightInstantiation(premise, statement, formula, substituteVariables(formula, subst)))
              case None => theorem(statement, Seq(premise))
