package lisa.utils.prooflib

import lisa.utils.K
import lisa.utils.fol.FOL.*
import lisa.utils.prooflib.Helpers.withParams
import lisa.utils.prooflib.ProofHelpers.*

object Tautology extends SequentTactic with PremiseSequentTactic:
  def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent): ProofJudgement =
    from(using file, line)()(conclusion)

  def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
    from(using file, line)(Thm(premise))(conclusion)

  def from(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(premises: Thm*)(conclusion: Sequent): ProofJudgement =
    solve(conclusion.underlying, premises.map(_.kernel)) match
      case Right(thm) => ProofCarrier(Set.empty, conclusion, Some(Thm(conclusion, thm)), ())
      case Left(message) =>
        ProofCarrier(
          Set(SoftError(withParams(message, "Conclusion" -> conclusion, "Premises" -> premises), file, line)),
          conclusion,
          None,
          ()
        )

  /**
    * Variant of [[from]] that also adds the local proof's previous theorem to
    * the premises. The `Have` machinery supplies that theorem.
    */
  def fromLastStep(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(premises: Thm*): (Sequent, Thm) => ProofJudgement =
    (conclusion, lastStep) => from(using file, line)(lastStep +: premises.toSeq*)(conclusion)

  /**
    * Attempts to prove a kernel sequent propositionally, returning a theorem
    * instead of a proof tree. This is intentionally just kernel steps: truth is
    * introduced once, then weakened to the desired statement.
    */
  def solveSequent(using library: Library)(statement: K.Sequent): Either[K.Thm, (String, K.Sequent)] =
    proveTautology(statement).swap.map(_ -> statement)

  private def solve(using library: Library)(conclusion: K.Sequent, premises: Seq[K.Thm]): Either[String, K.Thm] =
    proveFromPremises(conclusion, premises)(proveTautology)

  /** Adds theorem premises as formulas, invokes a solver, then cuts them away. */
  private[prooflib] def proveFromPremises(using library: Library)(
      conclusion: K.Sequent,
      premises: Seq[K.Thm]
  )(solver: K.Sequent => Either[String, K.Thm]): Either[String, K.Thm] =
    if premises.isEmpty then solver(conclusion)
    else
      val premiseFormulas = Vector.newBuilder[(K.Expression, K.Thm)]
      val iterator = premises.iterator
      while iterator.hasNext do
        formulaTheorem(iterator.next()) match
          case Right(result) => premiseFormulas += result
          case Left(error) => return Left(error)

      // Only add premise formulas that are not already available in the target.
      // This avoids cutting away a real user assumption equivalent to a premise.
      var left = conclusion.left
      val cuts = Vector.newBuilder[(K.Expression, K.Thm)]
      for (formula, thm) <- premiseFormulas.result() do
        if !K.Helpers.containsEq(left)(formula) then
          left += formula
          cuts += formula -> thm

      solver(K.Sequent(left, conclusion.right)).flatMap(cutPremises(conclusion, cuts.result()))

  private def proveTautology(using library: Library)(statement: K.Sequent): Either[String, K.Thm] =
    val augmented = AugSequent((Nil, Nil), K.reducedForm(K.sequentToFormula(statement)))
    val marker = K.Variable(K.freshId(augmented.formula.freeVariables.map(_.id), "MaRvIn"), K.Prop)
    try
      Right(checked("final restate")(K.Restate(using library.theory)(statement, solveAugSequent(using library, marker)(augmented))))
    catch
      case failure: NoProofFoundException =>
        Left(
          "The statement may be incorrect or not provable within propositional logic.\n" +
            "The proof search failed because it needed the truth of the following sequent:\n" +
            failure.unsolvable
        )
      case failure: ReconstructionFailure => Left(failure.getMessage)

  private case class AugSequent(decisions: (List[K.Expression], List[K.Expression]), formula: K.Expression)

  private class NoProofFoundException(val unsolvable: K.Sequent) extends Exception

  private class ReconstructionFailure(step: String, error: Any)
      extends Exception(s"Tautology proof reconstruction failed at $step: $error")

  private def checked(step: String)(result: Either[?, K.Thm]): K.Thm =
    result.fold(error => throw new ReconstructionFailure(step, error), identity)

  /** Reduces a sequent to the AIG expression used by proof search. */
  def reduceSequent(statement: K.Sequent): K.Expression =
    K.reducedForm(K.sequentToFormula(statement))

  /** Chooses the most frequent propositional atom in a reduced expression. */
  def findBestAtom(expression: K.Expression): Option[K.Expression] =
    val atoms = scala.collection.mutable.HashMap.empty[K.Expression, Int]
    def collect(current: K.Expression): Unit =
      current match
        case K.and(left, right) =>
          collect(left)
          collect(right)
        case K.neg(inner) => collect(inner)
        case _ if current != K.top && current != K.bot => atoms.updateWith(current)(_.map(_ + 1).orElse(Some(1)))
        case _ => ()
    collect(expression)
    atoms.maxByOption(_._2).map(_._1)

  /** Replaces occurrences of `target` by `variable`, avoiding variable capture. */
  def findSubformula(expression: K.Expression, variable: K.Variable, target: K.Expression): Option[K.Expression] =
    def recurse(outer: K.Expression, forbidden: Set[K.Variable]): (K.Expression, Boolean) =
      if K.isSame(outer, target) then variable -> true
      else
        outer match
          case K.Application(function, argument) =>
            val (newFunction, changedFunction) = recurse(function, forbidden)
            val (newArgument, changedArgument) = recurse(argument, forbidden)
            if changedFunction || changedArgument then K.Application(newFunction, newArgument) -> true
            else outer -> false
          case K.Lambda(bound, body) if !forbidden.contains(bound) =>
            val (newBody, changed) = recurse(body, forbidden)
            if changed then K.Lambda(bound, newBody) -> true else outer -> false
          case K.Lambda(bound, body) =>
            val fresh = K.Variable(K.freshId(outer.freeVariables.map(_.id) ++ forbidden.map(_.id), bound.id), bound.sort)
            val renamed = K.substituteVariables(body, Map(bound -> fresh))
            val (newBody, changed) = recurse(renamed, forbidden + fresh)
            if changed then K.Lambda(fresh, newBody) -> true else outer -> false
          case _ => outer -> false

    recurse(expression, target.freeVariables) match
      case (result, true) => Some(result)
      case _ => None

  private def solveAugSequent(using library: Library, marker: K.Variable)(sequent: AugSequent): K.Thm =
    val reduced = K.reducedForm(sequent.formula)
    val (positive, negative) = sequent.decisions
    val assumptions = (positive ++ negative.map(formula => K.neg(formula))).toSet

    if reduced == K.top then
      checked("closed branch")(K.RestateTrue(using library.theory)(K.Sequent(assumptions, Set(sequent.formula))))
    else
      findBestAtom(reduced) match
        case None =>
          throw new NoProofFoundException(K.Sequent(positive.toSet, (reduced :: negative).toSet))
        case Some(atom) =>
          findSubformula(reduced, marker, atom) match
            case None => solveAugSequent(AugSequent(sequent.decisions, reduced))
            case Some(context) =>
              val positiveBranch = AugSequent(
                (atom :: positive, negative),
                K.substituteVariables(context, Map(marker -> K.top))
              )
              val positiveProof = solveAugSequent(positiveBranch)
              val positiveSubstitution = checked("positive atom substitution"):
                K.RightSubstEq(
                  using library.theory
                )(
                  K.Sequent(assumptions + atom, Set(reduced)),
                  positiveProof,
                  Seq(K.top -> atom),
                  Seq(marker) -> context
                )

              val negatedAtom = K.neg(atom)
              val negativeBranch = AugSequent(
                (negatedAtom :: positive, negative),
                K.substituteVariables(context, Map(marker -> K.bot))
              )
              val negativeProof = solveAugSequent(negativeBranch)
              val negativeSubstitution = checked("negative atom substitution"):
                K.RightSubstEq(
                  using library.theory
                )(
                  K.Sequent(assumptions + negatedAtom, Set(reduced)),
                  negativeProof,
                  Seq(K.bot -> atom),
                  Seq(marker) -> context
                )

              val atomOnRight = checked("negative branch restate"):
                K.Restate(using library.theory)(K.Sequent(assumptions, Set(reduced, atom)), negativeSubstitution)
              val cut = checked("atom cut"):
                K.Cut(using library.theory)(K.Sequent(assumptions, Set(reduced)), atomOnRight, positiveSubstitution, atom)
              checked("reduced formula restate"):
                K.Restate(using library.theory)(K.Sequent(assumptions, Set(sequent.formula)), cut)

  private def formulaTheorem(using library: Library)(premise: K.Thm): Either[String, (K.Expression, K.Thm)] =
    val formula = K.sequentToFormula(premise.statement)
    val statement = K.Sequent(Set.empty[K.Expression], Set(formula))
    K.Restate(using library.theory)(statement, premise)
      .left.map(error => s"Tautology could not convert a premise to formula form: $error")
      .map(formula -> _)

  private def cutPremises(using library: Library)(conclusion: K.Sequent, cuts: Vector[(K.Expression, K.Thm)])(initial: K.Thm): Either[String, K.Thm] =
    var current = initial
    val iterator = cuts.iterator
    while iterator.hasNext do
      val (formula, premise) = iterator.next()
      val nextStatement = K.Sequent(current.statement.left - formula, current.statement.right)
      K.Cut(using library.theory)(nextStatement, premise, current, formula) match
        case Right(thm) => current = thm
        case Left(error) => return Left(s"Tautology could not discharge a premise formula: $error")

    if current.statement == conclusion then Right(current)
    else K.Restate(using library.theory)(conclusion, current).left.map(error => s"Tautology final restate failed: $error")
