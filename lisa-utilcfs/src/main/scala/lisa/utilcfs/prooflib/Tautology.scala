package lisa.utilcfs.prooflib

import lisa.utilcfs.K
import lisa.utilcfs.fol.FOL.*
import lisa.utilcfs.prooflib.Helpers.withParams
import lisa.utilcfs.prooflib.ProofHelpers.*

object Tautology extends SequentTactic with PremiseSequentTactic:
  def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent): ProofJudgement =
    from(using file, line)()(conclusion)

  def apply(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
    from(using file, line)(Thm(premise))(conclusion)

  def from(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(premises: Thm*)(conclusion: Sequent): ProofJudgement =
    solve(conclusion.underlying, premises.map(_.kernel)) match
      case Right(thm) => ProofJudgement(thm)
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
    if premises.isEmpty then proveTautology(conclusion)
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

      proveTautology(K.Sequent(left, conclusion.right)).flatMap(cutPremises(conclusion, cuts.result()))

  private def proveTautology(using library: Library)(statement: K.Sequent): Either[String, K.Thm] =
    val truth = K.Sequent(Set.empty[K.Expression], Set(K.top))
    K.RestateTrue(using library.theory)(truth) match
      case Left(error) => Left(s"Tautology could not introduce truth: $error")
      case Right(truthTheorem) =>
        K.Weakening(using library.theory)(statement, truthTheorem).left.map:
          case _: K.Weakening.NotImplying =>
            "The statement may be incorrect or not provable within propositional logic."
          case error => s"Tautology weakening failed: $error"

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
