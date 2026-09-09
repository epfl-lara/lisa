package lisa.utils.prooflib

import lisa.utils.K
import lisa.utils.fol.FOL.*
import lisa.utils.prooflib.Helpers.withParams

import scala.collection.mutable

/** Proves Horn consequences by forward chaining and cut reconstruction. */
object Horn extends DerivedFromPremises:

  object CutKey:
    /** Match cut formulas by their front-end syntax. */
    val Syntactic: Expr[Prop] => Expr[Prop] = identity

    /** Use OL equivalence as hash-key equality. */
    final class OL private[CutKey] (private val formula: K.Expression):
      override def equals(other: Any): Boolean =
        other match
          case that: OL => K.isSame(formula, that.formula)
          case _ => false

      // OL has no cheap canonical hash currently. Keep this lawful and let
      // benchmarks measure its collision cost separately.
      override def hashCode(): Int = 0

    /** Match cut formulas modulo OL equivalence. */
    val OL: Expr[Prop] => OL = formula => new OL(formula.underlying)

  protected def prove(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(conclusion: Sequent, premises: Seq[Thm]): ProofJudgement =
    proveWith(conclusion, premises, CutKey.Syntactic)

  /** Use `cutKey` to choose which formulas may be connected by a cut. */
  def withCutKey[Key](cutKey: Expr[Prop] => Key)(premises: Thm*)(using
      file: sourcecode.File,
      line: sourcecode.Line,
      library: Library
  ): Sequent => ProofJudgement =
    conclusion => proveWith(conclusion, premises, cutKey)

  private def proveWith[Key](conclusion: Sequent, premises: Seq[Thm], cutKey: Expr[Prop] => Key)(using
      file: sourcecode.File,
      line: sourcecode.Line,
      library: Library
  ): ProofJudgement =
    solve(conclusion, premises, cutKey) match
      case Right(theorem) => ProofJudgement(theorem)
      case Left(message) =>
        ProofCarrier(Set(SoftError(withParams(message, "Conclusion" -> conclusion, "Premises" -> premises), file, line)), conclusion, None, ())

  private def solve[Key](conclusion: Sequent, premises: Seq[Thm], cutKey: Expr[Prop] => Key)(using library: Library): Either[String, Thm] =
    if conclusion.right.size != 1 then Left("Horn requires exactly one formula on the right of the conclusion.")
    else
      premises.zipWithIndex.collectFirst { case (premise, index) if premise.right.size != 1 => index -> premise } match
        case Some((index, premise)) => Left(s"Horn premise $index is not definite: expected exactly one formula on the right, found ${premise.right.size}.")
        case None =>
          val clauses = premises.map(premise => HornSolver.Clause(premise.left.toVector, premise.right.head)).toIndexedSeq
          val target = conclusion.right.head
          val result = HornSolver.solve(conclusion.left, clauses, Seq(target))(cutKey)
          result.goal match
            case None => Left("Horn forward chaining could not derive the conclusion.")
            case Some(_) => reconstruct(conclusion, premises, result, target, cutKey)

  private def reconstruct[Key](
      conclusion: Sequent,
      premises: Seq[Thm],
      result: HornSolver.Result[Expr[Prop]],
      target: Expr[Prop],
      cutKey: Expr[Prop] => Key
  )(using library: Library): Either[String, Thm] =
    val known = mutable.HashMap.empty[Key, Thm]

    val iterator = result.steps.iterator
    while iterator.hasNext do
      val step = iterator.next()
      val proof = step.origin match
        case HornSolver.Origin.Initial => hypothesis(step.atom)
        case HornSolver.Origin.ByClause(index) => applyClause(conclusion.left, premises(index), known, cutKey)

      proof match
        case Left(error) => return Left(error)
        case Right(theorem) => known.update(cutKey(step.atom), theorem)

    for
      proof <- known.get(cutKey(target)).toRight("Horn lost the derivation of its reached goal.")
      aligned <- align(proof, target)
      weakened <- K.Weakening(using library.theory)(conclusion.underlying, aligned.kernel).left.map(error => s"Horn final weakening failed: $error")
    yield Thm(conclusion, weakened)

  private def hypothesis(atom: Expr[Prop])(using library: Library): Either[String, Thm] =
    val statement = Sequent(Set(atom), Set(atom))
    K.Hypothesis(using library.theory)(statement.underlying, atom.underlying)
      .left
      .map(error => s"Horn hypothesis reconstruction failed: $error")
      .map(Thm(statement, _))

  private def applyClause[Key](
      initialFacts: Set[Expr[Prop]],
      clause: Thm,
      known: mutable.Map[Key, Thm],
      cutKey: Expr[Prop] => Key
  )(using library: Library): Either[String, Thm] =
    var current = clause
    val body = clause.left.iterator
    while body.hasNext do
      val required = body.next()
      if !initialFacts.contains(required) then
        val next = for
          available <- known.get(cutKey(required)).toRight(s"Horn reconstruction is missing a proof of $required.")
          aligned <- align(available, required)
          statement = Sequent((current.left - required) ++ aligned.left, current.right)
          cut <- K
            .Cut(using library.theory)(statement.underlying, aligned.kernel, current.kernel, required.underlying)
            .left
            .map(error => s"Horn cut reconstruction failed for $required: $error")
        yield Thm(statement, cut)

        next match
          case Left(error) => return Left(error)
          case Right(theorem) => current = theorem
    Right(current)

  private def align(proof: Thm, required: Expr[Prop])(using library: Library): Either[String, Thm] =
    proof.right.headOption match
      case Some(actual) if actual == required => Right(proof)
      case Some(_) =>
        val statement = Sequent(proof.left, Set(required))
        K.Restate(using library.theory)(statement.underlying, proof.kernel)
          .left
          .map(error => s"Horn could not align a selected cut with $required: $error")
          .map(Thm(statement, _))
      case None => Left("Horn encountered a proof without a conclusion during reconstruction.")
