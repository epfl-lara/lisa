package lisa.utils.automation

import lisa.utils.K
import lisa.utils.collection.Extensions.orElseCasting
import lisa.utils.fol.FOL._
import lisa.utils.prooflib.Helpers.withParams
import lisa.utils.prooflib.Library
import lisa.utils.prooflib.ProofCarrier
import lisa.utils.prooflib.ProofHelpers._
import lisa.utils.prooflib.ProofJudgement

/**
 * Prove propositional sequents by decomposing their connectives directly.
 */
object Tautology extends SequentTactic with PremiseSequentTactic:
  def apply(using sourcecode.File, sourcecode.Line)(using Library)(conclusion: Sequent): ProofJudgement =
    from()(conclusion)

  def apply(using sourcecode.File, sourcecode.Line)(using Library)(conclusion: Sequent, premise: K.Thm): ProofJudgement =
    from(Thm(premise))(conclusion)

  /**
   * Use the supplied theorems as clauses, cutting in only the premises needed by the proof.
   */
  def from(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(premises: Thm*)(conclusion: Sequent): ProofJudgement =
    val target = conclusion.underlying
    val result = solve(target, premises = premises.map(_.kernel).toList)
    result match
      case Right(theorem) => ProofJudgement(Thm(conclusion, theorem))
      case Left(message) =>
        ProofCarrier.Failure(withParams(message, "Conclusion" -> conclusion))

  /**
   * Include the previous proof step among the supplied premises.
   */
  def fromLastStep(using file: sourcecode.File, line: sourcecode.Line)(using library: Library)(premises: Thm*): (Sequent, Thm) => ProofJudgement =
    (conclusion, lastStep) => from(lastStep +: premises.toSeq*)(conclusion)

  /**
   * Return a theorem on the left, or the failure message and requested sequent on the right.
   */
  def solveSequent(using Library)(statement: K.Sequent): Either[K.Thm, (String, K.Sequent)] =
    solve(statement).swap.map(_ -> statement)

  private case class Pending(formula: K.Expression, onLeft: Boolean):
    def occursIn(statement: K.Sequent): Boolean =
      if onLeft then statement.left.contains(formula) else statement.right.contains(formula)

  private case class Expansion(left: List[K.Expression] = Nil, right: List[K.Expression] = Nil):
    def addTo(statement: K.Sequent): K.Sequent = K.Sequent(statement.left ++ left, statement.right ++ right)
    def removeFrom(proof: K.Thm): K.Sequent = K.Sequent(proof.left -- left, proof.right -- right)

  private def sufficient(proof: K.Thm, statement: K.Sequent): Boolean =
    proof.left.subsetOf(statement.left) && proof.right.subsetOf(statement.right)

  private def checked(result: Either[?, K.Thm]): Either[String, K.Thm] =
    result.left.map(error => s"Propositional proof reconstruction failed: $error")

  /**
   * Prove a kernel sequent with direct connective rules and selective OL closure.
   */
  private def solve(statement: K.Sequent, premises: List[K.Thm] = Nil)(using library: Library): Either[String, K.Thm] =
    given K.Theory = library.theory

    def pending(left: Iterable[K.Expression], right: Iterable[K.Expression]): List[Pending] =
      left.iterator.map(Pending(_, true)).toList ++ right.iterator.map(Pending(_, false)).toList

    def focus(statement: K.Sequent, deferred: List[Pending]): List[Pending] =
      // Propagate an available antecedent before making a genuine split.
      deferred.find {
        case Pending(K.implies(a, b), true) => statement.left.contains(a) && !statement.left.contains(b)
        case _ => false
      } match
        case Some(next) => next :: deferred.filterNot(_ == next)
        case None => deferred

    def search(statement: K.Sequent, todo: List[Pending], deferred: List[Pending], premises: List[K.Thm]): Either[String, K.Thm] =
      val reusable = premises.find(sufficient(_, statement))
      statement.left.find(statement.right.contains) match
        case Some(pivot) => checked(K.Hypothesis(K.Sequent(Set(pivot), Set(pivot)), pivot))
        case None if reusable.nonEmpty => Right(reusable.get)
        case None =>
          todo match
            case current :: tail if !current.occursIn(statement) => search(statement, tail, deferred, premises)
            case current :: tail =>
              val Pending(formula, onLeft) = current
              val rest =
                if onLeft then statement.copy(left = statement.left - formula)
                else statement.copy(right = statement.right - formula)

              def unary(left: List[K.Expression], right: List[K.Expression])(rebuild: (K.Sequent, K.Thm) => Either[?, K.Thm]): Either[String, K.Thm] =
                val expansion = Expansion(left, right)
                search(expansion.addTo(rest), pending(left, right) ::: tail, deferred, premises).flatMap { proof =>
                  // Skip a rule whose principal formula was not used in its premise.
                  if sufficient(proof, statement) then Right(proof)
                  else
                    val context = expansion.removeFrom(proof)
                    val target = if onLeft then context.copy(left = context.left + formula) else context.copy(right = context.right + formula)
                    checked(rebuild(target, proof))
                }

              (onLeft, formula) match
                case (true, K.bot) => checked(K.RestateTrue(K.Sequent(Set(K.bot), Set.empty)))
                case (false, K.top) => checked(K.RestateTrue(K.Sequent(Set.empty, Set(K.top))))
                case (true, K.and(a, b)) => unary(List(a, b), Nil)(K.LeftAnd(_, _, a, b))
                case (false, K.or(a, b)) => unary(Nil, List(a, b))(K.RightOr(_, _, a, b))
                case (true, K.neg(a)) => unary(Nil, List(a))(K.LeftNot(_, _, a))
                case (false, K.neg(a)) => unary(List(a), Nil)(K.RightNot(_, _, a))
                case (false, K.implies(a, b)) => unary(List(a), List(b))(K.RightImplies(_, _, a, b))
                case (true, K.iff(a, b)) => unary(List(K.implies(a)(b), K.implies(b)(a)), Nil)(K.LeftIff(_, _, a, b))
                case (true, K.or(_, _)) | (true, K.implies(_, _)) | (false, K.and(_, _)) | (false, K.iff(_, _)) =>
                  search(statement, tail, current :: deferred, premises)
                case _ if !formula.isBetaNormal =>
                  val normalized = formula.betaNormalForm
                  val left = if onLeft then List(normalized) else Nil
                  val right = if onLeft then Nil else List(normalized)
                  unary(left, right)(K.Restate(_, _))
                case _ => search(statement, tail, deferred, premises)

            case Nil =>
              focus(statement, deferred) match
                case current :: remaining if !current.occursIn(statement) => search(statement, Nil, remaining, premises)
                case Pending(formula, onLeft) :: remaining =>
                  val rest =
                    if onLeft then statement.copy(left = statement.left - formula)
                    else statement.copy(right = statement.right - formula)

                  def binary(first: Expansion, second: Expansion)(rebuild: (K.Sequent, K.Thm, K.Thm) => Either[?, K.Thm]): Either[String, K.Thm] =
                    val checkIff = !onLeft && (formula match
                      case K.iff(_, _) => true
                      case _ => false)
                    def branch(expansion: Expansion): Either[String, K.Thm] =
                      val child = expansion.addTo(rest)
                      def decompose = search(child, pending(expansion.left, expansion.right), remaining, premises)
                      if checkIff then K.RestateTrue(child).orElseCasting(decompose) else decompose
                    branch(first).flatMap { left =>
                      if sufficient(left, statement) then Right(left)
                      else
                        branch(second).flatMap { right =>
                          if sufficient(right, statement) then Right(right)
                          else
                            val a = first.removeFrom(left)
                            val b = second.removeFrom(right)
                            val context = K.Sequent(a.left ++ b.left, a.right ++ b.right)
                            val target = if onLeft then context.copy(left = context.left + formula) else context.copy(right = context.right + formula)
                            checked(rebuild(target, left, right))
                        }
                    }

                  (onLeft, formula) match
                    case (true, K.or(a, b)) =>
                      binary(Expansion(left = List(a)), Expansion(left = List(b)))((s, l, r) => K.LeftOr(s, Seq(l, r), Seq(a, b)))
                    case (true, K.implies(a, b)) =>
                      binary(Expansion(right = List(a)), Expansion(left = List(b)))(K.LeftImplies(_, _, _, a, b))
                    case (false, K.and(a, b)) =>
                      binary(Expansion(right = List(a)), Expansion(right = List(b)))((s, l, r) => K.RightAnd(s, Seq(l, r), Seq(a, b)))
                    case (false, K.iff(a, b)) =>
                      binary(Expansion(right = List(K.implies(a)(b))), Expansion(right = List(K.implies(b)(a))))(K.RightIff(_, _, _, a, b))
                    case _ => Left("Unexpected deferred propositional rule.")
                case Nil =>
                  val clauses = premises.iterator.filterNot(premise => premise.left.exists(statement.right.contains) || premise.right.exists(statement.left.contains)).map { premise =>
                    val unknown = pending(premise.right -- statement.right, premise.left -- statement.left)
                    premise -> unknown
                  }
                  clauses.minByOption(_._2.size) match
                    case None => K.RestateTrue(statement).left.map(_ => "The statement has an open propositional branch.")
                    case Some((premise, literals)) =>
                      val remaining = premises.filterNot(_ eq premise)

                      // A sequent is a clause: refute its antecedents or use one of its conclusions.
                      def eliminate(current: K.Thm, literals: List[Pending]): Either[String, K.Thm] =
                        if sufficient(current, statement) then Right(current)
                        else
                          literals match
                            case Nil => Left("Premise reconstruction left an undischarged formula.")
                            case (literal @ Pending(formula, onLeft)) :: tail =>
                              val needed = if onLeft then current.right.contains(formula) else current.left.contains(formula)
                              if !needed then eliminate(current, tail)
                              else
                                val child = if onLeft then statement.copy(left = statement.left + formula) else statement.copy(right = statement.right + formula)
                                search(child, List(literal), Nil, remaining).flatMap { proof =>
                                  if sufficient(proof, statement) then Right(proof)
                                  else
                                    val (first, second) = if onLeft then (current, proof) else (proof, current)
                                    val target = K.Sequent(first.left ++ (second.left - formula), (first.right - formula) ++ second.right)
                                    checked(K.Cut(target, first, second, formula)).flatMap(eliminate(_, tail))
                                }
                      eliminate(premise, literals)

    def align(proof: K.Thm): Either[String, K.Thm] =
      if proof.statement == statement then Right(proof) else checked(K.Weakening(statement, proof))
    def decompose = search(statement, pending(statement.left, statement.right), Nil, premises).flatMap(align)
    if premises.exists(premise => !(premise.theory eq library.theory)) then Left("A premise belongs to a different theory.")
    else
      statement.left.find(statement.right.contains) match
        case Some(pivot) => checked(K.Hypothesis(statement, pivot))
        case None =>
          premises.find(sufficient(_, statement)) match
            case Some(proof) => align(proof)
            case None => K.RestateTrue(statement).orElseCasting(decompose)
