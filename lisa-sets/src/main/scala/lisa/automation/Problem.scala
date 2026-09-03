package lisa.automation

import lisa.utils.K.Application
import lisa.utils.K.Expression
import lisa.utils.K.Lambda
import lisa.utils.K.Sequent
import lisa.utils.K.Variable

/**
 * What a solver is asked to do: derive `conjecture` from `hypotheses`, with no conjecture standing for the
 * empty goal `⊢`. `frozen` holds the variables a transformation must leave alone: neither instantiated nor quantified over.
 * Skolem symbols an earlier phase introduced are the usual case.
 *
 * A kernel proof of a problem concludes its goal and takes its hypotheses as imports, pointwise and in order;
 * [[hypIndex]] is the import reference of the `i`-th one. A producer needing imports of its own puts them
 * after the hypotheses.
 */
case class Problem(hypotheses: Seq[Sequent], conjecture: Option[Sequent], frozen: Set[Variable] = Set.empty):

  /**
   * The hypotheses, as the leading segment of the import list of a proof of this problem.
   */
  def imports: IndexedSeq[Sequent] = hypotheses.toIndexedSeq

  /**
   * The import reference of hypothesis `i`.
   */
  def hypIndex(i: Int): Int = -(i + 1)

  /**
   * Node count over every formula in the problem, hypotheses and conjecture alike. How big the input is, which
   * search heuristics and benchmarks size their budgets by.
   */
  def size: Int =
    def seqSize(s: Sequent): Int =
      s.left.toSeq.map(Problem.formulaSize).sum + s.right.toSeq.map(Problem.formulaSize).sum
    hypotheses.map(seqSize).sum + conjecture.fold(0)(seqSize)

object Problem:

  /**
   * Node count of a kernel expression: variables, constants, applications and lambdas each count one.
   */
  private def formulaSize(e: Expression): Int = e match
    case Application(f, a) => 1 + formulaSize(f) + formulaSize(a)
    case Lambda(_, body) => 1 + formulaSize(body)
    case _ => 1
