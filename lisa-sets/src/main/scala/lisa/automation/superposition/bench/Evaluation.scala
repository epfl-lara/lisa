package lisa.automation.superposition
package bench

/**
 * Clausal, equality-free, unsatisfiable TPTP problems. Every one is unsatisfiable, so refuted against timed
 * out is the measure and a saturated verdict is itself a bug. Being equality-free, `equality=off` here
 * measures what the equality machinery costs when it can never apply. Everything else is [[Harness]].
 */
object Evaluation:
  // The third argument names *this* object, so a forked child re-enters here and reads the same problem list.
  private val harness = new Harness("tptp-clausal-fo-noeq-uns.txt", "TPTP_CNF_LIST", "lisa.automation.superposition.bench.Evaluation")

  def allProblems: Vector[String] = harness.allProblems
  def sample(n: Int = 100, seed: Long = 42): Vector[String] = harness.sample(n, seed)
  def main(args: Array[String]): Unit = harness.main(args)
