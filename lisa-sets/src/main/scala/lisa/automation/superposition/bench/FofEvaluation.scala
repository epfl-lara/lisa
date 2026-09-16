package lisa.automation.superposition
package bench

/**
 * The 8017 refutable first-order FOF problems of the TPTP library, from [[BuildDatasets]]. Everything else is
 * [[Harness]].
 */
object FofEvaluation:
  // The third argument names *this* object, so a forked child re-enters here and reads the same problem list.
  private val harness = new Harness("tptp-eligible-fof.txt", "TPTP_FOF_LIST", "lisa.automation.superposition.bench.FofEvaluation")

  def allProblems: Vector[String] = harness.allProblems
  def sample(n: Int = 100, seed: Long = 42): Vector[String] = harness.sample(n, seed)
  def main(args: Array[String]): Unit = harness.main(args)
