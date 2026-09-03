package lisa.automation.superposition
package bench

/**
 * 944 equality-free first-order FOF theorems, the non-clausal analogue of [[Evaluation]]. The SUMO domain is
 * excluded: all 359 of its problems carry a numeric ontology whose identifiers the TPTP parser mishandles and
 * which exceeds any reasonable clausification budget. Everything else is [[Harness]].
 */
object FofEvaluation:
  // The third argument names *this* object, so a forked child re-enters here and reads the same problem list.
  private val harness = new Harness("tptp-fof-fo-noeq-thm.txt", "TPTP_FOF_LIST", "lisa.automation.superposition.bench.FofEvaluation")

  def allProblems: Vector[String] = harness.allProblems
  def sample(n: Int = 100, seed: Long = 42): Vector[String] = harness.sample(n, seed)
  def main(args: Array[String]): Unit = harness.main(args)
