package lisa.automation.superposition
package bench

/** 944 equality-free first-order FOF theorems, the non-clausal analogue of [[Evaluation]]. The SUMO domain is
  * excluded: all 359 of its problems carry a numeric ontology whose identifiers the TPTP parser mishandles and
  * which exceeds any reasonable clausification budget.
  *
  * Being equality-free, varying `equality` here measures only what the equality machinery costs when it cannot
  * apply. Everything else is [[FofHarness]]. */
object FofEvaluation:
  // The third argument names *this* object, so a forked child re-enters here and reads the same problem list.
  private val harness = new FofHarness("tptp-fof-fo-noeq-thm.txt", "TPTP_FOF_LIST",
    "lisa.automation.superposition.bench.FofEvaluation")

  // `allProblems`/`sample` are the only members referenced outside the harness (tests, other harnesses); see
  // [[FofHarness]] for their contract.
  def allProblems: Vector[String] = harness.allProblems
  def sample(n: Int = 100, seed: Long = 42): Vector[String] = harness.sample(n, seed)
  def main(args: Array[String]): Unit = harness.main(args)
