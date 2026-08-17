package lisa.automation.superposition
package bench

/** 5589 equality-bearing first-order FOF theorems, selected by the TPTP `SPC` header exactly as
  * [[FofEvaluation]] is but with the equality classes in place of the equality-free ones. The SUMO domain is
  * excluded for the same reason as there.
  *
  * This is the dataset on which the equality inferences do real work, so it is the one on which the `equality`
  * setting is worth varying. Everything else is [[FofHarness]]. */
object EqFofEvaluation:
  // The third argument names *this* object, so a forked child re-enters here and reads the same problem list.
  private val harness = new FofHarness("tptp-fof-fo-eq-thm.txt", "TPTP_FOF_EQ_LIST",
    "lisa.automation.superposition.bench.EqFofEvaluation")

  // `allProblems`/`sample` are the only members referenced outside the harness (tests, other harnesses); see
  // [[FofHarness]] for their contract.
  def allProblems: Vector[String] = harness.allProblems
  def sample(n: Int = 100, seed: Long = 42): Vector[String] = harness.sample(n, seed)
  def main(args: Array[String]): Unit = harness.main(args)
