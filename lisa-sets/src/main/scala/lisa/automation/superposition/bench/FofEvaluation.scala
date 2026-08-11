package lisa.automation.superposition
package bench

/**
 * The second evaluation dataset: non-clausal (FOF), first-order, equality-free, arithmetic-free TPTP
 * **theorems** (`tptp-fof-fo-noeq-thm.txt`) — the analog of the clausal [[Evaluation]] set, selected the very
 * same way (by the TPTP `SPC` header: `FOF_THM_{RFO,EPR}_NEQ`) but **without** the already-clausal restriction.
 * The `CSR` (SUMO commonsense) domain is excluded: all 359 such problems include a giant (30k–40k-line) numeric
 * ontology whose long numeric-suffixed identifiers (`c_bcase_3235139646`) the TPTP parser mishandles and which
 * exceed any sane clausification size budget — leaving 944 clean FO theorems.
 *
 * Being equality-free, the `equality` ablation here only measures the equality machinery's inert cost (unlike
 * the equality-bearing [[EqFofEvaluation]]). Everything else — the pipeline, CLI, and output — is the shared
 * [[FofHarness]]; see it for the run modes and column meanings.
 */
object FofEvaluation:
  // The third argument names *this* object, so a forked child re-enters here and reads the same problem list.
  private val harness = new FofHarness("tptp-fof-fo-noeq-thm.txt", "TPTP_FOF_LIST",
    "lisa.automation.superposition.bench.FofEvaluation")

  // `allProblems`/`sample` are the only members referenced outside the harness (tests, other harnesses); see
  // [[FofHarness]] for their contract.
  def allProblems: Vector[String] = harness.allProblems
  def sample(n: Int = 100, seed: Long = 42): Vector[String] = harness.sample(n, seed)
  def main(args: Array[String]): Unit = harness.main(args)
