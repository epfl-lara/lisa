package lisa.automation.superposition
package bench

/**
 * The third evaluation dataset: non-clausal (FOF), first-order, **equality-bearing**, arithmetic-free TPTP
 * **theorems** (`tptp-fof-fo-eq-thm.txt`) — the exact analog of the equality-free [[FofEvaluation]] set, selected
 * the very same way (by the TPTP `SPC` header) but with the equality classes `FOF_THM_{RFO,EPR}_{SEQ,PEQ}`
 * (**S**ome or **P**ure **EQ**uality) in place of `…_NEQ`. The `CSR` (SUMO commonsense) domain is excluded for
 * the same reason as there (giant numeric ontologies the parser mishandles / that blow the size budget), and only
 * `.p` problem files are kept (not TPTP's withdrawn `.rm` variants), leaving 5589 clean equality-bearing FO
 * theorems.
 *
 * This is the set that actually exercises the equality inferences (superposition, equality
 * resolution/factoring, demodulation) end-to-end, so the `equality` ablation is meaningful here (many refutations
 * need equality reasoning). Everything else — the pipeline, CLI, and output — is the shared [[FofHarness]]; see it
 * for the run modes and column meanings.
 */
object EqFofEvaluation:
  // The third argument names *this* object, so a forked child re-enters here and reads the same problem list.
  private val harness = new FofHarness("tptp-fof-fo-eq-thm.txt", "TPTP_FOF_EQ_LIST",
    "lisa.automation.superposition.bench.EqFofEvaluation")

  // `allProblems`/`sample` are the only members referenced outside the harness (tests, other harnesses); see
  // [[FofHarness]] for their contract.
  def allProblems: Vector[String] = harness.allProblems
  def sample(n: Int = 100, seed: Long = 42): Vector[String] = harness.sample(n, seed)
  def main(args: Array[String]): Unit = harness.main(args)
