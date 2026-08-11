package lisa.automation.superposition

import org.scalatest.funsuite.AnyFunSuite

import lisa.tptp.Problem
import lisa.tptp.KernelParser.{problemToKernel, strictMapAtom, strictMapTerm, strictMapVariable}

/**
 * Baseline test: the prover ([[Bridge.solve]]) on a sample of easy TPTP `SYN` problems.
 *
 * These are small, self-contained, no-equality, unsatisfiable clausal problems (SPC
 * `CNF_UNS_EPR_NEQ_HRN`) — exactly the fragment Phase-1 ordered resolution handles. They are located
 * via the `TPTP` environment variable (pointing at the TPTP root, e.g. `.../TPTP-v9.2.1`); if it is
 * unset the tests are **cancelled**, not failed, so the suite stays portable.
 */
class SynBaselineTest extends AnyFunSuite:

  // Resolved per test through [[TptpCorpus]], which warns loudly the first time the corpus is missing.

  // 20 small self-contained no-equality unsatisfiable SYN clausal problems (2-5 clauses each),
  // all refutable by ordered resolution + factoring (no paramodulation needed).
  private val problems: List[String] = List(
    "SYN048-1.p", "SYN064-1.p", "SYN073-1.p", "SYN339-1.p", "SYN340-1.p",
    "SYN341-1.p", "SYN731-1.p", "SYN034-1.p", "SYN035-1.p", "SYN049-1.p",
    "SYN063-2.p", "SYN081-1.p", "SYN333-1.p", "SYN338-1.p", "SYN343-1.p",
    "SYN727-1.p", "SYN033-1.p", "SYN051-1.p", "SYN079-1.p", "SYN315-1.p"
  )

  problems.foreach { name =>
    test(s"SYN baseline: $name is refuted") {
      val f = new java.io.File(TptpCorpus.subdirOrCancel("Problems/SYN", "the SYN baseline"), name)
      assume(f.exists, s"$f not found")
      val problem: Problem = problemToKernel(f)(using (strictMapAtom, strictMapTerm, strictMapVariable))
      assert(Bridge.solveTPTPProblem(problem, maxGiven = 50000).refuted)
    }
  }
