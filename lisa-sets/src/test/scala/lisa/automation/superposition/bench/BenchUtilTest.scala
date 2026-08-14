package lisa.automation.superposition
package bench

import org.scalatest.funsuite.AnyFunSuite
import scala.util.Success

/**
 * Tests for [[BenchUtil.withTimeout]]'s handling of a worker that overruns its budget.
 *
 * Interruption on the JVM is cooperative, so "we asked it to stop" and "it stopped" are different facts. A
 * worker that ignores the request keeps burning CPU and holding its heap (a saturation's passive set can be
 * millions of clauses) for the remainder of the run, and every problem measured afterwards is timed against
 * a machine that is busy and nearly out of memory. That is not hypothetical: it turned a 44-refutation
 * corpus run into a 20-refutation one, reporting problems that refute standalone in 6 ms as `TIMEOUT`.
 *
 * Nothing can kill such a thread (`Thread.stop` is gone), so the contract is: wait a grace period, then
 * *count* it, so the harnesses can say the run is contaminated instead of reporting the numbers as fact.
 */
class BenchUtilTest extends AnyFunSuite:

  /** Spin without ever checking the interrupt flag, so only the clock stops us. Bounded so the test does not
    * leave a thread running for the rest of the JVM's life. */
  private def spinIgnoringInterrupts(ms: Long): Unit =
    val until = System.nanoTime() + ms * 1000000L
    while System.nanoTime() < until do ()

  test("a body that finishes in time returns its result and is not counted") {
    BenchUtil.resetAbandoned()
    assert(BenchUtil.withTimeout(30000L)(6 * 7) == Some(Success(42)))
    assert(BenchUtil.abandonedWorkers == 0)
    assert(BenchUtil.contaminationWarning.isEmpty)
  }

  test("a worker that respects its interrupt times out but is NOT counted as abandoned") {
    BenchUtil.resetAbandoned()
    // `Thread.sleep` throws on interrupt, so this unwinds well inside the grace period.
    val r = BenchUtil.withTimeout(50L)(Thread.sleep(60000L))
    assert(r.isEmpty, "an overrun must report no result")
    assert(BenchUtil.abandonedWorkers == 0, "a worker that stopped when asked is not contamination")
    assert(BenchUtil.contaminationWarning.isEmpty)
  }

  test("a worker that ignores its interrupt is counted, and the run is reported contaminated") {
    BenchUtil.resetAbandoned()
    // Outlives the 2s grace period, so it is still running when `withTimeout` gives up.
    val r = BenchUtil.withTimeout(50L)(spinIgnoringInterrupts(4000L))
    assert(r.isEmpty)
    assert(BenchUtil.abandonedWorkers == 1, "an unstoppable worker must be counted")
    val w = BenchUtil.contaminationWarning
    assert(w.nonEmpty && w.contains("1 worker"), s"expected a warning naming one worker, got: $w")
    BenchUtil.resetAbandoned()
    assert(BenchUtil.contaminationWarning.isEmpty, "reset must clear the count for the next run")
  }

  // The distinction the whole mechanism turns on: an overrun is `None` either way, so a harness that only
  // looked at the return value could not tell the harmless case from the poisonous one.
  test("both overrun cases return None; only the count distinguishes them") {
    BenchUtil.resetAbandoned()
    val cooperative = BenchUtil.withTimeout(50L)(Thread.sleep(60000L))
    val after = BenchUtil.abandonedWorkers
    val stubborn = BenchUtil.withTimeout(50L)(spinIgnoringInterrupts(4000L))
    assert(cooperative.isEmpty && stubborn.isEmpty)
    assert(after == 0 && BenchUtil.abandonedWorkers == 1)
  }

  // A worker unwinding during the grace period stores `Failure(InterruptedException)`. Returning that would
  // reclassify every `HARD_TIMEOUT` as `ERROR(InterruptedException)` in the harness summaries.
  test("an interrupted worker's own exception does not leak out as a result") {
    BenchUtil.resetAbandoned()
    val r = BenchUtil.withTimeout(50L) {
      try Thread.sleep(60000L)
      catch case e: InterruptedException => throw new IllegalStateException("unwound")
    }
    assert(r.isEmpty, s"the budget was exceeded, so there is no result to report; got $r")
  }
