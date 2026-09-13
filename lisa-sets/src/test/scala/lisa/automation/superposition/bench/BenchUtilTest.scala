package lisa.automation.superposition
package bench

import org.scalatest.funsuite.AnyFunSuite

import scala.util.Success

/**
 * Tests for [[BenchUtil.withTimeout]]'s handling of a worker that overruns its budget.
 *
 * Interruption on the JVM is cooperative, so "we asked it to stop" and "it stopped" are different facts. A
 * worker that ignores the request keeps burning CPU and holding its heap, and nothing can kill it. The
 * contract is therefore: wait a grace period, then give up on it and return, which is why the cluster runs
 * one problem per forked JVM rather than relying on this at all.
 */
class BenchUtilTest extends AnyFunSuite:

  /**
   * Spin without ever checking the interrupt flag, so only the clock stops us. Bounded so the test does not
   * leave a thread running for the rest of the JVM's life.
   */
  private def spinIgnoringInterrupts(ms: Long): Unit =
    val until = System.nanoTime() + ms * 1000000L
    while System.nanoTime() < until do ()

  test("a body that finishes in time returns its result") {
    assert(BenchUtil.withTimeout(30000L)(6 * 7) == Some(Success(42)))
  }

  // Both overruns are `None`: the one that unwound when asked, and the one that did not.
  test("an overrun returns None whether or not the worker stops") {
    val cooperative = BenchUtil.withTimeout(50L)(Thread.sleep(60000L))
    val stubborn = BenchUtil.withTimeout(50L)(spinIgnoringInterrupts(4000L))
    assert(cooperative.isEmpty && stubborn.isEmpty)
  }

  // A worker unwinding during the grace period stores `Failure(InterruptedException)`. Returning that would
  // reclassify every `HARD_TIMEOUT` as `ERROR(InterruptedException)` in the harness summaries.
  test("a cooperative overrun is not reported as an error") {
    assert(BenchUtil.withTimeout(50L)(Thread.sleep(60000L)).isEmpty)
  }
