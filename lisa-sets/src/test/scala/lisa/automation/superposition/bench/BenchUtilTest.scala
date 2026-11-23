package lisa.automation.superposition
package bench

import org.scalatest.funsuite.AnyFunSuite

import scala.util.Failure
import scala.util.Success

/**
 * Tests for [[BenchUtil.withTimeout]]'s handling of a worker that overruns its budget.
 *
 * Interruption on the JVM is cooperative, so "we asked it to stop" and "it stopped" are different facts. A
 * worker that ignores the request cannot be killed, so the contract is: wait a grace period, then give up.
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

  test("ordinary worker failures preserve the cause in Failure") {
    val error = new IllegalStateException("ordinary worker failure")
    assert(BenchUtil.withTimeout(30000L)(throw error) == Some(Failure(error)))
  }

  test("a fatal worker error escapes on the caller thread with its original cause") {
    val error = new LinkageError("incompatible library")
    assert(intercept[LinkageError](BenchUtil.withTimeout(30000L)(throw error)) eq error)
  }

  test("a worker interrupted before the deadline propagates its interruption") {
    val error = new InterruptedException("external cancellation")
    assert(intercept[InterruptedException](BenchUtil.withTimeout(30000L)(throw error)) eq error)
  }

  test("an overrun returns None whether or not the worker stops") {
    val cooperative = BenchUtil.withTimeout(50L)(Thread.sleep(60000L))
    val stubborn = BenchUtil.withTimeout(50L)(spinIgnoringInterrupts(4000L))
    assert(cooperative.isEmpty && stubborn.isEmpty)
  }

  test("a cooperative overrun is not reported as an error") {
    assert(BenchUtil.withTimeout(50L)(Thread.sleep(60000L)).isEmpty)
  }
