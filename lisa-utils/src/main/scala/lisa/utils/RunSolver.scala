package lisa.utils

import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent._
import java.util.concurrent.CancellationException

import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.Sequent

object RunSolver {
  sealed trait SolverResult
  case class Solved(proof: SCProof) extends SolverResult
  case object Unsolved extends SolverResult
  case object Timeout extends SolverResult
  case class SolverThrow(t: Throwable) extends SolverResult

  def proveSequent(sequent: Sequent, timeout: Duration, solver: Sequent => Option[SCProof]): SolverResult = {
    val (futureSolver, cancelSolver) = Future.interruptibly { solver(sequent) }
    try
      Await.result(futureSolver, timeout) match
        case Some(proof) => Solved(proof)
        case None => Unsolved
    catch
      case _: TimeoutException =>
        cancelSolver()
        Timeout
      case t: Throwable =>
        cancelSolver()
        SolverThrow(t)
  }

  // Class to handle future cancellation
  // Source: https://viktorklang.com/blog/Futures-in-Scala-protips-6.html
  final class Interrupt extends (() => Boolean) {
    // We need a state-machine to track the progress.
    // It can have the following states:
    // a null reference means execution has not started.
    // a Thread reference means that the execution has started but is not done.
    // a this reference means that it is already cancelled or is already too late.
    private[this] final var state: AnyRef = null

    /**
     * This is the signal to cancel the execution of the logic.
     * Returns whether the cancellation signal was successully issued or not.
     */
    override final def apply(): Boolean = this.synchronized {
      state match {
        case null =>
          state = this
          true
        case _: this.type => false
        case t: Thread =>
          state = this
          // def kill = t.interrupt() // ask nicely for interruption, but this requires cooperation from the thread (involves checking isInterrupted() regularly)
          @annotation.nowarn
          def kill = t.stop() // brutally kill the thread without asking, more portable but less "safe". I believe it's safe here because we don't share any resources with the thread.
          kill
          true
      }
    }

    // Initializes right before execution of logic and
    // allows to not run the logic at all if already cancelled.
    private[this] final def enter(): Boolean =
      this.synchronized {
        state match {
          case _: this.type => false
          case null =>
            state = Thread.currentThread
            true
        }
      }

    // Cleans up after the logic has executed
    // Prevents cancellation to occur "too late"
    private[this] final def exit(): Boolean =
      this.synchronized {
        state match {
          case _: this.type => false
          case t: Thread =>
            state = this
            true
        }
      }

    /**
     * Executes the suplied block of logic and returns the result.
     * Throws CancellationException if the block was interrupted.
     */
    def interruptibly[T](block: => T): T =
      if (enter()) {
        try block
        catch {
          case ie: InterruptedException => throw new CancellationException()
          case td: ThreadDeath => throw new CancellationException()
          case t: Throwable => throw t
        } finally {
          if (!exit() && Thread.interrupted())
            () // If we were interrupted and flag was not cleared
        }
      } else throw new CancellationException()
  }

  implicit class FutureInterrupt(val future: Future.type) extends AnyVal {
    def interruptibly[T](block: => T)(implicit ec: ExecutionContext): (Future[T], () => Boolean) = {
      val interrupt = new Interrupt()
      (Future(interrupt.interruptibly(block))(ec), interrupt)
    }
  }
}
