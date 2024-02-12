import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent._
import java.util.concurrent.CancellationException

import lisa.utils.tptp.Example.*
import lisa.utils.tptp.KernelParser.annotatedFormulaToKernel
import lisa.utils.tptp.KernelParser.parseToKernel
import lisa.utils.tptp.KernelParser.problemToSequent
import lisa.utils.tptp.ProblemGatherer.getPRPproblems
import lisa.utils.ProofsConverter.*

object TPTPSolver extends lisa.Main {
  try {
    println("Fetching problems from TPTP library...")
    val probs = getPRPproblems

    println("Number of problems found: " + probs.size)

    // We limit the execution time to solve each problem
    val timeoutTableau = 1.second
    val timeoutTautology = 1.second

    var tableauProofs = List[Option[SCProof]]()
    var tautologyProofs = List[Option[SCProof]]()

    for ((p, i) <- probs.zipWithIndex) {
      // Progress bar
      if ((i + 1) % 10 == 0 || i + 1 == probs.size) {
        val pbarLength = 30
        var pbarContent = "=" * (((i + 1) * pbarLength) / probs.size)
        pbarContent += " " * (pbarLength - pbarContent.length)
        print("[" + pbarContent + "]")
        print(" -- Processed " + (i + 1) + "/" + probs.size)
        print(" -- " + tableauProofs.count(_.isDefined) + " solved by Tableau")
        println(" -- " + tautologyProofs.count(_.isDefined) + " solved by Tautology")
      }

      val seq = problemToSequent(p)

      // Attempting proof by Tableau
      val (futureTableau, cancelTableau) = Future.interruptibly { Tableau.solve(seq) }
      tableauProofs = tableauProofs :+ (
        try Await.result(futureTableau, timeoutTableau)
        catch
          case _ =>
            cancelTableau()
            None
      )

      // Attempting proof by Tautology
      val (futureTautology, cancelTautology) = Future.interruptibly {
        Tautology.solveSequent(seq) match
          case Left(proof) => Some(proof)
          case _ => None
      }
      tautologyProofs = tautologyProofs :+ (
        try Await.result(futureTautology, timeoutTautology)
        catch
          case _ =>
            cancelTautology()
            None
      )
    }
  } catch {
    case error: NullPointerException => println("You can download the tptp library at http://www.tptp.org/ and put it in main/resources")
  }
}

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
        // t.interrupt()
        t.stop()
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
