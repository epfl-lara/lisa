import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent._
import java.util.concurrent.CancellationException
import java.io.File

import lisa.utils.tptp.*
import lisa.utils.tptp.KernelParser.*
import lisa.utils.tptp.KernelParser.getProblemInfos
import lisa.utils.tptp.ProblemGatherer.*
import lisa.utils.ProofsConverter.*
import lisa.kernel.proof.SCProof
import java.io.FileWriter
import lisa.kernel.proof.SequentCalculus.Sequent

object TPTPSolver extends lisa.Main {
  try {
    val spc = Seq("PRP", "FOF") // type of problems we want to extract and solve
    // val spc = Seq("PRP", "FOF", "CNF") // almost no CNF problems are solved by Tableau, TODO: investigate why

    // val d = new File(TPTPProblemPath)
    // val libraries = d.listFiles.filter(_.isDirectory)
    // val probfiles = libraries.flatMap(_.listFiles).filter(_.isFile)

    val d = new File(TPTPProblemPath + "SYN/")
    val probfiles = d.listFiles.filter(_.isFile)

    // We limit the execution time to solve each problem
    val timeoutTableau = .2.second
    val timeoutTautology = .2.second

    var problems = List[Problem]()
    var tableauProofs = List[SolverResult]()
    var tautologyProofs = List[SolverResult]()

    for ((probfile, i) <- probfiles.zipWithIndex) {
      // Progress bar
      if ((i + 1) % 10 == 0 || i + 1 == probfiles.size) {
        val pbarLength = 30
        var pbarContent = "=" * (((i + 1) * pbarLength) / probfiles.size)
        pbarContent += " " * (pbarLength - pbarContent.length)
        print("[" + pbarContent + "]")
        print(" -- " + (i + 1) + "/" + probfiles.size + " processed files")
        print(" -- " + problems.size + " extracted problems")
        print(" -- Tableau: " + tableauProofs.count(_.isInstanceOf[Solved]) + " solved")
        println(" -- Tautology: " + tautologyProofs.count(_.isInstanceOf[Solved]) + " solved")
      }

      // Try to extract the problem
      try {
        val md = getProblemInfos(probfile)
        if (md.spc.exists(spc.contains)) {
          val p = problemToKernel(probfile, md)
          problems = problems :+ p
          val seq = problemToSequent(p)

          // Attempting proof by Tableau
          tableauProofs = tableauProofs :+ solveProblem(p, timeoutTableau, Tableau.solve)

          // Attempting proof by Tautology
          def tautologySolver(s: lisa.utils.K.Sequent): Option[SCProof] = Tautology.solveSequent(s) match
            case Left(proof) => Some(proof)
            case _ => None
          tautologyProofs = tautologyProofs :+ solveProblem(p, timeoutTautology, tautologySolver)
        }
      } catch {
        case _ => ()
      }

    }
  } catch {
    case error: NullPointerException => println("You can download the tptp library at http://www.tptp.org/ and put it in main/resources")
  }
}

sealed trait SolverResult
case class Solved(proof: SCProof) extends SolverResult
case object Unsolved extends SolverResult
case object Timeout extends SolverResult
case object Error extends SolverResult

def solveProblem(problem: Problem, timeout: FiniteDuration, solver: Sequent => Option[SCProof]): SolverResult = {
  val seq = problemToSequent(problem)
  val (futureSolver, cancelSolver) = Future.interruptibly { solver(seq) }
  try
    Await.result(futureSolver, timeout) match
      case Some(proof) => Solved(proof)
      case None => Unsolved
  catch
    case e: TimeoutException =>
      cancelSolver()
      Timeout
    case _ =>
      cancelSolver()
      Error
}

def writeProof(problem: Problem, proof: SCProof, path: String): Unit = {
  // TODO
  val file = new File(path + problem.name + ".sc")
  val bw = new FileWriter(file)
  val proofCode = scproof2code(proof)
  bw.write(proof.toString)
  bw.close()
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
