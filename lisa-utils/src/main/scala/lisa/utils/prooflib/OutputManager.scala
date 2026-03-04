package lisa.utils.prooflib

import lisa.utils.KernelHelpers._
import lisa.utils._

import java.io.PrintWriter
import java.io.Writer

abstract class OutputManager {

  given OutputManager = this

  def output(s: String): Unit = stringWriter.write(s + "\n")
  def output(s: String, color: String): Unit = stringWriter.write(Console.RESET + color + s + "\n" + Console.RESET)
  val stringWriter: Writer

  def finishOutput(exception: Exception): Nothing

  def lisaThrow(le: LisaException): Nothing =
    le match {
      case ule: UserLisaException =>
        ule.fixTrace()
        output(ule.showError)
        finishOutput(ule)

      case e: LisaException.InvalidKernelJustificationComputation =>
        e.proof match {
          case Some(value) => output(lisa.utils.prooflib.ProofPrinter.prettyProof(value))
          case None => ()
        }
        output(e.underlying.repr)
        finishOutput(e)

    }

  def log(e: Exception): Unit = {
    stringWriter.write("\n[" + Console.RED + "Error" + Console.RESET + "] ")
    e.printStackTrace(PrintWriter(stringWriter))
    output(Console.RESET)
  }

}
object OutputManager {
  def RED(s: String): String = Console.RED + s + Console.RESET
  def GREEN(s: String): String = Console.GREEN + s + Console.RESET
  def BLUE(s: String): String = Console.BLUE + s + Console.RESET
  def YELLOW(s: String): String = Console.YELLOW + s + Console.RESET
  def CYAN(s: String): String = Console.CYAN + s + Console.RESET
  def MAGENTA(s: String): String = Console.MAGENTA + s + Console.RESET

  def WARNING(s: String): String = Console.YELLOW + "⚠ " + s + Console.RESET
}
