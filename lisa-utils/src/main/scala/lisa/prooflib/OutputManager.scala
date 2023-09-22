package lisa.prooflib

import lisa.utils.KernelHelpers.{_, given}
import lisa.utils.{_, given}

import java.io.PrintWriter
import java.io.StringWriter

abstract class OutputManager {

  given OutputManager = this

  def output(s: String): Unit = stringWriter.write(s + "\n")
  def output(s: String, color: String): Unit = stringWriter.write(Console.RESET + color + s + "\n" + Console.RESET)
  val stringWriter: StringWriter

  def finishOutput(exception: Exception): Nothing

  def lisaThrow(le: LisaException): Nothing =
    le match {
      case ule: UserLisaException =>
        ule.fixTrace()
        output(ule.showError)
        finishOutput(ule)

      case e: LisaException.InvalidKernelJustificationComputation =>
        e.proof match {
          case Some(value) => output(lisa.utils.ProofPrinter.prettyProof(value))
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
