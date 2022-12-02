package lisa.utils
import lisa.utils.Helpers.show

import java.io.PrintWriter
import java.io.StringWriter

abstract class OutputManager {
  given OutputManager = this

  def output(s: String): Unit = stringWriter.write(s + "\n")
  def output(s: String, color: String): Unit = stringWriter.write(color + s + "\n" + Console.BLACK)
  val stringWriter: StringWriter

  def finishOutput(exception: Exception): Nothing

  def lisaThrow(le: LisaException): Nothing =
    le match {
      case ule: UserLisaException =>
        ule match {
          case tacticException: UserLisaException.UnapplicableProofTactic =>
            val start = tacticException.getStackTrace.indexWhere(elem => {
              !elem.getClassName.contains(tacticException.tactic.name)
            }) + 1
            tacticException.setStackTrace(tacticException.getStackTrace.take(start))
            output(tacticException.showError)
            finishOutput(tacticException)
          case exception: UserLisaException.UserParsingException => finishOutput(le)
          case _ => finishOutput(le)
        }

      case e: LisaException.InvalidKernelJustificationComputation =>
        output(ProofPrinter.prettyProof(e.proof))
        e.underlying.show
        finishOutput(e)

    }

  def log(e: Exception): Unit = {
    stringWriter.write("\n[" + Console.RED + "Error" + Console.BLACK + "]")
    e.printStackTrace(PrintWriter(stringWriter))
    output(Console.BLACK)
  }
}
