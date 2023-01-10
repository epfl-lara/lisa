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
        ule.fixTrace()
        ule match {
          case tacticException: UserLisaException.UnapplicableProofTactic =>
            output(tacticException.showError)
            finishOutput(tacticException)
          case defException: UserLisaException.UserInvalidDefinitionException =>
            output(defException.showError)
            finishOutput(defException)
          case parsingException: UserLisaException.UserParsingException =>
            output(parsingException.showError)
            finishOutput(parsingException)
          case _ =>
            output(ule.showError)
            finishOutput(ule)
        }

      case e: LisaException.InvalidKernelJustificationComputation =>
        e.proof match {
          case Some(value) => output(ProofPrinter.prettyProof(value))
          case None => ()
        }
        e.underlying.show
        finishOutput(e)

    }

  def log(e: Exception): Unit = {
    stringWriter.write("\n[" + Console.RED + "Error" + Console.BLACK + "]")
    e.printStackTrace(PrintWriter(stringWriter))
    output(Console.BLACK)
  }
}
