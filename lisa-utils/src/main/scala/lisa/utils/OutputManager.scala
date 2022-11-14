package lisa.utils
import lisa.utils.Helpers.show

abstract class OutputManager {
  given OutputManager = this

  def output(s: String): Unit

  def finishOutput(t:Throwable): Nothing

  def lisaThrow(le: LisaException): Nothing = le match {
    case e: LisaException.InvalidKernelJustificationComputation =>
      output(ProofPrinter.prettyProof(e.proof))
      e.underlying.show
      finishOutput(e)
  }
}
