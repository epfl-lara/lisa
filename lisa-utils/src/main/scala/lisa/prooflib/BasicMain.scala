package lisa.prooflib

trait BasicMain {
  private val realOutput: String => Unit = println

  given om: OutputManager = new OutputManager {
    def finishOutput(exception: Exception): Nothing = {
      log(exception)
      main(Array[String]())
      sys.exit
    }
    val stringWriter: java.io.StringWriter = new java.io.StringWriter()
  }

  /**
   * This specific implementation make sure that what is "shown" in theory files is only printed for the one we run, and not for the whole library.
   */
  def main(args: Array[String]): Unit = {
    realOutput(om.stringWriter.toString)
  }

}
