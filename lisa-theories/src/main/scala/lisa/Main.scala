package lisa

import lisa.utils.OutputManager

/**
 * The parent trait of all theory files containing mathematical development
 */
trait Main {
  export lisa.settheory.SetTheoryLibrary.{_, given}

  private val realOutput: String => Unit = println
  private var outString: List[String] = List()
  private val lineBreak = "\n"

  given om:OutputManager = new OutputManager {
    override val output: String => Unit = s => outString = lineBreak :: s :: outString
    override val finishOutput: Throwable => Nothing = e => {
      main(Array[String]())
      throw e
    }
  }

  /**
   * This specific implementation make sure that what is "shown" in theory files is only printed for the one we run, and not for the whole library.
   */
  def main(args: Array[String]): Unit = {
    realOutput(outString.reverse.mkString(""))
  }

}
