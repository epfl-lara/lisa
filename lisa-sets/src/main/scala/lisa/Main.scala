package lisa

import lisa.SetTheoryLibrary
import lisa.utils.prooflib.OutputManager
import lisa.utils.prooflib.StringOutputManager

/**
 * The parent trait of all theory files containing mathematical development
 */
trait Main {

  // SetTheoryLibrary defines more specific versions of === and ≠, so we hide
  // the generic ones
  export lisa.utils.fol.FOL.{≠ as _, === as _, *, given}
  export SetTheoryLibrary.{section as _, given, _}
  export lisa.utils.prooflib.Exports.*

  // An eager initializer also initializes exported object fields on Scala 3.10.
  private val defaultOutput = new StringOutputManager
  given OutputManager = new OutputManager:
    def output(message: String): Unit = defaultOutput.output(message)
    override def error(message: String): Unit = println(message)

  def section(name: String)(using sourcecode.File): Unit =
    SetTheoryLibrary.section(name)

  // Errors print immediately; only the selected main prints its buffered declarations.
  def main(args: Array[String]): Unit =
    print(defaultOutput.toString)
    if SetTheoryLibrary.theorems.all.exists(_.errors.nonEmpty) then sys.exit(1)

}
