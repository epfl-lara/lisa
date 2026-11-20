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
  given OutputManager = defaultOutput

  def section(name: String)(using sourcecode.File): Unit =
    SetTheoryLibrary.section(name)

  // Imported developments keep their output buffered; only the selected main prints.
  def main(args: Array[String]): Unit = print(defaultOutput.toString)

}
