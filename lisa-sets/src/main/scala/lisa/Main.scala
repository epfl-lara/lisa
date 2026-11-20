package lisa

import lisa.SetTheoryLibrary
import lisa.utils.prooflib.OutputManager

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
  private val defaultOutput = OutputManager.stdout
  given OutputManager = defaultOutput

  def section(name: String)(using sourcecode.File): Unit =
    SetTheoryLibrary.section(name)

  def main(args: Array[String]): Unit = ()

}
