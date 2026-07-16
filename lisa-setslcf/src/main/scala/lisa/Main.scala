package lisa

import lisa.SetTheoryLibrary
import lisa.utilcfs.prooflib.OutputManager

/**
 * The parent trait of all theory files containing mathematical development
 */
trait Main {

  // SetTheoryLibrary defines more specific versions of === and ≠, so we hide
  // the generic ones
  export lisa.utilcfs.fol.FOL.{≠ as _, === as _, *, given}
  export SetTheoryLibrary.{section as _, given, _}
  export lisa.utilcfs.prooflib.Exports.*

  given OutputManager = OutputManager.stdout

  def section(name: String)(using sourcecode.File): Unit =
    SetTheoryLibrary.section(name)

  def main(args: Array[String]): Unit = ()

}
