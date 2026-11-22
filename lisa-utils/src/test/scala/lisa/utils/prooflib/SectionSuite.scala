package lisa.utils.prooflib

import org.scalatest.funsuite.AnyFunSuite

/**
 * Checks section numbering by source file, independently of imported developments and output managers.
 */
class SectionSuite extends AnyFunSuite:
  test("interleaved source files maintain independent section counters"):
    val library = new Library
    val first = new StringOutputManager
    val second = new StringOutputManager
    val firstFile = sourcecode.File("first/Example.scala")
    val secondFile = sourcecode.File("second/Example.scala")
    library.section("First introduction")(using first, firstFile)
    library.section("Second introduction")(using second, secondFile)
    library.section("First results")(using first, firstFile)
    library.section("Second results")(using second, secondFile)
    assert(
      first.toString.linesIterator.toSeq == Seq(
        OutputManager.BLUE("Section 1: First introduction"),
        OutputManager.BLUE("Section 2: First results")
      )
    )
    assert(
      second.toString.linesIterator.toSeq == Seq(
        OutputManager.BLUE("Section 1: Second introduction"),
        OutputManager.BLUE("Section 2: Second results")
      )
    )

  test("numbering belongs to the source file and library, not the output manager"):
    val library = new Library
    val first = new StringOutputManager
    val second = new StringOutputManager
    library.section("Introduction")(using first, sourcecode.File("Example.scala"))
    library.section("Results")(using second, sourcecode.File("Example.scala"))
    assert(second.toString.contains("Section 2: Results"))
    val otherLibrary = new Library
    otherLibrary.section("Independent introduction")(using second, sourcecode.File("Example.scala"))
    assert(second.toString.contains("Section 1: Independent introduction"))
