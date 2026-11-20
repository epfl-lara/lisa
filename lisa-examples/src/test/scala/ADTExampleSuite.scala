import lisa.SetTheoryLibrary
import org.scalatest.funsuite.AnyFunSuite

/**
 * Executes the public ADT example and checks its generated LCF proofs.
 */
class ADTExampleSuite extends AnyFunSuite:
  test("the unchanged ADT example constructs checked proofs without admissions"):
    val _ = ADTExamples.Example.repeatTyping
    val proofs = SetTheoryLibrary.theorems.all.filter { theorem =>
      val source = theorem.file.value.replace('\\', '/')
      source.endsWith("/ADTExample.scala") || source.contains("/src/main/scala/lisa/maths/SetTheory/Types/ADT/")
    }.toSeq
    assert(proofs.nonEmpty)
    for theorem <- proofs do
      withClue(s"${theorem.fullName.value}: ") {
        assert(theorem.errors.isEmpty, theorem.errors.mkString("\n"))
        assert(!theorem.kernel.usesSorry)
      }
