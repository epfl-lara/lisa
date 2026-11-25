package lisa.maths.SetTheory.Types.ADT

import lisa.SetTheoryLibrary
import lisa.maths.SetTheory.Cardinal.UniverseRank
import lisa.maths.SetTheory.Functions.Sigma
import org.scalatest.funsuite.AnyFunSuite

/**
 * Executes the shared ADT proofs, including lemmas not forced by a small declaration.
 */
class ProofInitializationSuite extends AnyFunSuite:
  test("initialize height and recursion proofs without errors or admissions"):
    height.proofs.ProofsInitialization.initialize()
    recursion.proofs.ProofsInitialization.initialize()
    val generated = SetTheoryLibrary.theorems.all.filter(_.file.value.replace('\\', '/').contains("/src/main/scala/lisa/maths/SetTheory/Types/ADT/")).toSeq
    assert(generated.nonEmpty)
    for theorem <- generated do
      withClue(s"${theorem.fullName.value}: ") {
        assert(theorem.errors.isEmpty, theorem.errors.mkString("\n"))
        assert(!theorem.kernel.usesSorry)
      }

  test("execute the repaired dependent-sum and universe-level proofs"):
    for theorem <- Seq(Sigma.membership, UniverseRank.levelIsOrdinal) do
      assert(theorem.errors.isEmpty, theorem.errors.mkString("\n"))
      assert(!theorem.kernel.usesSorry)
