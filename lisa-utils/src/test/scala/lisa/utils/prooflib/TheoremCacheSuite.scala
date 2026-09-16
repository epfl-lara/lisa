package lisa.utils.prooflib

import lisa.kernel.proof.{RunningTheory, SCProofChecker}
import lisa.utils.fol.FOL.{*, given}
import lisa.utils.prooflib.BasicStepTactic.Hypothesis
import org.scalatest.funsuite.AnyFunSuite

import java.nio.file.{Files, Path}
import java.util.UUID

class TheoremCacheSuite extends AnyFunSuite:
  private given OutputManager = new OutputManager:
    val stringWriter = new java.io.StringWriter
    def finishOutput(exception: Exception): Nothing = throw exception

  private class CachedLibrary extends Library:
    val theory = new RunningTheory
    withCache()

  private val p = Variable[Prop]("cache-p")
  private val q = Variable[Prop]("cache-q")

  private def theorem(lib: CachedLibrary, name: String, formula: Expr[Prop])(onCompute: => Unit): lib.THM =
    import lib.*
    Theorem(using summon[OutputManager], sourcecode.FullName(name))(formula |- formula):
      onCompute
      have(thesis) by Hypothesis

  private def withNames(test: (String, String) => Unit): Unit =
    val prefix = "cache-test-" + UUID.randomUUID().toString
    val first = s"$prefix.First.membership"
    val second = s"$prefix.Second.membership"
    try test(first, second)
    finally
      for name <- Seq(first, second); extension <- Seq(".proof", ".trees") do
        Files.deleteIfExists(Path.of("cache", name + extension))

  test("same short names keep separate cache files and kernel identities"):
    withNames: (first, second) =>
      val cold = new CachedLibrary
      theorem(cold, first, p)(())
      theorem(cold, second, q)(())
      assert(cold.theory.getTheorem(first).nonEmpty)
      assert(cold.theory.getTheorem(second).nonEmpty)

      val warm = new CachedLibrary
      val a = theorem(warm, first, p)(fail("recomputed first cached proof"))
      val b = theorem(warm, second, q)(fail("recomputed second cached proof"))
      assert(a.statement == (p |- p))
      assert(b.statement == (q |- q))
      assert(a.highProof.isEmpty)
      assert(b.highProof.isEmpty)
      assert(SCProofChecker.checkSCProof(a.kernelProof.get).isValid)
      assert(SCProofChecker.checkSCProof(b.kernelProof.get).isValid)

  test("a changed statement rejects the stale cache and computes its own proof"):
    withNames: (name, _) =>
      theorem(new CachedLibrary, name, p)(())
      val warm = new CachedLibrary
      var computed = false
      val changed = theorem(warm, name, q) { computed = true }
      assert(computed)
      assert(changed.statement == (q |- q))
      assert(warm.theory.getTheorem(name).get.proposition == changed.statement.underlying)
      assert(changed.highProof.nonEmpty)

  test("a cache with the wrong name is rejected before registration"):
    withNames: (first, second) =>
      theorem(new CachedLibrary, first, p)(())
      val theory = new RunningTheory
      val result = lisa.utils.Serialization.oneProofFromFile(
        "cache/" + first,
        theory,
        Some(second -> (p |- p).underlying)
      )
      assert(result.isEmpty)
      assert(theory.getTheorem(first).isEmpty)
      assert(theory.getTheorem(second).isEmpty)
