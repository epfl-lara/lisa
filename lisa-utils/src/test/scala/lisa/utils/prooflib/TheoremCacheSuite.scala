package lisa.utils.prooflib

import lisa.kernel.proof.{RunningTheory, SCProofChecker}
import lisa.utils.fol.FOL.{*, given}
import lisa.utils.prooflib.BasicStepTactic.{Hypothesis, Restate}
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

  test("cache the final restatement, not just an equivalent conclusion"):
    withNames: (name, _) =>
      val declared = p |- !(!p)
      def build(lib: CachedLibrary)(onCompute: => Unit): lib.THM =
        import lib.*
        Theorem(using summon[OutputManager], sourcecode.FullName(name))(declared):
          onCompute
          have(p |- p) by Hypothesis

      val cold = build(new CachedLibrary)(())
      assert(cold.kernelProof.get.conclusion == declared.underlying)
      val warm = build(new CachedLibrary)(fail("recomputed the restated proof"))
      assert(warm.highProof.isEmpty)
      assert(warm.kernelProof.get.conclusion == declared.underlying)
      assert(SCProofChecker.checkSCProof(warm.kernelProof.get).isValid)

  test("reload a generated dependency without executing the consuming proof body"):
    withNames: (childName, parentName) =>
      val cold = new CachedLibrary
      val goal = (p |- p).underlying
      val child = cold.THM.fromSCProof(
        p |- p, childName, cold.InternalStatement,
        () => lisa.kernel.proof.SCProof(lisa.kernel.proof.SequentCalculus.Hypothesis(goal, p.underlying)), Nil
      )
      locally:
        import cold.{*, given}
        Theorem(using summon[OutputManager], sourcecode.FullName(parentName))(p |- p):
          have(thesis) by Restate.from(child)

      val files = for name <- Seq(childName, parentName); suffix <- Seq(".proof", ".trees") yield Path.of("cache", name + suffix)
      val before = files.map(Files.getLastModifiedTime(_))
      val warm = new CachedLibrary
      val parent = theorem(warm, parentName, p)(fail("recomputed the parent"))
      assert(parent.highProof.isEmpty)
      assert(warm.theory.getTheorem(childName).nonEmpty)
      assert(files.map(Files.getLastModifiedTime(_)) == before)
      assert(SCProofChecker.checkSCProof(parent.kernelProof.get).isValid)

      val reloaded = warm.THM.fromSCProof(
        p |- p, childName, warm.InternalStatement, () => fail("recomputed generated proof"), Nil
      )
      assert(reloaded.kernelProof.get.conclusion == goal)

  test("reject a dependency that no longer proves the imported statement"):
    withNames: (childName, parentName) =>
      def child(lib: CachedLibrary, formula: Expr[Prop]): lib.THM =
        val axiom = lib.Axiom(using sourcecode.FullName(childName + ".axiom"))(formula)
        val statement = (Sequent(Set.empty, Set(formula))).underlying
        lib.THM.fromSCProof(
          axiom.statement, childName, lib.InternalStatement,
          () => lisa.kernel.proof.SCProof(IndexedSeq(lisa.kernel.proof.SequentCalculus.Restate(statement, -1)), IndexedSeq(statement)),
          List(axiom.innerJustification), List(axiom)
        )
      val cold = new CachedLibrary
      val dependency = child(cold, p)
      locally:
        import cold.{*, given}
        Theorem(using summon[OutputManager], sourcecode.FullName(parentName))(p):
          have(thesis) by Restate.from(dependency)
      child(new CachedLibrary, q)

      val warm = new RunningTheory
      warm.addAxiom(childName + ".axiom", q.underlying)
      val loaded = lisa.utils.Serialization.oneProofFromFile("cache/" + parentName, warm, Some(parentName -> dependency.statement.underlying))
      assert(loaded.isEmpty)
      assert(warm.getTheorem(parentName).isEmpty)

  test("reject cyclic cache dependencies without registering either theorem"):
    withNames: (first, second) =>
      val cold = new CachedLibrary
      val a = theorem(cold, first, p)(())
      val b = theorem(cold, second, p)(())
      val statement = (p |- p).underlying
      val proof = lisa.kernel.proof.SCProof(IndexedSeq(lisa.kernel.proof.SequentCalculus.Restate(statement, -1)), IndexedSeq(statement))
      lisa.utils.Serialization.thmsToFile("cache/" + first, cold.theory, List((first, proof, List((b.owner, b.innerJustification)))))
      lisa.utils.Serialization.thmsToFile("cache/" + second, cold.theory, List((second, proof, List((a.owner, a.innerJustification)))))
      val warm = new RunningTheory
      assert(lisa.utils.Serialization.oneProofFromFile("cache/" + first, warm).isEmpty)
      assert(warm.getTheorem(first).isEmpty)
      assert(warm.getTheorem(second).isEmpty)

  test("a string-hash collision cannot reuse a different generated statement"):
    withNames: (name, _) =>
      val a = Variable[Prop]("Aa")
      val b = Variable[Prop]("BB")
      assert(a.underlying.toString.hashCode == b.underlying.toString.hashCode)
      def build(lib: CachedLibrary, formula: Expr[Prop])(onCompute: => Unit): lib.THM =
        val statement = (formula |- formula).underlying
        lib.THM.fromSCProof(
          formula |- formula, name, lib.InternalStatement,
          () => {
            onCompute
            lisa.kernel.proof.SCProof(lisa.kernel.proof.SequentCalculus.Hypothesis(statement, formula.underlying))
          }, Nil
        )
      build(new CachedLibrary, a)(())
      var computed = false
      val replacement = build(new CachedLibrary, b) { computed = true }
      assert(computed)
      assert(replacement.kernelProof.get.conclusion == (b |- b).underlying)
