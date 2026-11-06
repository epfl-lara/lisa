package lisa.hol

import java.io.ByteArrayOutputStream
import java.nio.file.{Files, Path}
import lisa.hol.extractor.*
import org.scalatest.funsuite.AnyFunSuite

class PreprocessingSuite extends AnyFunSuite:
  test("retain startup preprocessing settings after properties change"):
    val enabled = Config.precomputeLemmas
    val key = "lisa.hol.precomputeLemmas"
    val previous = sys.props.get(key)
    try
      sys.props(key) = (!enabled).toString
      assert(Config.precomputeLemmas == enabled)
    finally
      previous match
        case Some(value) => sys.props(key) = value
        case None => sys.props.remove(key)

  test("import with optional preprocessing and report its cost before reconstruction"):
    assert(Config.proofCacheMode == "local")
    val directory = Files.createTempDirectory("scp-preprocessing")
    val prefix = directory.resolve("trace").toString
    val paths = Seq("proofs", "theorems", "names").map(suffix => Path.of(s"$prefix.$suffix"))
    val variable = "v(preprocessing_p)(c[bool][])"
    val equalityType = "c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]"
    val equality = s"C(C(c(=)($equalityType))($variable))($variable)"
    val proofs = Seq(
      ProofLine(1000, REFL(variable)), ProofLine(1001, TRANS(1000, 1000)),
      ProofLine(1003, TRANS(1001, 1001)), ProofLine(1007, TRANS(1001, 1003))
    )
    val names = Seq(TheoremRef(1003, s"preprocessing_${Config.precomputeLemmas}_first"), TheoremRef(1007, s"preprocessing_${Config.precomputeLemmas}_second"))
    try
      Files.writeString(paths(0), proofs.map(upickle.default.write(_)).mkString("\n"))
      Files.writeString(paths(1), proofs.map(record => upickle.default.write(TheoremStatement(record.id, RawSequent(Nil, equality)))).mkString("\n"))
      Files.writeString(paths(2), names.map(upickle.default.write(_)).mkString("\n"))
      val output = new ByteArrayOutputStream
      var preprocessing = Option.empty[LemmaSelection.Timing]
      val timings = Console.withOut(output):
        Import.importFromPrefix(prefix, 2, onPreprocessing = timing => {
          assert(!output.toString.contains("Last theorem"))
          preprocessing = Some(timing)
        })
      val measured = preprocessing.get
      assert(measured.enabled == Config.precomputeLemmas)
      assert(measured.selectedLemmas == (if Config.precomputeLemmas then 1 else 0))
      assert(measured.elapsedNanos >= 0)
      assert(Config.precomputeLemmas || measured.elapsedNanos == 0)
      assert(timings.forall(_.succeeded))
      assert(timings.last.totalSteps == (if Config.precomputeLemmas then 4 else 6))
      assert(output.toString.linesIterator.count(_.startsWith("HOL_PREPROCESSING_METRICS ")) == 1)
      for ref <- names do
        val theorem = lisa.SetTheoryLibrary.theory.getTheorem(s"Import.${ref.name.replace("_", "⑪")}").get
        assert(!theorem.withSorry)
    finally
      paths.foreach(Files.deleteIfExists)
      Files.deleteIfExists(directory)
