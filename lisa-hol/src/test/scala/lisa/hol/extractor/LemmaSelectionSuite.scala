package lisa.hol.extractor

import java.nio.file.Files
import org.scalatest.funsuite.AnyFunSuite

class LemmaSelectionSuite extends AnyFunSuite:
  test("report disabled preprocessing without opening the proof file"):
    val output = new java.io.ByteArrayOutputStream
    var measured = Option.empty[LemmaSelection.Timing]
    val (result, timing) = Console.withOut(output):
      LemmaSelection.prepare(new java.io.File("missing-lemma-trace"), Set(3L), false)(value => measured = Some(value))
    assert(result == LemmaSelection.Result(Set.empty, 0, 0))
    assert(measured.contains(timing))
    assert(timing == LemmaSelection.Timing(false, 0L, 0, 0, 0))
    assert(output.toString.linesIterator.count(_.startsWith("HOL_PREPROCESSING_METRICS ")) == 1)

  private def analyze(records: Seq[ProofLine], roots: Set[Long]): LemmaSelection.Result =
    val file = Files.createTempFile("lemma-selection", ".proofs")
    try
      Files.writeString(file, records.map(upickle.default.write(_)).mkString("\n"))
      LemmaSelection.analyze(file.toFile, roots)
    finally Files.delete(file)

  test("cut at two owners, not at repeated edges within one owner"):
    val records = Seq(ProofLine(0, REFL("unparsed")), ProofLine(1, TRANS(0, 0)), ProofLine(3, TRANS(1, 1)), ProofLine(7, TRANS(1, 3)))
    assert(analyze(records, Set(7L)).ids.isEmpty)
    val shared = analyze(records, Set(3L, 7L))
    assert(shared.ids == Set(1L))
    assert(shared.records == 4 && shared.reachable == 4)

  test("named roots are already boundaries and aliases do not add owners"):
    val records = Seq(ProofLine(0, REFL("unparsed")), ProofLine(1, TRANS(0, 0)), ProofLine(3, TRANS(1, 1)))
    assert(analyze(records, Set(1L, 3L)).ids.isEmpty)

  test("include definition witnesses as separate contexts"):
    val records = Seq(ProofLine(0, REFL("unparsed")), ProofLine(1, TYPE_DEFINITION(0, "unparsed", "unused")), ProofLine(3, TRANS(0, 0)))
    assert(analyze(records, Set(3L)).ids == Set(0L))

  test("ignore unreachable sharing and stop at the requested prefix"):
    val records = Seq(ProofLine(0, REFL("unparsed")), ProofLine(2, TRANS(0, 0)), ProofLine(4, REFL("unparsed")), ProofLine(7, TRANS(6, 6)))
    val result = analyze(records, Set(4L))
    assert(result.ids.isEmpty && result.records == 3 && result.reachable == 1)

  test("preserve sparse IDs beyond exact Double range"):
    val id = 9007199254740993L
    val records = Seq(ProofLine(id, REFL("unparsed")), ProofLine(id + 1, TRANS(id, id)), ProofLine(id + 2, TRANS(id, id)))
    assert(analyze(records, Set(id + 1, id + 2)).ids == Set(id))

  test("reject missing roots and premises, forward references and duplicate IDs"):
    val invalid = Seq(
      Seq(ProofLine(0, REFL("unparsed"))) -> Set(1L),
      Seq(ProofLine(2, TRANS(0, 0))) -> Set(2L),
      Seq(ProofLine(0, TRANS(1, 1)), ProofLine(1, REFL("unparsed"))) -> Set(1L),
      Seq(ProofLine(0, REFL("unparsed")), ProofLine(0, REFL("unparsed")), ProofLine(1, REFL("unparsed"))) -> Set(1L)
    )
    for (records, roots) <- invalid do
      assertThrows[IllegalArgumentException](analyze(records, roots))

  test("empty selection does not scan the proof file"):
    assert(LemmaSelection.analyze(new java.io.File("missing-lemma-trace"), Set.empty) == LemmaSelection.Result(Set.empty, 0, 0))

  test("time selection independently of the reporting callback"):
    val file = Files.createTempFile("lemma-timing", ".proofs")
    try
      Files.writeString(file, upickle.default.write(ProofLine(3, REFL("unparsed"))))
      var measured = Option.empty[LemmaSelection.Timing]
      val (result, timing) = Console.withOut(new java.io.ByteArrayOutputStream):
        LemmaSelection.prepare(file.toFile, Set(3L), true)(value => measured = Some(value))
      assert(measured.contains(timing))
      assert(result.records == 1 && timing.records == 1 && timing.reachable == 1)
      assert(timing.enabled && timing.elapsedNanos > 0 && timing.elapsedSeconds > 0)
      assert(timing.selectedLemmas == result.ids.size)
    finally Files.delete(file)

  test("selected boundaries give one reconstruction per reachable node with local memoization"):
    val random = new scala.util.Random(42)
    for _ <- 0 until 30 do
      val records = Vector.tabulate(40): node =>
        val step =
          if node == 0 || random.nextInt(4) == 0 then REFL("unparsed")
          else TRANS(random.nextInt(node).toLong, random.nextInt(node).toLong)
        ProofLine(node.toLong, step)
      val roots = Set(25L, 33L, 39L)
      val result = analyze(records, roots)
      val boundaries = roots ++ result.ids
      val counts = Array.fill(records.size)(0)
      for root <- boundaries do
        val local = scala.collection.mutable.Set.empty[Long]
        def visit(id: Long): Unit =
          if (id == root || !boundaries(id)) && local.add(id) then
            counts(id.toInt) += 1
            records(id.toInt).step match
              case TRANS(first, second) => visit(first); visit(second)
              case _ => ()
        visit(root)
      assert(counts.forall(_ <= 1))
      assert(counts.count(_ == 1) == result.reachable)
