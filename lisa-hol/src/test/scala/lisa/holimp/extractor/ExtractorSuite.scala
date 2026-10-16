package lisa
package hol
package extractor

import java.nio.charset.StandardCharsets
import java.nio.file.Files

import org.scalatest.funsuite.AnyFunSuite

import core._
import core.Parser._

class ExtractorSuite extends AnyFunSuite:
  test("report invalid HOL syntax from public record decoders"):
    assertThrows[CouldNotParseException](InstPair("invalid", "v(p)(c[bool][])").toTermPair)
    assertThrows[CouldNotParseException](InstPair("v[A]", "invalid").toTypePair)
    assertThrows[CouldNotParseException](extractor.REFL("invalid").extract)
    assertThrows[CouldNotParseException](RawSequent(Nil, "invalid").extract)
    assertThrows[CouldNotParseException](parseAll("invalid", term(using _)).getDone)

  test("distinguish JSON syntax, incomplete records, and schema failures"):
    withFiles("""{"id":0,"pr":{"step":"REFL","term":!}}""", ""): context =>
      assertThrows[ujson.ParsingFailedException](context.getProof(0))
    withFiles("""{"id":0,"pr":{"step":"REFL","term":"v(p)(c[bool][])"""", ""): context =>
      assertThrows[ujson.ParsingFailedException](context.getProof(0))
    withFiles("""{"id":0,"pr":{"step":"REFL","term":{}}}""", ""): context =>
      assertThrows[upickle.core.AbortException](context.getProof(0))

  test("propagate deferred read failures from caller-owned readers"):
    val failure = new java.io.IOException("Cannot read trace")
    val reader = new java.io.Reader:
      def read(chars: Array[Char], offset: Int, length: Int): Int = throw failure
      def close(): Unit = ()
    val context = JSONParser.toContext(reader, new java.io.StringReader(""))
    try assert(intercept[java.io.IOException](context.getProof(0)) eq failure)
    finally context.close()

  test("defer names decoding and propagate missing named proofs during iteration"):
    val directory = Files.createTempDirectory("lisa-hol-iterator-failures")
    val proof = directory.resolve("trace.proofs")
    val statement = directory.resolve("trace.theorems")
    val names = directory.resolve("trace.names")
    try
      val term = "v(p)(c[bool][])"
      Files.writeString(proof, upickle.default.write(ProofLine(0, extractor.REFL(term))))
      Files.writeString(statement, upickle.default.write(TheoremStatement(0, RawSequent(Nil, term))))
      Files.writeString(names, """{"id":0,"nm":{}}""")
      val invalidNames = JSONParser.namesIterator(names.toString)
      assertThrows[upickle.core.AbortException](invalidNames.hasNext)
      val invalidTheorems = JSONParser.theoremIterator(proof.toString, statement.toString, names.toString)
      assertThrows[upickle.core.AbortException](invalidTheorems.hasNext)

      Files.writeString(names, upickle.default.write(TheoremRef(7, "missing")))
      val missing = JSONParser.theoremIterator(proof.toString, statement.toString, names.toString)
      assertThrows[NoSuchElementException](missing.hasNext)
      assertThrows[java.io.FileNotFoundException](JSONParser.toContext(directory.resolve("absent").toString, statement.toString))
    finally
      Seq(proof, statement, names).foreach(Files.deleteIfExists)
      Files.deleteIfExists(directory)

  test("leave caller-owned readers open when an iterator context closes"):
    class TrackedReader(text: String) extends java.io.StringReader(text):
      var closed = false
      override def close(): Unit =
        closed = true
        super.close()

    val term = "v(p)(c[bool][])"
    val proofs = new TrackedReader(upickle.default.write(ProofLine(0, extractor.REFL(term))))
    val statements = new TrackedReader(upickle.default.write(TheoremStatement(0, RawSequent(Nil, term))))
    try
      val context = JSONParser.toContext(proofs, statements)
      assert(context.getProof(0) == core.REFL(Variable("p", BoolType)))
      context.close()
      assert(!proofs.closed && !statements.closed)
    finally
      proofs.close()
      statements.close()

  test("close a partially consumed names file with its prefix context"):
    val directory = Files.createTempDirectory("lisa-hol-names")
    val prefix = directory.resolve("trace").toString
    val paths = Seq("proofs", "theorems", "names").map(ext => java.nio.file.Path.of(s"$prefix.$ext"))
    try
      val term = "v(p)(c[bool][])"
      Files.writeString(paths(0), upickle.default.write(ProofLine(0, extractor.REFL(term))))
      Files.writeString(paths(1), upickle.default.write(TheoremStatement(0, RawSequent(Nil, term))))
      Files.writeString(paths(2), (1 to 4).map(i => upickle.default.write(TheoremRef(0, s"Θ$i😀"))).mkString("\n"))
      assert(JSONParser.namesIterator(paths(2).toString).map(_.name).toList == (1 to 4).map(i => s"Θ$i😀").toList)
      val (context, names) = JSONParser.initializeFromPrefix(prefix)
      try assert(names.next().name == "Θ1😀")
      finally context.close()
      assertThrows[java.io.IOException](names.toList)
    finally
      paths.foreach(Files.deleteIfExists)
      Files.deleteIfExists(directory)

  test("file contexts retrieve indexed steps lazily"):
    val proofFile = Files.createTempFile("lisa-hol-extractor", ".proofs")
    val theoremFile = Files.createTempFile("lisa-hol-extractor", ".theorems")

    val variable = "v(p)(c[bool][])"
    val proofs =
      s"""{"id":0,"pr":{"step":"ASSUME","term":"$variable"}}
         |{"id":1,"pr":{"step":"REFL","term":"$variable"}}
         |""".stripMargin
    val theorems =
      s"""{"id":0,"th":{"hy":["$variable"],"cc":"$variable"}}
         |{"id":1,"th":{"hy":[],"cc":"$variable"}}
         |""".stripMargin

    try
      Files.writeString(proofFile, proofs, StandardCharsets.UTF_8)
      Files.writeString(theoremFile, theorems, StandardCharsets.UTF_8)

      val context = JSONParser.toContext(proofFile.toString, theoremFile.toString)
      try
        assert(context.getDefinition(1).isEmpty)
        assert(context.getProof(1) == core.REFL(Variable("p", BoolType)))
        assert(context.getStatement(0) == HOLSequent(List(Variable("p", BoolType)), Variable("p", BoolType)))
      finally context.close()
    finally
      Files.deleteIfExists(proofFile)
      Files.deleteIfExists(theoremFile)

  test("definition scans skip absent indices while direct lookups reject them"):
    val proofFile = Files.createTempFile("lisa-hol-sparse-extractor", ".proofs")
    val theoremFile = Files.createTempFile("lisa-hol-sparse-extractor", ".theorems")

    val variable = "v(p)(c[bool][])"
    val proofs =
      s"""{"id":0,"pr":{"step":"DEFINITION","term":"$variable","name":"P"}}
         |{"id":2,"pr":{"step":"REFL","term":"$variable"}}
         |""".stripMargin
    val theorems =
      s"""{"id":0,"th":{"hy":[],"cc":"$variable"}}
         |{"id":2,"th":{"hy":[],"cc":"$variable"}}
         |""".stripMargin

    try
      Files.writeString(proofFile, proofs, StandardCharsets.UTF_8)
      Files.writeString(theoremFile, theorems, StandardCharsets.UTF_8)

      val context = JSONParser.toContext(proofFile.toString, theoremFile.toString)
      try
        assert(context.getDefinitionsBetween(-1, 2) == Seq(0L -> core.DEFINITION("P", Variable("p", BoolType))))
        assertThrows[NoSuchElementException](context.getTheorem(1))
        assertThrows[NoSuchElementException](context.getProof(1))
        assertThrows[NoSuchElementException](context.getDefinition(1))
        assert(context.getProof(2) == core.REFL(Variable("p", BoolType)))
      finally context.close()
    finally
      Files.deleteIfExists(proofFile)
      Files.deleteIfExists(theoremFile)
  private def withFiles(proofs: String, statements: String)(check: ExtractorContext => Unit): Unit =
    val proofFile = Files.createTempFile("lisa-hol-reader", ".proofs")
    val theoremFile = Files.createTempFile("lisa-hol-reader", ".theorems")
    try
      Files.writeString(proofFile, proofs, StandardCharsets.UTF_8)
      Files.writeString(theoremFile, statements, StandardCharsets.UTF_8)
      val context = JSONParser.toContext(proofFile.toString, theoremFile.toString)
      try check(context)
      finally context.close()
    finally
      Files.deleteIfExists(proofFile)
      Files.deleteIfExists(theoremFile)

  test("random UTF-8 statement lookups preserve the sequential scan across sparse IDs"):
    val entries = Seq(0L -> "α😀", 7L -> "β", 15L -> "終")
    val proofs = entries.map: (id, name) =>
      upickle.default.write(ProofLine(id, extractor.REFL(s"v($name)(c[bool][])")))
    val statements = entries.map: (id, name) =>
      upickle.default.write(TheoremStatement(id, RawSequent(Nil, s"v($name)(c[bool][])")))

    // Use CRLF and omit the final terminator to exercise exact saved offsets.
    withFiles(proofs.mkString("\r\n"), statements.mkString("\r\n")): context =>
      for (id, name) <- entries do
        assert(context.getProof(id) == core.REFL(Variable(name, BoolType)))
        assert(context.getStatement(0).concl == Variable("α😀", BoolType))
        assert(context.getStatement(id).concl == Variable(name, BoolType))
      assertThrows[NoSuchElementException](context.getProof(8))
      assertThrows[NoSuchElementException](context.getProof(16))
      assert(context.getStatement(7).concl == Variable("β", BoolType))

  test("defer missing statements until requested; exhaustive validation rejects mismatched IDs"):
    val proofs = upickle.default.write(ProofLine(0, extractor.REFL("v(p)(c[bool][])")))
    val statements = upickle.default.write(TheoremStatement(1, RawSequent(Nil, "v(p)(c[bool][])")))
    withFiles(proofs, statements): context =>
      assert(context.getProof(0) == core.REFL(Variable("p", BoolType)))
      assert(context.statistics.statementBytes == 0)
      assertThrows[NoSuchElementException](context.getStatement(0))
      val error = intercept[IllegalArgumentException](context.toMap)
      assert(error.getMessage.contains("Proof step 0 is paired with theorem statement 1"))

  test("alternate long UTF-8 line scans and older statement lookups with every line ending"):
    val entries = Seq(0L -> "α😀", 7L -> ("λ" * 70000), 15L -> "終", 20L -> "last")
    def join(lines: Seq[String]): String =
      lines.zip(Seq("\r", "\r\n", "\n", "")).map((line, ending) => line + ending).mkString
    val proofs = entries.map: (id, name) =>
      upickle.default.write(ProofLine(id, extractor.REFL(s"v($name)(c[bool][])")))
    val statements = entries.map: (id, name) =>
      upickle.default.write(TheoremStatement(id, RawSequent(Nil, s"v($name)(c[bool][])")))

    withFiles(join(proofs), join(statements)): context =>
      for (id, name) <- entries do
        assert(context.getProof(id) == core.REFL(Variable(name, BoolType)))
        assert(context.getStatement(0).concl == Variable("α😀", BoolType))
        assert(context.getStatement(id).concl == Variable(name, BoolType))
      assertThrows[NoSuchElementException](context.getProof(21))
      assert(context.getStatement(7).concl == Variable(entries(1)._2, BoolType))
      assert(context.getProof(20) == core.REFL(Variable("last", BoolType)))

  test("report EOF for empty trace files"):
    withFiles("", ""): context =>
      assertThrows[NoSuchElementException](context.getProof(0))
      assertThrows[NoSuchElementException](context.getStatement(0))
      assert(context.getDefinitionsBetween(-1, Long.MaxValue).isEmpty)

  test("definition intervals may end beyond EOF for both context implementations"):
    val proof = ProofLine(3, extractor.DEFINITION("v(p)(c[bool][])", "P"))
    val statement = TheoremStatement(3, RawSequent(Nil, "v(p)(c[bool][])"))
    def check(context: ExtractorContext): Unit =
      assert(context.getDefinitionsBetween(-1, 100).map(_._1) == Seq(3))
      assert(context.getDefinitionsBetween(3, 100).isEmpty)
      assertThrows[NoSuchElementException](context.getProof(100))
      assertThrows[IllegalArgumentException](context.getDefinitionsBetween(100, 3))
    withFiles(upickle.default.write(proof), upickle.default.write(statement))(check)
    val eager = new ExtractorContext(Iterator(proof), Iterator(statement))
    try check(eager)
    finally eager.close()

  test("defer parsing intermediate statements until they are requested"):
    val proofs = upickle.default.write(ProofLine(0, extractor.REFL("v(p)(c[bool][])")))
    val statements = upickle.default.write(TheoremStatement(0, RawSequent(Nil, "not a term")))
    withFiles(proofs, statements): context =>
      assert(context.getProof(0) == core.REFL(Variable("p", BoolType)))
      assertThrows[CouldNotParseException](context.getStatement(0))

  test("skim ordinary proof payloads without parsing them or reading any statements"):
    val proofs = """{"id":0,"pr":{"step":"REFL","term": invalid JSON}}
                   |{"id":9,"pr":{"step":"REFL","term":"v(p)(c[bool][])"}}""".stripMargin
    withFiles(proofs, "not even a statement header"): context =>
      assert(context.getDefinitionsBetween(-1, 9).isEmpty)
      assert(context.statistics.proofHeaders == 2)
      assert(context.statistics.proofRecords == 0)
      assert(context.statistics.statementBytes == 0)
      assert(context.getProof(9) == core.REFL(Variable("p", BoolType)))
      assert(context.statistics.proofRecords == 1)
      assertThrows[Exception](context.getProof(0))
      assertThrows[IllegalArgumentException](context.getStatement(9))

  test("definitions are discovered in order without parsing unused ordinary terms"):
    val term = "v(p)(c[bool][])"
    val lines = Seq(
      ProofLine(2, extractor.REFL("invalid")),
      ProofLine(7, extractor.DEFINITION(term, "P")),
      ProofLine(12, extractor.TYPE_DEFINITION(7, term, "T")),
      ProofLine(99, extractor.REFL(term))
    )
    withFiles(lines.map(upickle.default.write(_)).mkString("\n"), ""): context =>
      assert(context.getDefinitionsBetween(-1, 8).map(_._1) == Seq(7))
      assert(context.getDefinitionsBetween(8, 99).map(_._1) == Seq(12))
      assert(context.getDefinitionsBetween(-1, 99).map(_._1) == Seq(7, 12))
      assert(context.statistics.statementBytes == 0)
      assertThrows[CouldNotParseException](context.getProof(2))

  test("reject malformed definition payloads before returning a definition interval"):
    withFiles("""{"id":0,"pr":{"step":"DEFINITION","term":"invalid","name":"P"}}""", ""): context =>
      assertThrows[CouldNotParseException](context.getDefinitionsBetween(-1, 0))

  test("reject duplicate and descending proof IDs even when their payloads are unused"):
    for ids <- Seq(Seq(1L, 1L), Seq(2L, 1L)) do
      val lines = ids.map(id => upickle.default.write(ProofLine(id, extractor.REFL("invalid")))).mkString("\n")
      withFiles(lines, ""): context =>
        assertThrows[IllegalArgumentException](context.getDefinitionsBetween(-1, 10))
        // A failed scan must not be recoverable by advancing past the bad header.
        assertThrows[IllegalArgumentException](context.getProof(1))

  test("retain a malformed-header failure after the cursor has advanced"):
    val bad = """{"id":0,"pr":{"step":"UNKNOWN","term":"ignored"}}"""
    val good = """{"id":1,"pr":{"step":"REFL","term":"v(p)(c[bool][])"}}"""
    withFiles(bad + "\n" + good, ""): context =>
      val first = intercept[IllegalArgumentException](context.getDefinitionsBetween(-1, 1))
      val second = intercept[IllegalArgumentException](context.getProof(1))
      assert(first eq second)

  test("reject truncated, overflowing, reordered, and unknown proof headers"):
    val lines = Seq(
      "",
      "{",
      "{\"id\":",
      "{\"id\":-1,\"pr\":{\"step\":\"REFL\",",
      "{\"id\":9223372036854775808,\"pr\":{\"step\":\"REFL\",",
      "{\"pr\":{\"step\":\"REFL\"},\"id\":0}",
      "{\"id\":0,\"pr\":{\"step\":\"FUTURE_RULE\",\"term\":\"x\"}}"
    )
    for line <- lines.tail do withFiles(line, "")(context => assertThrows[IllegalArgumentException](context.getDefinitionsBetween(-1, 0)))

  test("exhaustive validation detects unmatched tails and malformed unused payloads"):
    val proof = upickle.default.write(ProofLine(0, extractor.REFL("v(p)(c[bool][])")))
    val statement = upickle.default.write(TheoremStatement(0, RawSequent(Nil, "v(p)(c[bool][])")))
    withFiles(proof, "")(context => assertThrows[IllegalArgumentException](context.toMap))
    withFiles("", statement)(context => assertThrows[IllegalArgumentException](context.toMap))
    withFiles(proof, statement + "\n" + statement)(context => assertThrows[IllegalArgumentException](context.toMap))
    withFiles(proof.replace("v(p)(c[bool][])", "invalid"), statement)(context => assertThrows[CouldNotParseException](context.toMap))

  test("exhaustive validation rejects records after the maximum ID"):
    val proof = upickle.default.write(ProofLine(Long.MaxValue, extractor.REFL("v(p)(c[bool][])")))
    val statement = upickle.default.write(TheoremStatement(Long.MaxValue, RawSequent(Nil, "v(p)(c[bool][])")))
    withFiles(proof, statement)(context => assert(context.toMap.size == 1))
    withFiles(proof + "\n" + proof, statement)(context => assertThrows[IllegalArgumentException](context.toMap))
    withFiles(proof + "\n{", statement)(context => assertThrows[IllegalArgumentException](context.toMap))

  test("seek sparse variable-length records across blocks and compare with eager extraction"):
    val entries = (0 until 2300).map(i => (i.toLong * 13, s"v(x$i${"λ" * (i % 71)})(c[bool][])"))
    val proofs = entries.map((id, term) => ProofLine(id, extractor.REFL(term)))
    val statements = entries.map((id, term) => TheoremStatement(id, RawSequent(Nil, term)))
    def lines[A: upickle.default.Writer](entries: Seq[A]): String =
      entries.zipWithIndex.map((entry, i) => upickle.default.write(entry) + Seq("\n", "\r", "\r\n")(i % 3)).mkString
    withFiles(lines(proofs), lines(statements)): context =>
      val eager = new ExtractorContext(proofs.iterator, statements.iterator)
      val expected = eager.toMap.toMap
      val random = new scala.util.Random(42)
      for (id, _) <- random.shuffle(entries).take(160) ++ entries.take(2) ++ entries.takeRight(2) do assert(context.getTheorem(id) == expected(id))
      assertThrows[NoSuchElementException](context.getProof(1))
      assertThrows[NoSuchElementException](context.getStatement(Long.MaxValue))
      assert(context.toMap.toMap == expected)

  test("preserve exact IDs above double precision and at Long.MaxValue"):
    val ids = Seq(9007199254740992L, 9007199254740993L, Long.MaxValue)
    val proofs = ids.map(id => upickle.default.write(ProofLine(id, extractor.REFL("v(p)(c[bool][])")))).mkString("\n")
    val statements = ids.map(id => upickle.default.write(TheoremStatement(id, RawSequent(Nil, "v(p)(c[bool][])")))).mkString("\n")
    // Test both uPickle's quoted Long encoding and HOL's decimal encoding.
    def decimal(text: String): String = "\"id\":\"([0-9]+)\"".r.replaceAllIn(text, "\"id\":$1")
    for (ps, ts) <- Seq(proofs -> statements, decimal(proofs) -> decimal(statements)) do
      withFiles(ps, ts): context =>
        ids.reverse.foreach(id => assert(context.getTheorem(id).proof == core.REFL(Variable("p", BoolType))))
        assertThrows[NoSuchElementException](context.getProof(ids.head - 1))

end ExtractorSuite
