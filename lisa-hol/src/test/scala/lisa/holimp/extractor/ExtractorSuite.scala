package lisa
package hol
package extractor

import java.nio.charset.StandardCharsets
import java.nio.file.Files

import org.scalatest.funsuite.AnyFunSuite

import core._
import core.Parser._

class ExtractorSuite extends AnyFunSuite:
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

  test("reject mismatched proof and statement IDs during scanning"):
    val proofs = upickle.default.write(ProofLine(0, extractor.REFL("v(p)(c[bool][])")))
    val statements = upickle.default.write(TheoremStatement(1, RawSequent(Nil, "v(p)(c[bool][])")))
    withFiles(proofs, statements): context =>
      val error = intercept[IllegalArgumentException](context.getProof(0))
      assert(error.getMessage.contains("Proof step 0 is paired with theorem statement 1"))

  test("alternate long UTF-8 line scans and older statement lookups with every line ending"):
    val entries = Seq(0L -> "α😀", 7L -> "λ".repeat(70000), 15L -> "終", 20L -> "last")
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

  test("defer parsing intermediate statements until they are requested"):
    val proofs = upickle.default.write(ProofLine(0, extractor.REFL("v(p)(c[bool][])")))
    val statements = upickle.default.write(TheoremStatement(0, RawSequent(Nil, "not a term")))
    withFiles(proofs, statements): context =>
      assert(context.getProof(0) == core.REFL(Variable("p", BoolType)))
      assertThrows[CouldNotParseException](context.getStatement(0))

end ExtractorSuite
