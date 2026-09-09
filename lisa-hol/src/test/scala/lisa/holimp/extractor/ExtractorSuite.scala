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
end ExtractorSuite
