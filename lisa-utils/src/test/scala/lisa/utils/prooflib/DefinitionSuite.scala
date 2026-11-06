package lisa.utils.prooflib

import lisa.kernel.proof.RunningTheory
import lisa.utils.K
import lisa.utils.fol.FOL.{_, given}
import org.scalatest.funsuite.AnyFunSuite

import java.io.ByteArrayInputStream
import java.io.ByteArrayOutputStream
import java.io.DataInputStream
import java.io.DataOutputStream

class DefinitionSuite extends AnyFunSuite:
  private given OutputManager = new OutputManager:
    val stringWriter = new java.io.StringWriter
    def finishOutput(exception: Exception): Nothing = throw exception

  private class Definitions extends Library:
    val theory = new RunningTheory
    private val x = variable[Ind]

    object First:
      val ω = DEF(λ(x, x))

    object Second:
      val ω = DEF(λ(x, x))

    val predicate = DEF(λ(x, x === x))
    val etaExpanded: Constant[Ind >>: Ind] = DEF(First.ω)

  test("keep qualified definition identities and print short names"):
    val lib = new Definitions
    import lib.*
    val first = First.ω
    val second = Second.ω
    assert(first != second)
    for symbol <- Seq(first, second) do
      assert(symbol.fullName == symbol.id.toString)
      assert(symbol.toString == "ω")
      assert(symbol.definition.fullName == symbol.fullName)
      assert(symbol.definition.name == "ω")
      assert(theory.getDefinition(symbol.underlying).exists(_.cst == symbol.underlying))
    assert(first.id.name.endsWith(".First.ω"))
    assert(second.id.name.endsWith(".Second.ω"))
    assert(theory.getDefinition(K.Constant("ω", first.sort)).isEmpty)

  test("capture definition names at the declaration, including eta expansion"):
    val lib = new Definitions
    import lib.*
    for symbol <- Seq(predicate, etaExpanded) do
      assert(symbol.id.name.endsWith(s".Definitions.${symbol.shortName}"))
      assert(symbol.definition.fullName == symbol.fullName)
      assert(theory.getDefinition(symbol.underlying).nonEmpty)
    assert(
      etaExpanded.definition.statement.underlying ==
        theory.sequentFromJustification(etaExpanded.definition.innerJustification)
    )

  test("reject duplicate full names"):
    val lib = new Definitions
    import lib.*
    val original = theory.getDefinition(First.ω.underlying)
    intercept[UserInvalidDefinitionException]:
      new DirectDefinition[Ind >>: Ind](sourcecode.FullName(First.ω.fullName), summon[sourcecode.Line], summon[sourcecode.File])(Second.ω, Seq(variable[Ind]))
    assert(theory.getDefinition(First.ω.underlying) == original)

  test("resolve qualified definition imports after serialization"):
    val cold = new Definitions
    val definition = cold.getDefinition(cold.First.ω).get
    val statement = definition.statement.underlying
    val proof = lisa.kernel.proof.SCProof(
      IndexedSeq(lisa.kernel.proof.SequentCalculus.Restate(statement, -1)),
      IndexedSeq(statement)
    )
    val trees = new ByteArrayOutputStream
    val steps = new ByteArrayOutputStream
    lisa.utils.Serialization.thmsToDataStream(
      new DataOutputStream(trees),
      new DataOutputStream(steps),
      cold.theory,
      List(("DefinitionSuite.imported", proof, List((definition.owner, definition.innerJustification))))
    )
    val warm = new Definitions
    val checked = lisa.utils.Serialization.thmsFromDataStream(
      new DataInputStream(new ByteArrayInputStream(trees.toByteArray)),
      new DataInputStream(new ByteArrayInputStream(steps.toByteArray)),
      warm.theory
    )
    assert(checked.size == 1)
    assert(checked.head._1.proposition == statement)
    assert(!checked.head._1.withSorry)
