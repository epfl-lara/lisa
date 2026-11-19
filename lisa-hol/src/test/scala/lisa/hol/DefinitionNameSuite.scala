package lisa.hol

import lisa.hol.Import.Transformers._
import lisa.hol.extractor._
import lisa.utils.K
import org.scalatest.funsuite.AnyFunSuite

class DefinitionNameSuite extends AnyFunSuite:
  test("check qualified definition names without colliding with library symbols"):
    val existing = lisa.maths.SetTheory.Order.Extrema.minimal
    val previous = lisa.SetTheoryLibrary.theory.getDefinition(existing.underlying)
    lisa.SetTheoryLibrary.theory.addSymbol(K.Constant(K.Identifier("Import.constant.minimal"), K.Prop))
    val bool = "c[bool][]"
    val equality = s"c(=)(c[fun][[$bool][c[fun][[$bool][$bool]]]])"
    val term = s"C(C($equality)(c(minimal)($bool)))(c(T)($bool))"
    given ExtractorContext = new ExtractorContext(
      Iterator(ProofLine(100, DEFINITION(term, "minimal"))),
      Iterator(TheoremStatement(100, RawSequent(Nil, term)))
    )
    val store = new Import.StepStore
    val result = store(100).asInstanceOf[lisa.SetTheoryLibrary.THM]
    val imported = core.Constant("minimal", core.BoolType).toLisaTerm
    assert(imported.underlying.constants.forall(_.id != existing.id))
    assert(imported.underlying.constants.exists(_.id.name == "Import.constant.minimal$1"))
    assert(lisa.SetTheoryLibrary.theory.getDefinition(existing.underlying) == previous)
    assert(result.proofStatistics.kernelSize > 0)
    assert(!result.withSorry)
    assert(store(100) eq result)
