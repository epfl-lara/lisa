package lisa.hol

import lisa.hol.Import.Transformers.*
import lisa.hol.extractor.*
import lisa.utils.K
import org.scalatest.funsuite.AnyFunSuite

class DefinitionNameSuite extends AnyFunSuite:
  test("import a constant whose name already belongs to a library symbol of another sort"):
    val existing = lisa.maths.SetTheory.Order.Extrema.minimal
    val previous = lisa.SetTheoryLibrary.theory.getDefinition(existing.underlying)
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
    assert(lisa.SetTheoryLibrary.theory.getDefinition(existing.underlying) == previous)
    assert(result.proofStatistics.kernelSize > 0)
    assert(!result.withSorry)
    assert(store(100) eq result)
