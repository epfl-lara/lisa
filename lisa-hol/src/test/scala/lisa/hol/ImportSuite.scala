package lisa.hol

import lisa.hol.extractor.*
import org.scalatest.funsuite.AnyFunSuite

class ImportSuite extends AnyFunSuite:
  private val p = "v(store_p)(c[bool][])"
  private val q = "v(store_q)(c[bool][])"
  private val equality = s"C(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))($p))($p)"

  private def withStore[A](lastConclusion: String = p)(run: Import.StepStore => A): A =
    val proofs = Iterator(
      ProofLine(0, REFL(p)),
      ProofLine(1, ASSUME(p)),
      ProofLine(3, EQ_MP(0, 1)),
      ProofLine(7, EQ_MP(0, 1))
    )
    val statements = Iterator(
      TheoremStatement(0, RawSequent(Nil, equality)),
      TheoremStatement(1, RawSequent(List(p), p)),
      TheoremStatement(3, RawSequent(List(p), p)),
      TheoremStatement(7, RawSequent(List(p), lastConclusion))
    )
    given context: ExtractorContext = new ExtractorContext(proofs, statements)
    try run(new Import.StepStore)
    finally context.close()

  test("named theorems and aliases share unnamed dependencies"):
    withStore(): store =>
      val first = store.theorem(TheoremRef(3, "store_first"))
      val shared = store(0)
      assert(store.size == 3)

      val second = store.theorem(TheoremRef(7, "store_second"))
      assert(store.size == 4)
      assert(store(0) eq shared)
      assert(first.statement == second.statement)
      assert(!first.usesSorry && !second.usesSorry)

      store.theorem(TheoremRef(3, "store_alias"))
      assert(store.size == 4)
      assert(store(0) eq shared)

  test("sparse step IDs work and missing or forward premises fail"):
    withStore(): store =>
      assert(store(7).isValid)
      assertThrows[NoSuchElementException](store(2))
      assertThrows[Import.OutOfOrderException](store.premise(7, 7))
      assertThrows[Import.OutOfOrderException](store.premise(3, 7))

  test("a mismatched named statement fails without replacing the reconstructed step"):
    withStore(q): store =>
      val judgement = store(7)
      assert(judgement.isValid)
      assertThrows[Import.FailedTheoremException](store.theorem(TheoremRef(7, "store_mismatch")))
      assert(store(7) eq judgement)
      assert(!store.theorem(TheoremRef(3, "store_after_mismatch")).usesSorry)

  test("separate imports keep separate step stores"):
    withStore(): first =>
      val firstStep = first(0)
      withStore(): second =>
        assert(second.size == 0)
        assert(!(firstStep eq second(0)))
        assert(firstStep.justification.get.statement == second(0).justification.get.statement)

  test("cached proof errors propagate to dependent steps"):
    // Abstraction cannot bind a variable that remains free in a hypothesis.
    val proofs = Iterator(ProofLine(0, ASSUME(equality)), ProofLine(1, ABS(0, p)), ProofLine(2, TRANS(1, 1)))
    val statements = (0L to 2L).iterator.map(id => TheoremStatement(id, RawSequent(List(equality), equality)))
    given context: ExtractorContext = new ExtractorContext(proofs, statements)
    try
      val store = new Import.StepStore
      val invalid = store(1)
      assert(!invalid.isValid)
      assert(invalid.errors.nonEmpty)
      assert(store(1) eq invalid)
      assert(invalid.errors.subsetOf(store(2).errors))
      assertThrows[Import.FailedTheoremException](store.theorem(TheoremRef(2, "store_invalid")))
      assert(store(0).isValid)
    finally context.close()
