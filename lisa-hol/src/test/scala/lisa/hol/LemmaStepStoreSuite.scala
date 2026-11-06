package lisa.hol

import lisa.hol.extractor.*
import org.scalatest.funsuite.AnyFunSuite

class LemmaStepStoreSuite extends AnyFunSuite:
  private val p = "v(lemma_store_p)(c[bool][])"
  private val records = Seq(ProofLine(1000, ASSUME(p)), ProofLine(1001, ASSUME(p)), ProofLine(1002, ASSUME(p)))
  private val statements = records.map(record => TheoremStatement(record.id, RawSequent(List(p), p)))

  private def withStore[A](lemmas: Set[Long], named: Set[Long] = Set.empty)(run: Import.StepStore => A): A =
    val context = new ExtractorContext(records.iterator, statements.iterator)
    try run(new Import.StepStore(capacity = 1, generations = 0, lemmaSteps = lemmas, namedSteps = named, trackReconstruction = true)(using context))
    finally context.close()

  test("selected checked results survive eviction as named lemmas"):
    withStore(Set(1000L)): store =>
      val first = store(1000)
      store(1001)
      store(1002)
      val reused = store(1000)
      assert(first.isValid && (first eq reused))
      assert(store.lemmaCount == 1 && store.pinnedSize == 1)
      assert(store.uniqueSteps.contains(3) && store.recomputedSteps.contains(0))
      assert(!reused.kernel.usesSorry)
      val lemma = lisa.SetTheoryLibrary.theorems.get("Import.lemma_1000").get
      assert(lemma.errors.isEmpty)
      assert(lemma.kernel.assumptions == first.kernel.assumptions)

  test("count eviction replay separately from cache hits"):
    withStore(Set.empty): store =>
      store(1000)
      store(1001)
      store(1000)
      store(1000)
      assert(store.size == 3 && store.uniqueSteps.contains(2))
      assert(store.recomputedSteps.contains(1) && store.cacheHits == 1)
      assert(store.lemmaCount == 0)

  test("named roots do not get a second synthetic theorem"):
    withStore(Set(1000L), Set(1000L)): store =>
      store(1000)
      store(1001)
      store(1002)
      store(1000)
      assert(store.lemmaCount == 0 && store.recomputedSteps.contains(0))

  test("selection cannot hide missing references"):
    val context = new ExtractorContext(Iterator(ProofLine(1003, TRANS(1000, 1001))), Iterator(TheoremStatement(1003, RawSequent(List(p), p))))
    try
      val store = new Import.StepStore(lemmaSteps = Set(1003L), trackReconstruction = true)(using context)
      assertThrows[NoSuchElementException](store(1003))
      assert(store.lemmaCount == 0 && store.uniqueSteps.contains(0))
    finally context.close()
