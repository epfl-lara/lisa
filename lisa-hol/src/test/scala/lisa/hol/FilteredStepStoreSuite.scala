package lisa.hol

import lisa.hol.extractor.{ExtractorContext, ProofLine, RawSequent, TheoremRef, TheoremStatement}
import lisa.utils.K
import org.scalatest.funsuite.AnyFunSuite

class FilteredStepStoreSuite extends AnyFunSuite:
  private val variable = "v(filtered)(c[bool][])"
  private val equalityType = "c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]"
  private val equality = s"C(C(c(=)($equalityType))($variable))($variable)"

  private def context(offset: Long): ExtractorContext =
    val proofs = Seq(
      ProofLine(offset, extractor.REFL(variable)),
      ProofLine(offset + 1, extractor.TRANS(offset, offset)),
      ProofLine(offset + 2, extractor.TRANS(offset + 1, offset)),
      ProofLine(offset + 3, extractor.TRANS(offset + 1, offset + 1))
    )
    val statements = proofs.map(line => TheoremStatement(line.id, RawSequent(Nil, equality)))
    new ExtractorContext(proofs.iterator, statements.iterator)

  private def check(result: Import.Justification): Unit =
    val theorem = result.asInstanceOf[lisa.SetTheoryLibrary.THM]
    assert(!theorem.innerJustification.withSorry)
    assert(theorem.proofStatistics.kernelSize > 0)
    assert(theorem.isInstanceOf[lisa.SetTheoryLibrary.THMFromProof])

  test("export selected roots once and import them into distinct local proofs"):
    given ExtractorContext = context(0)
    val store = new Import.LocalStepStore(lemmaSteps = Set(0L, 1L))
    check(store.theorem(TheoremRef(2, "filtered_first")))
    assert(store.size == 3)
    check(store.theorem(TheoremRef(3, "filtered_second")))
    assert(store.size == 4)
    assert(store.lemmaCacheSize == 2)
    assert(store.lemmaCacheHits >= 2)
    assert(store.retainedSize == 4)
    assert(store.localCacheSize == 1)
    assert(lisa.SetTheoryLibrary.theory.getTheorem("Import.lemma_0").nonEmpty)
    assert(lisa.SetTheoryLibrary.theory.getTheorem("Import.lemma_1").nonEmpty)

  test("keep ordinary steps theorem-local when no helpers are selected"):
    given ExtractorContext = context(100)
    val store = new Import.LocalStepStore()
    check(store.theorem(TheoremRef(102, "local_first")))
    check(store.theorem(TheoremRef(103, "local_second")))
    assert(store.size == 6)
    assert(store.lemmaCacheSize == 0)
    assert(store.retainedSize == 2)
    assert(store.localCacheSize == 3)

  test("construct a selected named root without recursively requesting itself"):
    given ExtractorContext = context(200)
    val store = new Import.LocalStepStore(lemmaSteps = Set(203L))
    check(store.theorem(TheoremRef(203, "selected_named_root")))
    assert(store.size == 3)
    assert(store.lemmaCacheSize == 0)
    assert(store.retainedSize == 1)

  test("reject missing selected premises instead of treating the ID as a proof"):
    val proof = ProofLine(302, extractor.TRANS(301, 301))
    val statement = TheoremStatement(302, RawSequent(Nil, equality))
    given ExtractorContext = new ExtractorContext(Iterator(proof), Iterator(statement))
    val store = new Import.LocalStepStore(lemmaSteps = Set(301L))
    assertThrows[NoSuchElementException](store.theorem(TheoremRef(302, "missing_selected_root")))

  test("reject forward selected premises"):
    val proof = ProofLine(402, extractor.TRANS(403, 403))
    val statement = TheoremStatement(402, RawSequent(Nil, equality))
    given ExtractorContext = new ExtractorContext(Iterator(proof), Iterator(statement))
    val store = new Import.LocalStepStore(lemmaSteps = Set(403L))
    assertThrows[IllegalArgumentException](store.theorem(TheoremRef(402, "forward_selected_root")))

  test("retain named theorem metadata without construction archives"):
    given ExtractorContext = context(500)
    val store = new Import.LocalStepStore(lemmaSteps = Set(500L, 501L))
    val first = store.theorem(TheoremRef(502, "certificate_first")).asInstanceOf[lisa.SetTheoryLibrary.THM]
    val second = store.theorem(TheoremRef(503, "certificate_second")).asInstanceOf[lisa.SetTheoryLibrary.THM]
    List(first, second).foreach: theorem =>
      check(theorem)
      assert(!theorem.wasCached)
      assert(theorem.sorryDependencies.isEmpty)
    assert(first.fullName == "Import.certificate⑪first")
    assert(store.size == 4 && store.lemmaCacheSize == 2)
