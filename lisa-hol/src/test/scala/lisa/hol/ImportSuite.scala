package lisa.hol

import lisa.hol.extractor.*
import org.scalatest.funsuite.AnyFunSuite
import java.nio.file.Files

class ImportSuite extends AnyFunSuite:
  private def withContext[A](fileBacked: Boolean, proofs: Seq[ProofLine], statements: Seq[TheoremStatement])(run: ExtractorContext => A): A =
    val directory = Files.createTempDirectory("lisa-import-context")
    val proofFile = directory.resolve("trace.proofs")
    val statementFile = directory.resolve("trace.theorems")
    try
      val context = if fileBacked then
        Files.writeString(proofFile, proofs.map(upickle.default.write(_)).mkString("\n"))
        Files.writeString(statementFile, statements.map(upickle.default.write(_)).mkString("\n"))
        JSONParser.toContext(proofFile.toString, statementFile.toString)
      else new ExtractorContext(proofs.iterator, statements.iterator)
      try run(context)
      finally context.close()
    finally
      Files.deleteIfExists(proofFile)
      Files.deleteIfExists(statementFile)
      Files.deleteIfExists(directory)

  private val p = "v(store_p)(c[bool][])"
  private val q = "v(store_q)(c[bool][])"
  private val equality = s"C(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))($p))($p)"

  test("fatal step errors report the trace ID and preserve their cause"):
    val wrongType = "v(store_f)(c[fun][[c[bool][]][c[bool][]]])"
    val proofs = Iterator(ProofLine(0, REFL(p)), ProofLine(1, INST(0, List(InstPair(p, wrongType)))))
    val statements = (0L to 1L).iterator.map(id => TheoremStatement(id, RawSequent(Nil, equality)))
    given context: ExtractorContext = new ExtractorContext(proofs, statements)
    try
      val error = intercept[Import.FailedStepException](new Import.StepStore().apply(1))
      assert(error.index == 1 && error.step == "INST")
      assert(error.getMessage.contains("Type mismatch in instantiation"))
      assert(error.getCause.isInstanceOf[lisa.utils.prooflib.FatalCarrierDestructionException])
    finally context.close()

  test("lazy file imports reject missing and forward premises and mismatched named targets"):
    val statements = Seq(0L, 7L).map(id => TheoremStatement(id, RawSequent(Nil, equality)))
    withContext(true, Seq(ProofLine(0, REFL(p)), ProofLine(7, TRANS(3, 0))), statements): context =>
      given ExtractorContext = context
      assertThrows[NoSuchElementException](new Import.StepStore().apply(7))
    withContext(true, Seq(ProofLine(0, TRANS(7, 7)), ProofLine(7, REFL(p))), statements): context =>
      given ExtractorContext = context
      assertThrows[Import.OutOfOrderException](new Import.StepStore().apply(0))
    withContext(true, Seq(ProofLine(0, REFL(p))), Seq(TheoremStatement(0, RawSequent(Nil, q)))): context =>
      given ExtractorContext = context
      assertThrows[Import.FailedTheoremException](new Import.StepStore().theorem(TheoremRef(0, "lazy_mismatch")))

  test("register an implicitly used constant from its proof record alone"):
    val name = "lazy_implicit_constant"
    val constant = s"c($name)(c[bool][])"
    val truth = "c(T)(c[bool][])"
    def equal(left: String, right: String): String =
      s"C(C(c(=)(c[fun][[c[bool][]][c[fun][[c[bool][]][c[bool][]]]]]))($left))($right)"
    val proofs = Seq(ProofLine(0, DEFINITION(equal(constant, truth), name)), ProofLine(7, REFL(constant)))
    val statements = Seq(TheoremStatement(0, RawSequent(Nil, "not a term")), TheoremStatement(7, RawSequent(Nil, equal(constant, constant))))
    withContext(true, proofs, statements): context =>
      given ExtractorContext = context
      val store = new Import.StepStore
      assert(!store.theorem(TheoremRef(7, "lazy_constant_use")).usesSorry)
      assert(store(0).isValid)
      assert(context.statistics.statementRecords == 1)
      assertThrows[CouldNotParseException](context.getStatement(0))

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

  for
    absFirst <- Seq(true, false)
    polymorphic <- Seq(false, true)
    fileBacked <- Seq(false, true)
  do
    test(s"type definitions precede implicit uses (abs first: $absFirst, polymorphic: $polymorphic, file: $fileBacked)"):
      val bool = "c[bool][]"
      val name = s"store_type_${absFirst}_${polymorphic}_$fileBacked"
      val typ = if polymorphic then s"c[$name][[v[A]]]" else s"c[$name][]"
      def fun(from: String, to: String): String = s"c[fun][[$from][$to]]"
      def app(f: String, x: String): String = s"C($f)($x)"
      def equal(typ: String, x: String, y: String): String =
        app(app(s"c(=)(${fun(typ, fun(typ, bool))})", x), y)
      val representation = if polymorphic then fun("v[A]", "v[A]") else bool
      val witness = if polymorphic then "A(v(v)(v[A]))(v(v)(v[A]))" else s"c(T)($bool)"
      val a = s"v(a)($typ)"
      val r = s"v(r)($representation)"
      val abs = s"c(${name}_abs)(${fun(representation, typ)})"
      val rep = s"c(${name}_rep)(${fun(typ, representation)})"
      val absStatement = equal(typ, app(abs, app(rep, a)), a)
      val repStatement = equal(bool, equal(representation, witness, r), equal(representation, app(rep, app(abs, r)), r))
      val (first, second) = if absFirst then (absStatement, repStatement) else (repStatement, absStatement)
      val proofs = Seq(
        ProofLine(0, REFL(witness)),
        ProofLine(1, TYPE_DEFINITION(0, first, name)),
        ProofLine(2, TYPE_DEFINITION(0, second, name)),
        ProofLine(7, REFL(a))
      )
      val statements = Seq(
        TheoremStatement(0, RawSequent(Nil, equal(representation, witness, witness))),
        TheoremStatement(1, RawSequent(Nil, first)),
        TheoremStatement(2, RawSequent(Nil, second)),
        TheoremStatement(7, RawSequent(Nil, equal(typ, a, a)))
      )
      withContext(fileBacked, proofs, statements): context =>
        given ExtractorContext = context
        val store = new Import.StepStore
        // This REFL has no explicit dependency on either defining theorem.
        assert(!store.theorem(TheoremRef(7, s"${name}_use")).usesSorry)
        if fileBacked then assert(context.statistics.statementRecords == 1)
        for id <- Seq(1L, 2L) do
          val theorem = store.theorem(TheoremRef(id, s"${name}_$id"))
          assert(store(id).isValid)
          assert(!theorem.usesSorry)
          assert(store(id) eq store(id))
