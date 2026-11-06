package lisa.hol

import lisa.hol.extractor.*
import lisa.utils.K
import org.scalatest.funsuite.AnyFunSuite
import java.nio.file.Files

class BoundedStepStoreSuite extends AnyFunSuite:
  private val bool = "c[bool][]"
  private val p = s"v(bounded_p)($bool)"
  private val q = s"v(bounded_q)($bool)"
  private def fun(a: String, b: String) = s"c[fun][[$a][$b]]"
  private def app(f: String, x: String) = s"C($f)($x)"
  private def equal(t: String, a: String, b: String): String =
    app(app(s"c(=)(${fun(t, fun(t, bool))})", a), b)
  private val refl = equal(bool, p, p)

  private def withContext[A](file: Boolean, proofs: Seq[ProofLine], statements: Seq[TheoremStatement] = Nil)(f: ExtractorContext => A): A =
    val directory = Files.createTempDirectory("bounded-steps")
    val proofFile = directory.resolve("proofs")
    val statementFile = directory.resolve("theorems")
    val context = if file then
      Files.writeString(proofFile, proofs.map(upickle.default.write(_)).mkString("\n"))
      Files.writeString(statementFile, statements.map(upickle.default.write(_)).mkString("\n"))
      JSONParser.toContext(proofFile.toString, statementFile.toString)
    else
      // Iterator fixtures require one statement per proof, even when no statement is requested.
      val byId = statements.map(statement => statement.id -> statement).toMap
      val aligned = proofs.map(proof => byId.getOrElse(proof.id, TheoremStatement(proof.id, RawSequent(Nil, refl))))
      new ExtractorContext(proofs.iterator, aligned.iterator)
    try f(context)
    finally
      context.close()
      Files.deleteIfExists(proofFile)
      Files.deleteIfExists(statementFile)
      Files.delete(directory)

  for file <- Seq(false, true) do
    test(s"recheck evicted shared premises and preserve theorem metadata (file: $file)"):
      val records = Seq(ProofLine(0, REFL(p)), ProofLine(1, ASSUME(p)), ProofLine(3, EQ_MP(0, 1)), ProofLine(7, EQ_MP(0, 1)))
      withContext(file, records): context =>
        given ExtractorContext = context
        val bounded = new Import.StepStore(capacity = 1, generations = 0)
        val unbounded = new Import.StepStore(capacity = 0)
        val before = bounded(3)
        val reconstructed = bounded(7)
        val expected = unbounded(7)
        assert(reconstructed.isValid && before.isValid)
        assert(K.isSameSequent(reconstructed.kernel.statement, expected.kernel.statement))
        assert(reconstructed.kernel.axioms == expected.kernel.axioms)
        assert(reconstructed.kernel.assumptions == expected.kernel.assumptions)
        assert(!reconstructed.kernel.usesSorry)
        assert(bounded.retainedSize == 1)
        assert(bounded.evictions > 0)
        assert(bounded.size == 6 && unbounded.size == 3)
        val computed = bounded.size
        assert(bounded(7) eq reconstructed)
        assert(bounded.size == computed)

    test(s"pin future named steps, promote existing steps, and preserve aliases (file: $file)"):
      val records = Seq(0L, 1L, 3L, 7L).map(id => ProofLine(id, REFL(p)))
      val statements = records.map(r => TheoremStatement(r.id, RawSequent(Nil, refl)))
      withContext(file, records, statements): context =>
        given ExtractorContext = context
        val store = new Import.StepStore(capacity = 1, generations = 0, namedSteps = Set(0L))
        val futureNamed = store(0)
        val promoted = store(1)
        store.theorem(TheoremRef(1, s"bounded_promote_$file"))
        store(3)
        store(7)
        assert(store.pinnedSize == 2 && store.retainedSize == 3)
        assert(store(0) eq futureNamed)
        assert(store(1) eq promoted)
        val count = store.size
        store.theorem(TheoremRef(0, s"bounded_future_$file"))
        store.theorem(TheoremRef(0, s"bounded_alias_$file"))
        assert(store.size == count)

    test(s"eviction preserves missing/forward-reference errors and named mismatch rejection (file: $file)"):
      val records = Seq(ProofLine(0, REFL(p)), ProofLine(1, REFL(q)), ProofLine(3, TRANS(2, 0)), ProofLine(7, TRANS(8, 0)))
      val statements = Seq(TheoremStatement(0, RawSequent(Nil, q)))
      withContext(file, records, statements): context =>
        given ExtractorContext = context
        val store = new Import.StepStore(capacity = 1, generations = 0)
        store(0)
        store(1)
        assertThrows[NoSuchElementException](store(3))
        assertThrows[Import.OutOfOrderException](store(7))
        assertThrows[Import.FailedTheoremException](store.theorem(TheoremRef(0, s"bounded_mismatch_$file")))
        assert(store(0).isValid)

    test(s"invalid proofs stay invalid after eviction and in dependent steps (file: $file)"):
      val records = Seq(ProofLine(0, ASSUME(refl)), ProofLine(1, ABS(0, p)), ProofLine(2, REFL(q)), ProofLine(3, TRANS(1, 1)))
      withContext(file, records): context =>
        given ExtractorContext = context
        val store = new Import.StepStore(capacity = 1, generations = 0)
        val first = store(1)
        assert(!first.isValid && first.errors.nonEmpty)
        store(2)
        val rebuilt = store(1)
        assert(!(first eq rebuilt) && !rebuilt.isValid)
        assert(!store(3).isValid)

    test(s"pin constant definitions and both type-definition results (file: $file)"):
      val name = s"bounded_type_$file"
      val typ = s"c[$name][]"
      val witness = s"c(T)($bool)"
      val a = s"v(a)($typ)"
      val r = s"v(r)($bool)"
      val abs = s"c(${name}_abs)(${fun(bool, typ)})"
      val rep = s"c(${name}_rep)(${fun(typ, bool)})"
      val absStatement = equal(typ, app(abs, app(rep, a)), a)
      val repStatement = equal(bool, equal(bool, witness, r), equal(bool, app(rep, app(abs, r)), r))
      val constName = s"bounded_const_$file"
      val c = s"c($constName)($bool)"
      val records = Seq(
        ProofLine(0, REFL(witness)), ProofLine(1, TYPE_DEFINITION(0, absStatement, name)),
        ProofLine(2, TYPE_DEFINITION(0, repStatement, name)),
        ProofLine(3, DEFINITION(equal(bool, c, witness), constName)),
        ProofLine(7, REFL(a)), ProofLine(9, REFL(c))
      )
      withContext(file, records): context =>
        given ExtractorContext = context
        val store = new Import.StepStore(capacity = 1, generations = 0)
        assert(store(7).isValid)
        val definitions = Seq(1L, 2L, 3L).map(store(_))
        assert(store(9).isValid)
        val count = store.size
        assert(store.pinnedSize == 3 && store.retainedSize == 4)
        Seq(1L, 2L, 3L).zip(definitions).foreach((id, original) => assert(store(id) eq original))
        assert(store.size == count)

  test("step-shape statistics retain inputs evicted during dependency reconstruction"):
    val directory = Files.createTempDirectory("bounded-step-stats")
    val path = directory.resolve("steps.csv")
    val statistics = new ImportStatistics(stepOutput = Some(path))
    try
      withContext(true, Seq(ProofLine(0, REFL(p)), ProofLine(1, ASSUME(p)), ProofLine(3, EQ_MP(0, 1)))): context =>
        given ExtractorContext = context
        val store = new Import.StepStore(statistics, capacity = 1, generations = 0)
        statistics.begin(3)
        assert(store(3).isValid)
        statistics.finish(3, "bounded-shapes")
        assert(Files.readString(path).linesIterator.exists(_.startsWith("3,EQ_MP,")))
    finally
      statistics.close()
      Files.deleteIfExists(path)
      Files.delete(directory)
