package lisa.automation.superposition

import java.io.{ByteArrayOutputStream, File}
import java.nio.file.Files

import org.scalatest.funsuite.AnyFunSuite

import lisa.tptp.KernelParser.{problemToKernel, strictMapAtom, strictMapTerm, strictMapVariable}

/**
 * Tests for [[CascProver]], the CASC entry point.
 *
 * Everything in it is `private`, and rightly so, since its contract is not a Scala API but the **text it prints**,
 * which a competition harness parses. So these tests are black-box: write a problem, run `main`, capture
 * stdout, and check the output against the SZS conventions. The sharpest assertion is that every annotated
 * formula it emits **re-parses** with the same parser that read the input; a derivation that a harness cannot
 * read is worthless however correct the search was.
 *
 * The problems are written here rather than taken from the corpus, so this suite runs unconditionally, and it
 * does not join the ~40 tests that vanish when `TPTP` is unset (see [[TptpCorpus]]).
 *
 * Not covered, deliberately: the two argument-error paths (no problem file, unknown `--strategy`) call
 * `sys.exit(2)`, which would take the test JVM with them.
 */
class CascProverTest extends AnyFunSuite:

  private lazy val tmp: File = Files.createTempDirectory("casc-prover-test").toFile

  /** Write `body` as a `.p` file and return it. */
  private def problemFile(name: String, body: String): File =
    val f = new File(tmp, name)
    Files.writeString(f.toPath, body.stripMargin)
    f.deleteOnExit()
    f

  /** Run `CascProver.main` with stdout captured. Its diagnostics (SInE decisions, parse/solve errors) go to
    * stderr and are deliberately not captured, since only the machine-readable half is under test. */
  private def run(args: String*): String =
    val out = new ByteArrayOutputStream()
    Console.withOut(out)(CascProver.main(args.toArray))
    out.toString("UTF-8")

  /** The annotated formulas inside the `SZS output start/end CNFRefutation` block. */
  private def emittedFormulas(output: String): Vector[String] =
    output.linesIterator
      .dropWhile(l => !l.contains("SZS output start"))
      .takeWhile(l => !l.contains("SZS output end"))
      .filter(l => l.startsWith("cnf(") || l.startsWith("fof("))
      .toVector

  /** Feed the emitted derivation back through the parser that read the input, as a problem file, which is
    * what a competition harness does with it. Parsed whole rather than statement by statement: the clauses
    * are emitted as `cnf(...)` with `inference(...)` records, and only the problem-level entry point accepts
    * both (`annotatedStatementToKernel` is fof-only). */
  private def assertReparses(label: String, formulas: Vector[String]): Unit =
    assert(formulas.nonEmpty, s"$label: no annotated formulas emitted")
    val f = problemFile(s"$label-reparse.p", formulas.mkString("", "\n", "\n"))
    val parsed = scala.util.Try(problemToKernel(f)(using (strictMapAtom, strictMapTerm, strictMapVariable)))
    assert(parsed.isSuccess,
      s"$label: the emitted derivation does not re-parse\n${formulas.mkString("\n")}\n  ${parsed.failed.map(_.toString).getOrElse("")}")

  // ── SZS status ──────────────────────────────────────────────────────────────────────────────────────────

  test("an unsatisfiable clause set without a conjecture reports SZS Unsatisfiable") {
    val f = problemFile("unsat.p",
      """|cnf(a1, axiom, ( p(X) | q(X) )).
         |cnf(a2, axiom, ~p(a)).
         |cnf(a3, axiom, ~q(a)).
         |""")
    val out = run("-t", "20", f.getPath)
    assert(out.contains(s"% SZS status Unsatisfiable for ${f.getName}"), s"got:\n$out")
  }

  test("a provable conjecture reports SZS Theorem, not Unsatisfiable") {
    // The distinction is the whole point of `szsStatus`: with a conjecture present the refutation of its
    // negation is a *theorem*, and a harness scoring the run reads exactly this word.
    val f = problemFile("thm.p",
      """|fof(ax1, axiom, ![X] : ( p(X) => q(X) )).
         |fof(ax2, axiom, p(a)).
         |fof(goal, conjecture, q(a)).
         |""")
    val out = run("-t", "20", f.getPath)
    assert(out.contains(s"% SZS status Theorem for ${f.getName}"), s"got:\n$out")
  }

  test("a satisfiable problem reports GaveUp and emits no refutation") {
    // Never `Satisfiable`: the search may be incomplete (SInE pruning, budgets), so claiming satisfiability
    // could be *wrong*, while `GaveUp` merely gives up. A refutation block here would be a soundness bug.
    val f = problemFile("sat.p", """|cnf(a1, axiom, p(a)).
                                    |""")
    val out = run("-t", "20", f.getPath)
    assert(out.contains(s"% SZS status GaveUp for ${f.getName}"), s"got:\n$out")
    assert(!out.contains("SZS output start"), s"a saturated run must not print a refutation:\n$out")
  }

  test("an unparsable problem reports SZS Error rather than throwing") {
    val f = problemFile("bad.p", """|this is not TPTP at all (((
                                    |""")
    val out = run("-t", "20", f.getPath)
    assert(out.contains(s"% SZS status Error for ${f.getName}"), s"got:\n$out")
  }

  // ── the emitted derivation ──────────────────────────────────────────────────────────────────────────────

  test("the refutation block is delimited and ends in the empty clause") {
    val f = problemFile("block.p",
      """|cnf(a1, axiom, ( p(X) | q(X) )).
         |cnf(a2, axiom, ~p(a)).
         |cnf(a3, axiom, ~q(a)).
         |""")
    val out = run("-t", "20", f.getPath)
    assert(out.contains(s"% SZS output start CNFRefutation for ${f.getName}"), s"got:\n$out")
    assert(out.contains(s"% SZS output end CNFRefutation for ${f.getName}"), s"got:\n$out")
    val formulas = emittedFormulas(out)
    assert(formulas.nonEmpty, s"no annotated formulas emitted:\n$out")
    assert(formulas.exists(_.contains("$false")), s"the derivation must end in \\$$false:\n$out")
  }

  test("every emitted annotated formula re-parses with the TPTP parser") {
    // The contract that matters: a competition harness re-reads this text. `functor` quoting, `!=` literals,
    // `X<n>` variables and un-mangled distinct objects/numerals all have to survive the round trip.
    val f = problemFile("reparse.p",
      """|cnf(a1, axiom, ( p(X) | q(X) )).
         |cnf(a2, axiom, ~p(a)).
         |cnf(a3, axiom, ( ~q(X) | r(X) )).
         |cnf(a4, axiom, ~r(a)).
         |""")
    val out = run("-t", "20", f.getPath)
    assertReparses("resolution", emittedFormulas(out))
  }

  test("an equality problem's derivation re-parses too (`!=` literals and equality rules)") {
    // Disequality prints as `a != b`, and the rule names (`superposition`, `equality_resolution`, …) sit in
    // the inference record, a different print path from the pure-resolution case above.
    val f = problemFile("eq.p",
      """|cnf(a1, axiom, f(a) = b).
         |cnf(a2, axiom, f(a) != b).
         |""")
    val out = run("-t", "20", f.getPath)
    assert(out.contains("SZS status Unsatisfiable"), s"got:\n$out")
    assertReparses("equality", emittedFormulas(out))
  }

  test("distinct objects and non-identifier names survive the round trip un-mangled") {
    // The parser mangles `"hello world"` to a `$d`-prefixed constant with `$s` for the space; `unmangleSpecial`
    // and `functor` have to put it back, or the emitted proof names a symbol the input never had.
    val f = problemFile("distinct.p",
      """|cnf(d1, axiom, p("hello world")).
         |cnf(d2, axiom, ~p("hello world")).
         |""")
    val out = run("-t", "20", f.getPath)
    assert(out.contains("SZS status Unsatisfiable"), s"got:\n$out")
    val formulas = emittedFormulas(out)
    assert(formulas.exists(_.contains("\"hello world\"")),
      s"the distinct object should print in its source form, not mangled:\n${formulas.mkString("\n")}")
    formulas.foreach { line =>
      assert(!line.contains("$d") && !line.contains("$s"),
        s"parser mangling leaked into the output: $line")
    }
    assertReparses("distinct", formulas)
  }

  // ── generated symbols must survive printing ─────────────────────────────────────────────────────────────
  // The clause lines and the derivation lines are rendered by *different* code paths (`Tptp.render` on kernel
  // expressions vs. `printDerivation` on interned terms). Both must name a symbol the same way, or the
  // emitted proof contradicts itself. Neither problem below is reached by the tests above: they use explicit
  // constants, so only one Skolem ever exists, and they sit far below the naming threshold.

  /** Every distinct functor in the refutation block that starts with `prefix` (`sk`, `nm`, …). */
  private def generatedSymbols(output: String, prefix: String): Set[String] =
    val rx = raw"\b($prefix(?:_\d+)?)\b".r
    emittedFormulas(output).flatMap(l => rx.findAllMatchIn(l).map(_.group(1))).toSet

  /** Two existentials, so clausification mints `sk` and `sk_1`, and the refutation needs both. */
  private val twoSkolems =
    """|fof(a1, axiom, ? [X] : p(X)).
       |fof(a2, axiom, ? [Y] : q(Y)).
       |fof(a3, axiom, ! [Z,W] : ( ~p(Z) | ~q(W) )).
       |"""

  /** Above the naming threshold, with a free variable under the named subformula, so the naming atom is
    * *applied*, `nm_1(X)`. Printed as a variable this is `X0(X1)`, which is not valid TPTP at all. */
  private val appliedNamingAtom =
    """|fof(b1, axiom, ! [X] : ( (a1(X) & c1(X)) | (a2(X) & c2(X)) | (a3(X) & c3(X)) | (a4(X) & c4(X)) | (a5(X) & c5(X)) )).
       |fof(b2, axiom, ! [X] : ~a1(X)).
       |fof(b3, axiom, ! [X] : ~a2(X)).
       |fof(b4, axiom, ! [X] : ~a3(X)).
       |fof(b5, axiom, ! [X] : ~a4(X)).
       |fof(b6, axiom, ! [X] : ~a5(X)).
       |"""

  test("distinct Skolem constants print distinctly (the counter is part of the identity)") {
    // `UncertifiedClausifier` mints them as `sk`, `sk_1`, …, all sharing `id.name`. Rendering by name alone collapses
    // them, and then `q(sk)` does not follow from `? [Y] : q(Y)` at all, since `sk` is already a1's witness.
    // tptp4X cannot see this: the collapsed output is perfectly well-formed TPTP.
    val out = run("-t", "20", problemFile("twoskolem.p", twoSkolems).getPath)
    assert(out.contains("SZS status Unsatisfiable"), s"got:\n$out")
    val sks = generatedSymbols(out, "sk")
    assert(sks.size >= 2, s"two distinct Skolem constants collapsed into ${sks.mkString("{", ",", "}")}:\n$out")
  }

  test("an applied naming atom prints as a functor, not as a TPTP variable") {
    // `freshNamingAtom` returns naming atoms as `Variable`s so `InstSchema` can discharge them; that is an
    // internal representation choice, not a statement that they are TPTP variables.
    val out = run("-t", "20", problemFile("naming_fo.p", appliedNamingAtom).getPath)
    assert(out.contains("SZS status Unsatisfiable"), s"got:\n$out")
    val nms = generatedSymbols(out, "nm")
    assert(nms.nonEmpty, s"expected the naming threshold to fire, but no `nm` atom was emitted:\n$out")
    emittedFormulas(out).foreach { line =>
      assert(!raw"\bX\d+\s*\(".r.findFirstIn(line).isDefined,
        s"a variable is being applied, which is not valid TPTP: $line")
    }
  }

  test("tptp4X accepts every emitted refutation") {
    // The official checker, run offline from the TPTP distribution. Independent of our own parser, and the
    // one CASC applies to a submitted derivation.
    Tptp4X.orCancel("the emitted refutations")
    val problems = Seq(
      "twoskolem.p" -> twoSkolems,
      "naming_fo.p" -> appliedNamingAtom,
      "eq.p" -> """|cnf(a1, axiom, f(a) = b).
                   |cnf(a2, axiom, f(a) != b).
                   |""",
      "distinct.p" -> """|cnf(d1, axiom, p("hello world")).
                         |cnf(d2, axiom, ~p("hello world")).
                         |""")
    for (name, body) <- problems do
      val out = run("-t", "20", problemFile(name, body).getPath)
      val block = emittedFormulas(out)
      assert(block.nonEmpty, s"$name: no refutation emitted:\n$out")
      Tptp4X.check(block.mkString("", "\n", "\n")).foreach { diagnostic =>
        fail(s"$name: tptp4X rejected the emitted refutation:\n$diagnostic\n--- emitted ---\n${block.mkString("\n")}")
      }
  }

  // ── command line ────────────────────────────────────────────────────────────────────────────────────────

  test("unknown flags are ignored and a named strategy is accepted") {
    val f = problemFile("cli.p",
      """|cnf(a1, axiom, p(a)).
         |cnf(a2, axiom, ~p(a)).
         |""")
    val name = Strategy.portfolio.head.name
    val out = run("--some-future-casc-flag", "-t", "20", "--strategy", name, f.getPath)
    assert(out.contains(s"% SZS status Unsatisfiable for ${f.getName}"), s"strategy '$name' run failed:\n$out")
  }
