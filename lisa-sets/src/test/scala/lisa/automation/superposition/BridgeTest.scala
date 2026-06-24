package lisa.automation.superposition

import org.scalatest.funsuite.AnyFunSuite

import lisa.utils.K
import lisa.tptp.{Problem, AnnotatedStatement}
import lisa.tptp.KernelParser.{annotatedStatementToKernel, problemToKernel, emptyctx, strictMapAtom, strictMapTerm, strictMapVariable}

/**
 * Tests for the kernel/TPTP entry points ([[Bridge]]).
 *
 * NOTE on the TPTP suite: the TPTP `SYN` problem library is not bundled in this repo (no `TPTP`
 * environment variable, and project scope forbids adding a shared test-resources directory), so the
 * clausal problems below are built from inline TPTP `cnf`/`fof` clauses parsed by Lisa's real TPTP
 * parser. The final test additionally loads a genuine `cnf` problem from a `.p` file (written to a
 * temp file), exercising `lisa.tptp.problemToKernel`. To run against the real SYN collection, set the
 * `TPTP` env var and call `Bridge.solveProblem(problemToKernel(File(...)))`.
 */
class BridgeTest extends AnyFunSuite:

  // --- kernel construction helpers ----------------------------------------------------------
  private def sortOf(arity: Int, base: K.Sort): K.Sort = (0 until arity).foldRight(base)((_, acc) => K.Ind -> acc)
  private def pred(name: String, arity: Int): K.Expression = K.Constant(K.Identifier(name), sortOf(arity, K.Prop))
  private def fn(name: String, arity: Int): K.Expression = K.Constant(K.Identifier(name), sortOf(arity, K.Ind))
  private def cst(name: String): K.Expression = fn(name, 0)
  private def vr(name: String): K.Expression = K.Variable(K.Identifier(name), K.Ind)
  private def ap(f: K.Expression, args: K.Expression*): K.Expression = args.foldLeft(f)((acc, a) => K.Application(acc, a))
  private def sequent(left: Set[K.Expression], right: Set[K.Expression]): K.Sequent = K.Sequent(left, right)

  // --- entry point 1: kernel sequents -------------------------------------------------------

  test("kernel sequents: {P} and {¬P} are refuted") {
    val p = pred("P", 0)
    // {P} = ⊢ P ; {¬P} = P ⊢
    assert(Bridge.solve(List(sequent(Set(), Set(p)), sequent(Set(p), Set())), maxGiven = 10000))
  }

  test("kernel sequents: the empty sequent is the empty clause (refuted)") {
    assert(Bridge.solve(List(sequent(Set(), Set())), maxGiven = 10000))
  }

  test("kernel sequents: a satisfiable set is not refuted") {
    val pa = ap(pred("P", 1), cst("a"))
    val qb = ap(pred("Q", 1), cst("b"))
    assert(!Bridge.solve(List(sequent(Set(), Set(pa)), sequent(Set(), Set(qb))), maxGiven = 10000))
  }

  test("kernel sequents: first-order resolution refutes") {
    val x = vr("X")
    val px = ap(pred("P", 1), x); val qx = ap(pred("Q", 1), x)
    val pa = ap(pred("P", 1), cst("a")); val qa = ap(pred("Q", 1), cst("a"))
    // {¬P(x), Q(x)} = P(x) ⊢ Q(x) ; {P(a)} = ⊢ P(a) ; {¬Q(a)} = Q(a) ⊢
    val cs = List(sequent(Set(px), Set(qx)), sequent(Set(), Set(pa)), sequent(Set(qa), Set()))
    assert(Bridge.solve(cs, maxGiven = 10000))
  }

  test("kernel sequents: propositional refutation needing several resolutions") {
    val p = pred("P", 0); val q = pred("Q", 0)
    // {P∨Q} = ⊢ P,Q ; {¬P} = P ⊢ ; {¬Q} = Q ⊢
    val cs = List(sequent(Set(), Set(p, q)), sequent(Set(p), Set()), sequent(Set(q), Set()))
    assert(Bridge.solve(cs, maxGiven = 10000))
  }

  // --- entry point 2: lisa.tptp.Problem -----------------------------------------------------

  private def parse(clause: String): AnnotatedStatement =
    annotatedStatementToKernel(clause)(using emptyctx, (strictMapAtom, strictMapTerm, strictMapVariable))

  private def problem(name: String, status: String, clauses: String*): Problem =
    Problem("inline", "SYN", name, status, Seq("CNF"), clauses.map(parse).toIndexedSeq)

  private val unsatisfiable: List[Problem] = List(
    problem("UNS_prop_1", "Unsatisfiable", "fof(a1, axiom, p).", "fof(a2, axiom, ~p)."),
    problem("UNS_prop_2", "Unsatisfiable", "fof(a1, axiom, (p | q)).", "fof(a2, axiom, ~p).", "fof(a3, axiom, ~q)."),
    problem(
      "UNS_prop_3",
      "Unsatisfiable",
      "fof(a1, axiom, (p | q)).",
      "fof(a2, axiom, (~p | q)).",
      "fof(a3, axiom, (p | ~q)).",
      "fof(a4, axiom, (~p | ~q))."
    ),
    problem("UNS_prop_4", "Unsatisfiable", "fof(a1, axiom, ((p | q) )).", "fof(a2, axiom, (~p | r)).", "fof(a3, axiom, (~q | r)).", "fof(a4, axiom, ~r)."),
    problem("UNS_fo_1", "Unsatisfiable", "fof(a1, axiom, ![X]: (~p(X) | q(X))).", "fof(a2, axiom, p(a)).", "fof(a3, axiom, ~q(a))."),
    problem(
      "UNS_fo_chain",
      "Unsatisfiable",
      "fof(a1, axiom, ![X]: (~p(X) | q(X))).",
      "fof(a2, axiom, ![X]: (~q(X) | r(X))).",
      "fof(a3, axiom, p(a)).",
      "fof(a4, axiom, ~r(a))."
    ),
    problem("UNS_fo_fun", "Unsatisfiable", "fof(a1, axiom, ![X]: (~p(X) | p(f(X)))).", "fof(a2, axiom, p(a)).", "fof(a3, axiom, ~p(f(f(a))))."),
    problem("UNS_factoring", "Unsatisfiable", "fof(a1, axiom, ![X,Y]: (p(X) | p(Y))).", "fof(a2, axiom, ![U,V]: (~p(U) | ~p(V)))."),
    problem("UNS_two_const", "Unsatisfiable", "fof(a1, axiom, ![X]: q(X)).", "fof(a2, axiom, ~q(c)).")
  )

  private val satisfiable: List[Problem] = List(
    problem("SAT_prop_1", "Satisfiable", "fof(a1, axiom, p).", "fof(a2, axiom, q)."),
    problem("SAT_prop_2", "Satisfiable", "fof(a1, axiom, (p | q)).", "fof(a2, axiom, ~p)."),
    problem("SAT_fo_1", "Satisfiable", "fof(a1, axiom, p(a)).", "fof(a2, axiom, q(b))."),
    problem("SAT_fo_2", "Satisfiable", "fof(a1, axiom, ![X]: (~p(X) | q(X))).", "fof(a2, axiom, p(a)).")
  )

  test("tptp problems: unsatisfiable clausal problems are refuted") {
    unsatisfiable.foreach(pr => assert(Bridge.solveProblem(pr, maxGiven = 20000), s"expected a refutation for ${pr.name}"))
  }

  test("tptp problems: satisfiable clausal problems are not refuted") {
    satisfiable.foreach(pr => assert(!Bridge.solveProblem(pr, maxGiven = 20000), s"expected no refutation for ${pr.name}"))
  }

  test("tptp problem loaded from a real cnf .p file is refuted") {
    val content =
      """% File     : TMP001-1 : Test
        |% Domain   : Test
        |% Problem  : a trivial propositional contradiction
        |% Status   : Unsatisfiable
        |% SPC      : CNF_UNS_EPR
        |cnf(a1, axiom, ( p )).
        |cnf(a2, negated_conjecture, ( ~ p )).
        |""".stripMargin
    val f: java.io.File = java.io.File.createTempFile("superposition_tptp_", ".p")
    try
      java.nio.file.Files.write(f.toPath, content.getBytes("UTF-8"))
      val pr: Problem = problemToKernel(f)(using (strictMapAtom, strictMapTerm, strictMapVariable))
      assert(Bridge.solveProblem(pr, maxGiven = 10000))
    finally f.delete()
  }
