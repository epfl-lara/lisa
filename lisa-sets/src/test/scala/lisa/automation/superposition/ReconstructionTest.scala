package lisa.automation.superposition

import org.scalatest.funsuite.AnyFunSuite

import lisa.utils.K
import lisa.tptp.Problem
import lisa.tptp.KernelParser.{problemToKernel, strictMapAtom, strictMapTerm, strictMapVariable}

/** Tests for proof reconstruction ([[Reconstruction]] via [[Bridge.proveAndReconstruct]]). */
class ReconstructionTest extends AnyFunSuite:

  // kernel construction helpers (clauses as sequents: negative atoms left, positive right)
  private def sortOf(arity: Int, base: K.Sort): K.Sort = (0 until arity).foldRight(base)((_, acc) => K.Ind -> acc)
  private def pred(name: String, arity: Int): K.Expression = K.Constant(K.Identifier(name), sortOf(arity, K.Prop))
  private def fn(name: String, arity: Int): K.Expression = K.Constant(K.Identifier(name), sortOf(arity, K.Ind))
  private def cst(name: String): K.Expression = fn(name, 0)
  private def vr(name: String): K.Expression = K.Variable(K.Identifier(name), K.Ind)
  private def ap(f: K.Expression, args: K.Expression*): K.Expression = args.foldLeft(f)((acc, a) => K.Application(acc, a))
  private def sequent(left: Set[K.Expression], right: Set[K.Expression]): K.Sequent = K.Sequent(left, right)

  private val emptySequent: K.Sequent = K.Sequent(Set.empty, Set.empty)

  /** Reconstruct, then assert the proof is kernel-valid, concludes `⊢`, and imports inputs once each. */
  private def check(name: String, clauses: List[K.Sequent]): Unit =
    val proof = Bridge.proveAndReconstruct(clauses, maxGiven = 10000)
    assert(proof.isDefined, s"$name: expected a refutation")
    val p = proof.get
    assert(K.SCProofChecker.checkSCProof(p).isValid, s"$name: proof rejected by the kernel: ${K.SCProofChecker.checkSCProof(p)}")
    assert(p.conclusion == emptySequent, s"$name: conclusion is not the empty sequent: ${p.conclusion}")
    assert(p.imports.toSet.subsetOf(clauses.toSet), s"$name: imports are not among the input clauses")
    // memoisation: a clause reused across the DAG is imported/expanded once, never duplicated
    assert(p.imports.distinct.length == p.imports.length, s"$name: an input clause was imported more than once")

  test("propositional: {P}, {¬P}") {
    val p = pred("P", 0)
    check("P/¬P", List(sequent(Set(), Set(p)), sequent(Set(p), Set())))
  }

  test("propositional: {P∨Q}, {¬P}, {¬Q}") {
    val p = pred("P", 0); val q = pred("Q", 0)
    check("P∨Q chain", List(sequent(Set(), Set(p, q)), sequent(Set(p), Set()), sequent(Set(q), Set())))
  }

  test("propositional: 2-colouring unsat needs all four clauses (DAG sharing)") {
    val p = pred("P", 0); val q = pred("Q", 0)
    // {P∨Q}, {¬P∨Q}, {P∨¬Q}, {¬P∨¬Q} -- jointly unsatisfiable, every clause used
    check(
      "2-colouring",
      List(
        sequent(Set(), Set(p, q)),
        sequent(Set(p), Set(q)),
        sequent(Set(q), Set(p)),
        sequent(Set(p, q), Set())
      )
    )
  }

  test("first-order: {¬P(x), Q(x)}, {P(a)}, {¬Q(a)}") {
    val x = vr("X")
    val px = ap(pred("P", 1), x); val qx = ap(pred("Q", 1), x)
    val pa = ap(pred("P", 1), cst("a")); val qa = ap(pred("Q", 1), cst("a"))
    check("FO chain", List(sequent(Set(px), Set(qx)), sequent(Set(), Set(pa)), sequent(Set(qa), Set())))
  }

  test("first-order with a function term: {¬P(x), P(f(x))}, {P(a)}, {¬P(f(f(a)))}") {
    val x = vr("X"); val f = fn("f", 1); val a = cst("a")
    val p = pred("P", 1)
    val px = ap(p, x); val pfx = ap(p, ap(f, x))
    val pa = ap(p, a); val pffa = ap(p, ap(f, ap(f, a)))
    check("FO fun", List(sequent(Set(px), Set(pfx)), sequent(Set(), Set(pa)), sequent(Set(pffa), Set())))
  }

  test("first-order needing factoring: {P(x) ∨ P(y)}, {¬P(a) ∨ ¬P(b)}") {
    val x = vr("X"); val y = vr("Y"); val p = pred("P", 1); val a = cst("a"); val b = cst("b")
    check(
      "factoring",
      List(sequent(Set(), Set(ap(p, x), ap(p, y))), sequent(Set(ap(p, a), ap(p, b)), Set()))
    )
  }

  test("propositional: longer implication chain {P},{¬P∨Q},{¬Q∨R},{¬R∨S},{¬S}") {
    val p = pred("P", 0); val q = pred("Q", 0); val r = pred("R", 0); val s = pred("S", 0)
    check(
      "chain",
      List(
        sequent(Set(), Set(p)),
        sequent(Set(p), Set(q)),
        sequent(Set(q), Set(r)),
        sequent(Set(r), Set(s)),
        sequent(Set(s), Set())
      )
    )
  }

  test("propositional: a three-literal clause {¬P∨¬Q∨R},{P},{Q},{¬R}") {
    val p = pred("P", 0); val q = pred("Q", 0); val r = pred("R", 0)
    check(
      "3-literal",
      List(
        sequent(Set(p, q), Set(r)),
        sequent(Set(), Set(p)),
        sequent(Set(), Set(q)),
        sequent(Set(r), Set())
      )
    )
  }

  test("first-order: binary predicate with symmetry {R(a,b)}, {¬R(x,y)∨R(y,x)}, {¬R(b,a)}") {
    val r = pred("R", 2); val x = vr("X"); val y = vr("Y"); val a = cst("a"); val b = cst("b")
    check(
      "binary",
      List(
        sequent(Set(), Set(ap(r, a, b))),
        sequent(Set(ap(r, x, y)), Set(ap(r, y, x))),
        sequent(Set(ap(r, b, a)), Set())
      )
    )
  }

  test("first-order: nested functions reusing a clause {¬P(f(x))∨P(x)}, {P(f(f(a)))}, {¬P(a)}") {
    val p = pred("P", 1); val f = fn("f", 1); val x = vr("X"); val a = cst("a")
    check(
      "nested",
      List(
        sequent(Set(ap(p, ap(f, x))), Set(ap(p, x))),
        sequent(Set(), Set(ap(p, ap(f, ap(f, a))))),
        sequent(Set(ap(p, a)), Set())
      )
    )
  }

  // -----------------------------------------------------------------------------------------
  // Reconstruction over real TPTP problems: the 20 easy SYN clausal problems.
  // Located via the TPTP env var (the TPTP root); cancelled (not failed) when it is unset.
  // -----------------------------------------------------------------------------------------

  private val synDir: Option[java.io.File] =
    sys.env.get("TPTP").map(t => new java.io.File(t, "Problems/SYN")).filter(_.isDirectory)

  private val synProblems: List[String] = List(
    "SYN048-1.p", "SYN064-1.p", "SYN073-1.p", "SYN339-1.p", "SYN340-1.p",
    "SYN341-1.p", "SYN731-1.p", "SYN034-1.p", "SYN035-1.p", "SYN049-1.p",
    "SYN063-2.p", "SYN081-1.p", "SYN333-1.p", "SYN338-1.p", "SYN343-1.p",
    "SYN727-1.p", "SYN033-1.p", "SYN051-1.p", "SYN079-1.p", "SYN315-1.p"
  )

  synProblems.foreach { name =>
    test(s"SYN reconstruction: $name is refuted and the proof is kernel-valid") {
      assume(synDir.isDefined, "set the TPTP env var (TPTP root) to run the SYN reconstruction suite")
      val f = new java.io.File(synDir.get, name)
      assume(f.exists, s"$f not found")
      val problem: Problem = problemToKernel(f)(using (strictMapAtom, strictMapTerm, strictMapVariable))
      val proof = Bridge.proveAndReconstructProblem(problem, maxGiven = 50000)
      assert(proof.isDefined, s"$name: expected a refutation")
      val p = proof.get
      assert(K.SCProofChecker.checkSCProof(p).isValid, s"$name: kernel rejected the proof: ${K.SCProofChecker.checkSCProof(p)}")
      assert(p.conclusion == emptySequent, s"$name: conclusion is not the empty sequent: ${p.conclusion}")
      assert(p.imports.distinct.length == p.imports.length, s"$name: an input clause was imported more than once")
    }
  }
