package lisa.automation.superposition

import lisa.automation.clausification.UncertifiedClausifier
import lisa.kernel.KernelProof
import lisa.tptp.KernelParser.problemToKernel
import lisa.tptp.KernelParser.strictMapAtom
import lisa.tptp.KernelParser.strictMapTerm
import lisa.tptp.KernelParser.strictMapVariable
import lisa.tptp.TptpProblem
import lisa.utils.K
import org.scalatest.funsuite.AnyFunSuite

/**
 * Tests for proof reconstruction ([[Reconstruction]] via [[Clausal.solve]] + [[Clausal.reconstruct]]).
 */
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

  /**
   * Reconstruct, then assert the proof is kernel-valid, concludes `⊢`, and imports inputs once each.
   *  `subsumptionResolution` / `condensation` force those simplifications on for the reconstruction check.
   */
  private def check(name: String, clauses: List[K.Sequent], subsumptionResolution: Boolean = false, condensation: Boolean = false): Unit =
    val proof: Option[K.SCProof] = Clausal.refute(
      clauses,
      SearchOptions(forwardSubsumptionResolution = subsumptionResolution, backwardSubsumptionResolution = subsumptionResolution, condensation = condensation, maxGiven = 10000)
    ) match
      case s: Clausal.Outcome.Success => Some(s.reconstructKernelProof)
      case _ => None
    assert(proof.isDefined, s"$name: expected a refutation")
    val p = proof.get
    KernelProof.assertCorrectProofNoSorry(p, name)
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

  test("first-order needing unit deletion: {P(a) ∨ Q(b)}, {¬P(x)}, {¬Q(b)}") {
    val x = vr("X"); val p = pred("P", 1); val q = pred("Q", 1); val a = cst("a"); val b = cst("b")
    // {¬P(x)} unit-deletes P(a) → {Q(b)}, then {¬Q(b)} unit-deletes Q(b) → □. The shrunk clauses are
    // ordinary resolvents, so the proof must still reconstruct to a kernel-valid `⊢`.
    check(
      "unit deletion",
      List(sequent(Set(), Set(ap(p, a), ap(q, b))), sequent(Set(ap(p, x)), Set()), sequent(Set(ap(q, b)), Set()))
    )
  }

  test("first-order needing general subsumption resolution: {¬P(x) ∨ Q(x)}, {P(a) ∨ Q(a) ∨ R(b)}, {¬Q(a)}, {¬R(b)}") {
    val x = vr("X"); val p = pred("P", 1); val q = pred("Q", 1); val r = pred("R", 1); val a = cst("a"); val b = cst("b")
    // {¬P(x), Q(x)} SR-resolves P(a) out of {P(a), Q(a), R(b)} → {Q(a), R(b)} (a multi-literal-side step);
    // then {¬Q(a)}, {¬R(b)} close it. The SR result is an ordinary resolvent, so it must reconstruct.
    check(
      "general SR",
      List(
        sequent(Set(ap(p, x)), Set(ap(q, x))),
        sequent(Set(), Set(ap(p, a), ap(q, a), ap(r, b))),
        sequent(Set(ap(q, a)), Set()),
        sequent(Set(ap(r, b)), Set())
      ),
      subsumptionResolution = true
    )
  }

  test("first-order needing condensation: {P(x) ∨ P(a)}, {¬P(a)}") {
    val x = vr("X"); val p = pred("P", 1); val a = cst("a")
    // {P(x), P(a)} condenses to {P(a)} (a factor of itself), then {¬P(a)} closes it. The condensed clause
    // carries a Factoring justification, so the proof must still reconstruct to a kernel-valid `⊢`.
    check(
      "condensation",
      List(sequent(Set(), Set(ap(p, x), ap(p, a))), sequent(Set(ap(p, a)), Set())),
      condensation = true
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
  // Equality reconstruction: superposition, equality resolution, equality
  // factoring, and demodulation. Each problem is refuted using the equality inferences, and the
  // kernel must accept the reconstructed `RightSubstEq`/`LeftSubstEq`/`LeftRefl` derivation.
  // -----------------------------------------------------------------------------------------

  private def eqK(s: K.Expression, t: K.Expression): K.Expression =
    ap(K.Constant(K.Identifier("="), K.Ind -> (K.Ind -> K.Prop)), s, t)

  test("equality: superposition + equality resolution {f(a)≈a}, {¬(f(f(a))≈a)}") {
    val f = fn("f", 1); val a = cst("a")
    // f(a)≈a rewrites f(f(a))≈a's inner subterm, then equality resolution closes the reflexive disequality
    check("ueq f", List(sequent(Set(), Set(eqK(ap(f, a), a))), sequent(Set(eqK(ap(f, ap(f, a)), a)), Set())))
  }

  test("equality: a group-like rewrite chain {g(x)≈x}, {¬(g(g(b))≈b)}") {
    val g = fn("g", 1); val x = vr("X"); val b = cst("b")
    check("ueq g", List(sequent(Set(), Set(eqK(ap(g, x), x))), sequent(Set(eqK(ap(g, ap(g, b)), b)), Set())))
  }

  test("equality: two axioms superposing {f(x)≈g(x)}, {g(a)≈b}, {¬(f(a)≈b)}") {
    val f = fn("f", 1); val g = fn("g", 1); val a = cst("a"); val b = cst("b"); val x = vr("X")
    check(
      "ueq fg",
      List(
        sequent(Set(), Set(eqK(ap(f, x), ap(g, x)))),
        sequent(Set(), Set(eqK(ap(g, a), b))),
        sequent(Set(eqK(ap(f, a), b)), Set())
      )
    )
  }

  test("equality: equality resolution needing unification {¬(f(x)≈f(a))}, plus a fact using x") {
    val f = fn("f", 1); val a = cst("a"); val x = vr("X"); val p = pred("P", 1)
    // {¬P(x) ∨ f(x)≉f(a)} : eq-resolution unifies x↦a leaving ¬P(a); then {P(a)} closes it
    check(
      "eqres",
      List(
        sequent(Set(ap(p, x), eqK(ap(f, x), ap(f, a))), Set()),
        sequent(Set(), Set(ap(p, a)))
      )
    )
  }

  test("equality: a non-unit equality clause exercising factoring {a≈b ∨ a≈c}, {¬(a≈b)}, {¬(a≈c)}, {¬(b≈c)}") {
    val a = cst("a"); val b = cst("b"); val c = cst("c")
    check(
      "factoring",
      List(
        sequent(Set(), Set(eqK(a, b), eqK(a, c))),
        sequent(Set(eqK(a, b)), Set()),
        sequent(Set(eqK(a, c)), Set()),
        sequent(Set(eqK(b, c)), Set())
      )
    )
  }

  // -----------------------------------------------------------------------------------------
  // Reconstruction over real TPTP problems: the 20 easy SYN clausal problems.
  // Located via the TPTP env var (the TPTP root); cancelled (not failed) when it is unset.
  // -----------------------------------------------------------------------------------------

  // Resolved per test through [[TptpCorpus]], which warns loudly the first time the corpus is missing rather
  // than letting ~40 cancellations pass under an "All tests passed" headline.

  private val synProblems: List[String] = List(
    "SYN048-1.p",
    "SYN064-1.p",
    "SYN073-1.p",
    "SYN339-1.p",
    "SYN340-1.p",
    "SYN341-1.p",
    "SYN731-1.p",
    "SYN034-1.p",
    "SYN035-1.p",
    "SYN049-1.p",
    "SYN063-2.p",
    "SYN081-1.p",
    "SYN333-1.p",
    "SYN338-1.p",
    "SYN343-1.p",
    "SYN727-1.p",
    "SYN033-1.p",
    "SYN051-1.p",
    "SYN079-1.p",
    "SYN315-1.p"
  )

  synProblems.foreach { name =>
    test(s"SYN reconstruction: $name is refuted and the proof is kernel-valid") {
      val f = new java.io.File(TptpCorpus.subdirOrCancel("Problems/SYN", "the SYN reconstruction suite"), name)
      assume(f.exists, s"$f not found")
      val problem: TptpProblem = problemToKernel(f)(using (strictMapAtom, strictMapTerm, strictMapVariable))
      val proof: Option[K.SCProof] = Clausal.solve(UncertifiedClausifier.clausalForm(Prover.fromTptp(problem)), SearchOptions(maxGiven = 50000)) match
        case s: Clausal.Outcome.Success => Some(s.reconstructKernelProof)
        case _ => None
      assert(proof.isDefined, s"$name: expected a refutation")
      val p = proof.get
      KernelProof.assertCorrectProofNoSorry(p, name)
      assert(p.conclusion == emptySequent, s"$name: conclusion is not the empty sequent: ${p.conclusion}")
      assert(p.imports.distinct.length == p.imports.length, s"$name: an input clause was imported more than once")
    }
  }
