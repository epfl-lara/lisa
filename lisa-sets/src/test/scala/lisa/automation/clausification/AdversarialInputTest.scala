package lisa.automation.clausification

import org.scalatest.funsuite.AnyFunSuite

import lisa.utils.K
import lisa.utils.K.{_, given}
import Clausification.Problem

/**
 * Adversarial inputs to the certified clausifier: the cases its `require`s exist for.
 *
 * The pipeline is dense with preconditions (well-formed input sequents, phase-ordering invariants, and a
 * documented contract on the prover it is handed), and none of them had a test. An untested `require` is a
 * comment with a runtime cost: it may already be unreachable, it may fire on inputs it was not meant to
 * catch, and nothing notices if a refactor removes it. These tests pin each one to the input that trips it.
 *
 * Each negative test asserts a substring of the message, not merely that *something* threw. That is
 * what makes the check meaningful: several of these inputs trip more than one `require` on their way down (a malformed sequent
 * would also fail a later phase's import check), so without pinning the text a test can keep passing while
 * silently moving to a different, later boundary, which is exactly the property being tested. What the
 * preconditions buy is a clean, diagnosable `IllegalArgumentException` *at the right boundary* rather than a
 * kernel rejection thousands of steps later; a prover that breaks `sameImportList`'s contract otherwise
 * surfaces as an unexplained invalid proof. The two tests with no substring check are the positive controls,
 * which have no exception to inspect.
 */
class AdversarialInputTest extends AnyFunSuite:

  private val a = Variable(Identifier("a"), Prop)
  private val b = Variable(Identifier("b"), Prop)
  private val x = Variable(Identifier("x"), Ind)
  private val P = Variable(Identifier("Pp"), Ind >>: Prop)

  /** A prover meeting `certifyClausal`'s contract: imports = the clause sequents, conclusion = `⊢`. */
  private def sorryProver(p: Problem): SCProof =
    SCProof(IndexedSeq(Sorry(Sequent(Set.empty, Set.empty))), p.imports)

  /** The same, as a phase-level [[ClausificationProver]]. A phase expects its downstream to declare the
    * library statements too. `certifyClausal`'s wrapper appends them, so a test calling a phase directly
    * has to do it itself or trip the phase's own import check. */
  private def sorryPhaseProver(p: Problem): ClausificationProof =
    val sc = sorryProver(p)
    ClausificationProof(sc.steps, sc.imports ++ Clausification.libImports)

  private def clausify(problem: Problem, prover: Problem => SCProof = sorryProver): SCProof =
    CertifiedClausifier.certifyClausal(problem, prover)

  // ── malformed input sequents ────────────────────────────────────────────────────────────────────────────
  // Every phase reads its axioms through `singleRightFormula`, which demands `⊢ φ` exactly. These are the
  // shapes a caller can hand in from outside the package, so they are the ones worth catching by name.

  test("a hypothesis with a non-empty left-hand side is rejected") {
    val e = intercept[IllegalArgumentException](clausify(Problem(Seq(Sequent(Set(a), Set(b))), Some(() |- a))))
    assert(e.getMessage.contains("empty left-hand side"), s"unexpected message: ${e.getMessage}")
  }

  test("a hypothesis with two right-hand formulas is rejected") {
    val e = intercept[IllegalArgumentException](clausify(Problem(Seq(Sequent(Set.empty, Set(a, b))), Some(() |- a))))
    assert(e.getMessage.contains("single formula on the right-hand side"), s"unexpected message: ${e.getMessage}")
  }

  test("a hypothesis with no right-hand formula is rejected") {
    val e = intercept[IllegalArgumentException](clausify(Problem(Seq(Sequent(Set.empty, Set.empty)), Some(() |- a))))
    assert(e.getMessage.contains("single formula on the right-hand side"), s"unexpected message: ${e.getMessage}")
  }

  test("a malformed conjecture is rejected just as a malformed hypothesis is") {
    val e = intercept[IllegalArgumentException](clausify(Problem(Seq.empty, Some(Sequent(Set(a), Set(b))))))
    assert(e.getMessage.contains("empty left-hand side"), s"unexpected message: ${e.getMessage}")
  }

  // ── the prover contract ─────────────────────────────────────────────────────────────────────────────────
  // `certifyClausal` documents what the prover it is given must return. A prover that breaks the contract is
  // the most likely *external* fault, being the one part of the pipeline a caller supplies.

  test("a prover that drops a clause import is caught at the boundary, not as an invalid proof") {
    // Contract: imports == the clause sequents, pointwise. Declaring only the clauses the refutation used is
    // the tempting mistake, and without this check it surfaces much later as a kernel rejection.
    val dropsAnImport: Problem => SCProof = p =>
      SCProof(IndexedSeq(Sorry(Sequent(Set.empty, Set.empty))), p.imports.drop(1))
    val problem = Problem(Seq(() |- a, () |- b), Some(() |- a))
    val e = intercept[IllegalArgumentException](clausify(problem, dropsAnImport))
    assert(e.getMessage.contains("imports"), s"unexpected message: ${e.getMessage}")
  }

  test("a prover that invents an extra import is caught too") {
    val addsAnImport: Problem => SCProof = p =>
      SCProof(IndexedSeq(Sorry(Sequent(Set.empty, Set.empty))), p.imports :+ (() |- b))
    val e = intercept[IllegalArgumentException](clausify(Problem(Seq(() |- a), Some(() |- a)), addsAnImport))
    assert(e.getMessage.contains("imports"), s"unexpected message: ${e.getMessage}")
  }

  test("a well-behaved prover on the same problems is accepted, so the checks above are not vacuous") {
    // Guards the four negative tests: if `sorryProver` were itself rejected they would all pass for the
    // wrong reason.
    val proof = clausify(Problem(Seq(() |- a, () |- b), Some(() |- a)))
    assert(proof.conclusion == (() |- a), s"unexpected conclusion: ${proof.conclusion.repr}")
  }

  // ── phase-ordering invariants ───────────────────────────────────────────────────────────────────────────
  // Each phase below `certifyNegated` requires the conjecture to have been consumed already. These are not
  // reachable through `certifyClausal`; they pin the composition order, so a rewiring fails loudly here
  // rather than producing a proof of the wrong thing.

  test("a phase below the negation step rejects a problem that still carries a conjecture") {
    val withConjecture = Problem(Seq(() |- a), Some(() |- b))
    for (name, phase) <- Seq[(String, Problem => Any)](
      "certifyDistribute" -> (DistributePhase.certifyDistribute(_, sorryPhaseProver)),
      "certifySkolem" -> (SkolemPhase.certifySkolem(_, sorryPhaseProver)),
      "certifyPrenex" -> (PrenexPhase.certifyPrenex(_, sorryPhaseProver))
    ) do
      val e = intercept[IllegalArgumentException](phase(withConjecture))
      assert(e.getMessage.contains("conjecture-free"), s"$name: unexpected message: ${e.getMessage}")
  }

  test("a non-NNF matrix reaching the distribution phase is rejected, not silently mis-clausified") {
    // `⟹` should have been eliminated by naming and NNF long before here. Without the check it falls through
    // to the literal case and becomes a one-literal "clause" whose literal is a whole implication, a wrong
    // clause set, and the resulting proof would fail far away from the cause.
    for bad <- Seq(implies(a)(b), forall(Lambda(x, P(x))), exists(Lambda(x, P(x))), a <=> b) do
      val e = intercept[IllegalArgumentException](
        DistributePhase.certifyDistribute(Problem(Seq(() |- bad), None), sorryPhaseProver))
      assert(e.getMessage.contains("non-literal leaf"), s"for $bad: unexpected message: ${e.getMessage}")
  }

  test("a genuine NNF matrix passes the same phase, so the leaf check is not rejecting everything") {
    val ok = or(a)(and(b)(neg(a)))
    val proof = DistributePhase.certifyDistribute(Problem(Seq(() |- ok), None), sorryPhaseProver)
    assert(proof.steps.nonEmpty)
  }

  // ── ProofIR construction invariants ─────────────────────────────────────────────────────────────────────
  // `ClausificationSubproof` splits its inner proof's imports into assumptions and parent-discharged
  // premises. Getting that split wrong would mis-index every reference inside the converted subproof, so it is
  // checked at construction rather than discovered during the conversion.

  test("a subproof whose assumptions and premises do not account for every import is rejected") {
    val inner = ClausificationProof(IndexedSeq(Hypothesis(a |- a, a)), IndexedSeq(() |- a, () |- b))
    val e = intercept[IllegalArgumentException](ClausificationSubproof(inner, IndexedSeq.empty, IndexedSeq(0)))
    assert(e.getMessage.contains("account for all imports"), s"unexpected message: ${e.getMessage}")
  }

  test("an assumption index outside the inner proof's imports is rejected") {
    val inner = ClausificationProof(IndexedSeq(Hypothesis(a |- a, a)), IndexedSeq(() |- a))
    val e = intercept[IllegalArgumentException](ClausificationSubproof(inner, IndexedSeq.empty, IndexedSeq(7)))
    assert(e.getMessage.contains("out of range"), s"unexpected message: ${e.getMessage}")
  }

  test("two assumptions naming the same import are rejected") {
    val inner = ClausificationProof(IndexedSeq(Hypothesis(a |- a, a)), IndexedSeq(() |- a, () |- b))
    val e = intercept[IllegalArgumentException](
      ClausificationSubproof(inner, IndexedSeq.empty, IndexedSeq(0, 0)))
    assert(e.getMessage.contains("distinct"), s"unexpected message: ${e.getMessage}")
  }

  test("an empty clausification proof is rejected (its conclusion is its last step)") {
    val e = intercept[IllegalArgumentException](ClausificationProof(IndexedSeq.empty, IndexedSeq.empty))
    assert(e.getMessage.contains("at least one step"), s"unexpected message: ${e.getMessage}")
  }
