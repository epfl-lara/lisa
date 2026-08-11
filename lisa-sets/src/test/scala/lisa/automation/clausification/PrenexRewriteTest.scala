package lisa.automation.clausification

import org.scalatest.funsuite.AnyFunSuite

import lisa.utils.K
import lisa.utils.K.{_, given}
import lisa.automation.Tableau
import lisa.kernel.KernelProof

/**
 * Regression tests for the certified prenex *rewrite* strategy (`PrenexPhase.provePrenexRewrite`).
 *
 * The rewrite strategy lifts a nested `∀` across `∧`/`∨` by `InstSchema`-ing one of the four
 * prenex-lifting library statements in [[Clausification]]. Those statements were previously stated
 * with the closed operand as `Q(x)` (a predicate applied to the *bound* variable), which makes them
 * variable-capture **non-theorems** — e.g. `(∀x.P(x)) ∧ Q(x) ⇔ ∀x.(P(x) ∧ Q(x))` is false (take
 * `P ≡ ⊤`, then it reads `Q(x) ⇔ ∀x.Q(x)`). Every certified proof imported them, so the certificate
 * rested on falsehoods; `checkSCProof` only masks this because it validates conditionally on imports.
 *
 * These tests are the coverage that was missing: the existing suite never exercised the rewrite path.
 *   - [[the four prenex-lifting library statements are genuine theorems]] proves each statement
 *     *independently* of any proof that merely imports it — this is the assertion that fails on the
 *     old (capturing) statements and passes on the corrected nullary-`Prop` ones.
 *   - [[provePrenexRewrite ...]] runs the actual rewrite path for all four `LiftLayer` cases and
 *     kernel-checks the produced subproof against the (corrected) statements.
 */
class PrenexRewriteTest extends AnyFunSuite:

  private val prenexStatements: List[(String, K.Sequent)] = List(
    ("forallAndLeft",  Clausification.forallAndLeftStatement),
    ("forallAndRight", Clausification.forallAndRightStatement),
    ("forallOrLeft",   Clausification.forallOrLeftStatement),
    ("forallOrRight",  Clausification.forallOrRightStatement)
  )

  test("the four prenex-lifting library statements are genuine theorems (were capture non-theorems)") {
    for (name, stmt) <- prenexStatements do
      val res = Tableau.solve(stmt)
      assert(res.isDefined, s"$name is NOT provable — Tableau found no proof of $stmt (a capture non-theorem?)")
      val proof = res.get
      KernelProof.assertCorrectProofNoSorry(proof, s"$name (Tableau)")
      assert(proof.conclusion == stmt, s"$name: proof concludes ${proof.conclusion}, expected $stmt")
  }

  test("provePrenexRewrite: each LiftLayer case lifts a nested ∀ and kernel-checks against the library statements") {
    // Predicate/prop *constants* in the source formula, distinct from the statements' schema variables.
    val Pc = Constant(Identifier("Pc", 0), Ind >>: Prop) // unary predicate
    val Ac = Constant(Identifier("Ac", 0), Prop)         // nullary, x-free — the closed sibling
    val x  = Variable(Identifier("x", 0), Ind)
    val fa = forall(Lambda(x, Application(Pc, x)))       // ∀x. Pc(x)

    // One source formula per LiftLayer case: the ∀ nested under one connective, on each side.
    val sources: List[(String, Expression)] = List(
      ("AndL", and(fa)(Ac)), // (∀x.Pc(x)) ∧ Ac
      ("AndR", and(Ac)(fa)), // Ac ∧ (∀x.Pc(x))
      ("OrL",  or(fa)(Ac)),  // (∀x.Pc(x)) ∨ Ac
      ("OrR",  or(Ac)(fa))   // Ac ∨ (∀x.Pc(x))
    )

    for (name, phi) <- sources do
      // Mirror `PrenexPhase.certifyPrenex`'s setup exactly: strip universals to the matrix, then
      // build the rewrite subproof with the library imports at the same fixed positions.
      val counter = Clausification.Counter()
      val (matrix, witnesses) = PrenexPhase.extractUniversalMatrix(phi, counter)
      val ax = () |- phi
      val outerImports = IndexedSeq(ax) ++ Clausification.libImports // [ax] ++ [existsEps, AndL, AndR, OrL, OrR]
      val nonLibSize = 1
      val refs = (
        Clausification.libRef(nonLibSize, Clausification.libForallAndLeftIdx),
        Clausification.libRef(nonLibSize, Clausification.libForallAndRightIdx),
        Clausification.libRef(nonLibSize, Clausification.libForallOrLeftIdx),
        Clausification.libRef(nonLibSize, Clausification.libForallOrRightIdx)
      )
      val sub = PrenexPhase.provePrenex(ax, -1, () |- matrix, witnesses, refs, forceRewrite = true)
      val proof = SCProof(IndexedSeq(sub), outerImports)
      KernelProof.assertCorrectProofNoSorry(proof, s"$name (prenex rewrite path)")
      assert(proof.conclusion == (() |- matrix), s"$name: unexpected conclusion ${proof.conclusion}")
  }

  // ── §1.12: the two strategies are not interchangeable ────────────────────────────────────────────────────
  //
  // `provePrenexRewrite` lifts a `∀` across a connective with one of the four library equivalences, e.g.
  //
  //     (∀x. P(x)) ∧ R   ⇔   ∀x. (P(x) ∧ R)
  //
  // which is a theorem only because `R` is a nullary `Prop` schema and therefore cannot contain `x`. When the
  // sibling *does* contain the binder's identifier free, the lifted formula captures it. `liftOneLayer` builds
  // that capturing target by hand, while the kernel's substitution into the library statement is
  // capture-avoiding, so the two disagree and the final strip yields the wrong matrix.
  //
  // The test above cannot see this: its sibling `Ac` is a nullary constant with no variables at all. Which
  // strategy runs is decided silently by `preferRewriteStrategy`, on formula size — so the same shape passes at
  // one size and fails at the next. The pair below is exactly that: one conjunct apart.

  private val Pc = Constant(Identifier("Pc", 0), Ind >>: Prop)
  private val Qc = Constant(Identifier("Qc", 0), Ind >>: Prop)
  // Deliberately NOT named `x`: that is the library statements' own bound variable (`Clausification.schemaX`),
  // and the defect has nothing to do with it. What matters is that the sibling mentions the *source* formula's
  // binder free, whatever either is called.
  private val zv = Variable(Identifier("z", 0), Ind)
  private val yv = Variable(Identifier("y", 0), Ind)

  /** `(∀z. Pc(z)) ∧ Qc(z)` — the `∀`'s sibling mentions the binder's identifier free. */
  private val capturing: Expression = and(forall(Lambda(zv, Application(Pc, zv))))(Application(Qc, zv))

  /** Run `PrenexPhase`'s own entry point on `phi`, exactly as `certifyPrenex` does, and return the composed
    * proof together with the matrix it is supposed to derive. `forceRewrite` is left at its default, so the
    * strategy is whatever `preferRewriteStrategy` picks — which is the behaviour under test. */
  private def prenexAuto(phi: Expression): (SCProof, Expression) =
    val (matrix, witnesses) = PrenexPhase.extractUniversalMatrix(phi, Clausification.Counter())
    val ax = () |- phi
    val refs = (
      Clausification.libRef(1, Clausification.libForallAndLeftIdx),
      Clausification.libRef(1, Clausification.libForallAndRightIdx),
      Clausification.libRef(1, Clausification.libForallOrLeftIdx),
      Clausification.libRef(1, Clausification.libForallOrRightIdx)
    )
    val sub = PrenexPhase.provePrenex(ax, -1, () |- matrix, witnesses, refs)
    (SCProof(IndexedSeq(sub), IndexedSeq(ax) ++ Clausification.libImports), matrix)

  test("prenex: a capturing sibling is handled at a size that selects the deconstruct strategy") {
    assert(!PrenexPhase.preferRewriteStrategy(capturing),
      "guard: this formula must take the deconstruct path, or it no longer contrasts with the test below")
    val (proof, matrix) = prenexAuto(capturing)
    KernelProof.assertCorrectProofNoSorry(proof, "deconstruct on a capturing sibling")
    assert(proof.conclusion == (() |- matrix))
  }

  test("prenex: the rewrite strategy lifts over a capturing sibling, for each of the four layers") {
    // Before the fix, `liftOneLayer` built the lifted formula as `∀z. (body ⊕ sibling)`, reusing the source
    // binder, which captures the sibling's free `z`. The kernel instantiates `schemaR := sibling`
    // capture-avoidingly, so it produced the correctly renamed formula and the two disagreed: the strip then
    // yielded `Pc(w) ∧ Qc(w) ∧ Qc(y)` where `extractUniversalMatrix` predicted `Pc(w) ∧ Qc(z) ∧ Qc(y)`, and
    // `provePrenex` died on its closing `require`.
    //
    // Each shape is wrapped in one extra conjunct for the sole purpose of pushing `size` past the
    // `size > 4·nq²` threshold, so the strategy chosen differs from the test above and nothing else does.
    val fa = forall(Lambda(zv, Application(Pc, zv)))
    val shapes: List[(String, Expression)] = List(
      ("AndL", and(fa)(Application(Qc, zv))),
      ("AndR", and(Application(Qc, zv))(fa)),
      ("OrL",  or(fa)(Application(Qc, zv))),
      ("OrR",  or(Application(Qc, zv))(fa))
    )
    for (name, inner) <- shapes do
      val phi = and(inner)(Application(Qc, yv))
      assert(PrenexPhase.preferRewriteStrategy(phi), s"$name: guard — this formula must take the rewrite path")
      val (proof, matrix) = prenexAuto(phi)
      KernelProof.assertCorrectProofNoSorry(proof, s"$name (capturing sibling, rewrite path)")
      assert(proof.conclusion == (() |- matrix), s"$name: unexpected conclusion ${proof.conclusion}")
      // the sibling's `z` is a different variable from the ∀'s bound `z` and must still be free in the matrix
      assert(matrix.freeVariables.contains(zv), s"$name: the sibling's free variable was captured — matrix $matrix")
  }
