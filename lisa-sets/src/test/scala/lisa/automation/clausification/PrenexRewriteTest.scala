package lisa.automation.clausification

import org.scalatest.funsuite.AnyFunSuite

import lisa.utils.K
import lisa.utils.K.{_, given}
import lisa.automation.Tableau

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
      assert(K.SCProofChecker.checkSCProof(proof).isValid, s"$name: Tableau's proof was rejected by the kernel")
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
      val judgement = K.SCProofChecker.checkSCProof(proof)
      assert(judgement.isValid, s"$name: rewrite-path proof rejected by the kernel: $judgement")
      assert(proof.conclusion == (() |- matrix), s"$name: unexpected conclusion ${proof.conclusion}")
  }
