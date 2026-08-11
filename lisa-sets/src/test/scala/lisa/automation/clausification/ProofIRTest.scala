package lisa.automation.clausification

import org.scalatest.funsuite.AnyFunSuite

import lisa.utils.K
import lisa.utils.K.{_, given}

/**
 * Tests for the assumption-threading in [[ProofIR]] — specifically the shallow `SCSubproof` rewrite in
 * `lowerKernelProofWithAssumptions`, which appends one `Weakening` to a nested subproof instead of pushing the
 * assumptions through all of its steps.
 *
 * That shortcut is sound exactly when the nested proof is **closed**. Its inner *steps* not carrying the
 * assumptions is harmless (the `Weakening` legitimises it), but an inner *import* is matched by the kernel
 * against the parent premise discharging it, and that premise does receive the assumptions — so an
 * import-bearing nested subproof would be silently lowered into a kernel-rejected step. These tests pin both
 * halves: the closed case stays valid, and the import-bearing case is refused loudly at build time rather
 * than producing a proof the kernel will reject much later.
 */
class ProofIRTest extends AnyFunSuite:

  private val A = Variable(Identifier("A"), Prop) // the assumption threaded onto the left
  private val B = Variable(Identifier("B"), Prop)
  private val C = Variable(Identifier("C"), Prop)

  // The proofs here are hand-built from real kernel steps, so they must be `Sorry`-free as well as accepted —
  // `isValid` alone would pass for a proof that proves nothing (see `KernelProof`).
  private def isValid(p: SCProof): Boolean =
    K.SCProofChecker.checkSCProof(p) match
      case K.SCProofCheckerJudgement.SCValidProof(_, usesSorry) => !usesSorry
      case _                                                    => false

  test("a closed nested SCSubproof survives the shallow rewrite kernel-valid") {
    val closed = SCProof(IndexedSeq(Hypothesis(B |- B, B)), IndexedSeq.empty) //     B ⊢ B, no imports
    val outer = SCProof(IndexedSeq(SCSubproof(closed, IndexedSeq.empty)), IndexedSeq.empty)
    assert(isValid(outer))
    val lowered = lowerKernelProofWithAssumptions(outer, Seq(A))
    assert(isValid(lowered), s"lowering broke a closed nested subproof: ${K.SCProofChecker.checkSCProof(lowered)}")
    assert(lowered.conclusion.left.contains(A), "the assumption did not reach the conclusion")
  }

  test("an import-bearing nested SCSubproof is refused rather than silently lowered to an invalid step") {
    // The inner proof takes `⊢ C` as an import, discharged by step 0 of the outer proof. Lowering weakens
    // step 0 to `A ⊢ C` but leaves the inner import at `⊢ C` — the kernel then rejects the SCSubproof with
    // "Premise step #0 is not the same as import #0 of the subproof".
    val withImports = SCProof(IndexedSeq(Restate(() |- C, -1)), IndexedSeq(() |- C))
    val outer = SCProof(
      IndexedSeq(Restate(() |- C, -1), SCSubproof(withImports, IndexedSeq(0))),
      IndexedSeq(() |- C))
    assert(isValid(outer), "the un-lowered proof should be valid — only the lowering is at issue")
    val e = intercept[IllegalArgumentException](lowerKernelProofWithAssumptions(outer, Seq(A)))
    assert(e.getMessage.contains("nested SCSubproof must be closed"))
  }

  test("with no assumptions the lowering is the identity, whatever the subproof shape") {
    val withImports = SCProof(IndexedSeq(Restate(() |- C, -1)), IndexedSeq(() |- C))
    val outer = SCProof(
      IndexedSeq(Restate(() |- C, -1), SCSubproof(withImports, IndexedSeq(0))),
      IndexedSeq(() |- C))
    // Same reference, so the guard is not even reached: the empty-assumption fast path returns `proof` as-is.
    assert(lowerKernelProofWithAssumptions(outer, Seq.empty) eq outer)
  }

  // ── selective assumption threading (`lowerClausificationProof`) ──────────────────────────────────────────
  // Assumptions are pasted only onto steps whose premise cone reaches an import, since that is the only way
  // one can enter a step. This is what lets `DistributePhase` emit its clause derivation flat without paying
  // a rewritten `Sequent` per step; the shape below is that phase in miniature.

  /** A `ClausificationProof` over one assumption import `⊢ A` and one ordinary import `⊢ B`:
    *   0: `C ⊢ C`      Hypothesis — cites nothing, so it must come out untouched by `A`
    *   1: `⊢ B`        Restate of the ordinary import — reaches an import, so it must gain `A`
    *   2: `B, C ⊢ C`   Cut-free join of the two via Weakening — reaches an import through step 1 */
  private def mixedProof: ClausificationProof =
    ClausificationProof(
      IndexedSeq(
        KernelStep(Hypothesis(C |- C, C)), //                          no premises: assumption-free
        KernelStep(Restate(() |- B, -2)), //                           cites import #2 (`⊢ B`)
        KernelStep(Weakening(Set(B, C) |- C, 0)) //                    cites step 0 only
      ),
      IndexedSeq(() |- A, () |- B))

  test("a step whose cone reaches no import keeps its bot; one that reaches an import gains the assumption") {
    val lowered = lowerClausificationProof(mixedProof, IndexedSeq(Assumption(A, 0)), IndexedSeq.empty)
    assert(isValid(lowered), s"selective threading produced an invalid proof: ${K.SCProofChecker.checkSCProof(lowered)}")
    // The `Hypothesis(φ ⊢ φ)` discharging the assumption import is prepended, so the original steps are shifted.
    val bots = lowered.steps.map(_.bot)
    assert(bots.exists(s => s.left == Set(C) && s.right == Set(C)),
      s"the import-free Hypothesis should not have been given `A`, got: ${bots.mkString(", ")}")
    assert(bots.exists(s => s.left.contains(A) && s.right == Set(B)),
      s"the step citing an import should have been given `A`, got: ${bots.mkString(", ")}")
  }

  test("the conclusion carries the assumptions even when its own cone reaches no import") {
    // Every step here is import-free, so nothing is rewritten — but the parent matches the lowered
    // conclusion against `ClausificationSubproof.bot`, which *does* carry `A`. A trailing Weakening covers it.
    val closed = ClausificationProof(IndexedSeq(KernelStep(Hypothesis(C |- C, C))), IndexedSeq(() |- A))
    val lowered = lowerClausificationProof(closed, IndexedSeq(Assumption(A, 0)), IndexedSeq.empty)
    assert(isValid(lowered), s"invalid: ${K.SCProofChecker.checkSCProof(lowered)}")
    assert(lowered.conclusion.left.contains(A), s"conclusion lost the assumption: ${lowered.conclusion}")
    assert(lowered.conclusion.right == Set(C), s"conclusion changed shape: ${lowered.conclusion}")
    // And it must agree with what the parent computes for the enclosing step's bot.
    val expected = ClausificationSubproof(closed, IndexedSeq.empty, IndexedSeq(Assumption(A, 0))).bot
    assert(isSameSequent(lowered.conclusion, expected), s"got ${lowered.conclusion}, parent expects $expected")
  }
