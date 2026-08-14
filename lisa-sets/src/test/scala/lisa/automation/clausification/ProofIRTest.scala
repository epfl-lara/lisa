package lisa.automation.clausification

import org.scalatest.funsuite.AnyFunSuite

import lisa.utils.K
import lisa.utils.K.{_, given}

/**
 * Tests for the assumption-threading in [[ProofIR]]. A kernel `SCSubproof` inside a `ClausificationProof` is
 * converted exactly like a `ClausificationSubproof` that declares no assumption of its own: it is handed the
 * assumptions in scope, its imports receive them, and only its steps that reach an import are rewritten.
 *
 * Two shapes are worth pinning. A **closed** inner proof has no step reaching an import, so nothing inside it
 * is rewritten and a trailing `Weakening` carries the assumptions to its conclusion. An **import-bearing**
 * inner proof has its imports matched by the kernel against the parent premises discharging them, so the
 * assumptions must reach both sides; this used to be refused outright and is now converted.
 */
class ProofIRTest extends AnyFunSuite:

  private val A = Variable(Identifier("A"), Prop) // the assumption threaded onto the left
  private val B = Variable(Identifier("B"), Prop)
  private val C = Variable(Identifier("C"), Prop)

  // The proofs here are hand-built from real kernel steps, so they must be `Sorry`-free as well as accepted:
  // `isValid` alone would pass for a proof that proves nothing (see `KernelProof`).
  private def isValid(p: SCProof): Boolean =
    K.SCProofChecker.checkSCProof(p) match
      case K.SCProofCheckerJudgement.SCValidProof(_, usesSorry) => !usesSorry
      case _                                                    => false

  /** `proof` under the single assumption `A`, declared as the assumption import at index 0. */
  private def underA(steps: IndexedSeq[ClausificationProofStep], imports: IndexedSeq[Sequent]): SCProof =
    clausificationProofToSCProof(ClausificationProof(steps, (() |- A) +: imports), IndexedSeq(0), IndexedSeq.empty)

  test("a closed nested SCSubproof is converted kernel-valid, with the assumption on the conclusion") {
    // A closed inner proof has no import, so the step holding it has no premise and reaches no import either:
    // nothing about it is rewritten. Being the last step, a trailing Weakening carries `A` to the conclusion.
    val closed = SCProof(IndexedSeq(Hypothesis(B |- B, B)), IndexedSeq.empty) //     B ⊢ B, no imports
    val converted = underA(IndexedSeq(Restate(() |- A, -1), SCSubproof(closed, IndexedSeq.empty)), IndexedSeq.empty)
    assert(isValid(converted), s"the conversion broke a closed nested subproof: ${K.SCProofChecker.checkSCProof(converted)}")
    assert(converted.conclusion.left.contains(A), "the assumption did not reach the conclusion")
  }

  test("an import-bearing nested SCSubproof is converted, not refused") {
    // The inner proof takes `⊢ C` as an import, discharged by step 0 of the outer proof. Step 0 cites an import,
    // so it gains `A`, and the inner import gains `A` as well: the two sides agree and the kernel accepts.
    val withImports = SCProof(IndexedSeq(Restate(() |- C, -1)), IndexedSeq(() |- C))
    val converted = underA(
      IndexedSeq(Restate(() |- C, -2), SCSubproof(withImports, IndexedSeq(0))),
      IndexedSeq(() |- C))
    assert(isValid(converted), s"an import-bearing nested subproof was mis-converted: ${K.SCProofChecker.checkSCProof(converted)}")
    assert(converted.conclusion.left.contains(A), s"conclusion lost the assumption: ${converted.conclusion}")
  }

  test("a nested SCSubproof mixing a reaching and an assumption-free premise is refused") {
    // Premise 1 reaches an import, so the subproof is handed `A` and both of its imports receive it. Premise 0
    // reaches none, so it keeps `C ⊢ C` while the import it discharges now reads `A, C ⊢ C`. The mismatch is
    // caught here rather than by the kernel later. A subproof all of whose premises are assumption-free is not
    // refused: it is simply converted without the assumptions, and both sides agree.
    val withImports = SCProof(IndexedSeq(Restate(C |- C, -1)), IndexedSeq(C |- C, () |- A))
    val e = intercept[IllegalArgumentException](underA(
      IndexedSeq(Hypothesis(C |- C, C), Restate(() |- A, -1), SCSubproof(withImports, IndexedSeq(0, 1))),
      IndexedSeq.empty))
    assert(e.getMessage.contains("never reaches an import"), s"unexpected message: ${e.getMessage}")
  }

  test("with no assumptions the conversion leaves every step untouched") {
    val withImports = SCProof(IndexedSeq(Restate(() |- C, -1)), IndexedSeq(() |- C))
    val steps: IndexedSeq[ClausificationProofStep] =
      IndexedSeq(Restate(() |- C, -1), SCSubproof(withImports, IndexedSeq(0)))
    val converted = clausificationProofToSCProof(ClausificationProof(steps, IndexedSeq(() |- C)))
    assert(isValid(converted))
    // No assumption in scope means no rewriting at all, so the ordinary step is the very same object.
    assert(converted.steps.head eq steps.head)
    assert(converted.conclusion == (() |- C), s"conclusion changed: ${converted.conclusion}")
  }

  // ── selective assumption threading (`clausificationProofToSCProof`) ──────────────────────────────────────────
  // Assumptions are pasted only onto steps whose premise cone reaches an import, since that is the only way
  // one can enter a step. This is what lets `DistributePhase` emit its clause derivation flat without paying
  // a rewritten `Sequent` per step; the shape below is that phase in miniature.

  /** A `ClausificationProof` over one assumption import `⊢ A` and one ordinary import `⊢ B`:
    *   0: `C ⊢ C`      Hypothesis, citing nothing, so it must come out untouched by `A`
    *   1: `⊢ B`        Restate of the ordinary import, which reaches one, so it must gain `A`
    *   2: `B, C ⊢ C`   Cut-free join of the two via Weakening, reaching an import through step 1 */
  private def mixedProof: ClausificationProof =
    ClausificationProof(
      IndexedSeq(
        Hypothesis(C |- C, C), //                                      no premises: assumption-free
        Restate(() |- B, -2), //                                       cites import #2 (`⊢ B`)
        Weakening(Set(B, C) |- C, 0) //                                cites step 0 only
      ),
      IndexedSeq(() |- A, () |- B))

  test("a step whose cone reaches no import keeps its bot; one that reaches an import gains the assumption") {
    val converted = clausificationProofToSCProof(mixedProof, IndexedSeq(0), IndexedSeq.empty)
    assert(isValid(converted), s"selective threading produced an invalid proof: ${K.SCProofChecker.checkSCProof(converted)}")
    // The `RestateTrue` discharging the assumption import is prepended, so the original steps are shifted.
    val bots = converted.steps.map(_.bot)
    assert(bots.exists(s => s.left == Set(C) && s.right == Set(C)),
      s"the import-free Hypothesis should not have been given `A`, got: ${bots.mkString(", ")}")
    assert(bots.exists(s => s.left.contains(A) && s.right == Set(B)),
      s"the step citing an import should have been given `A`, got: ${bots.mkString(", ")}")
  }

  test("the conclusion carries the assumptions even when its own cone reaches no import") {
    // Every step here is import-free, so nothing is rewritten, but the parent matches the converted
    // conclusion against `ClausificationSubproof.bot`, which *does* carry `A`. A trailing Weakening covers it.
    val closed = ClausificationProof(IndexedSeq(Hypothesis(C |- C, C)), IndexedSeq(() |- A))
    val converted = clausificationProofToSCProof(closed, IndexedSeq(0), IndexedSeq.empty)
    assert(isValid(converted), s"invalid: ${K.SCProofChecker.checkSCProof(converted)}")
    assert(converted.conclusion.left.contains(A), s"conclusion lost the assumption: ${converted.conclusion}")
    assert(converted.conclusion.right == Set(C), s"conclusion changed shape: ${converted.conclusion}")
    // And it must agree with what the parent computes for the enclosing step's bot.
    val expected = ClausificationSubproof(closed, IndexedSeq.empty, IndexedSeq(0)).bot
    assert(isSameSequent(converted.conclusion, expected), s"got ${converted.conclusion}, parent expects $expected")
  }
