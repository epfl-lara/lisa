package lisa.automation.superposition

import org.scalatest.funsuite.AnyFunSuite

import lisa.utils.K
import lisa.utils.K.{_, given}
import lisa.automation.clausification.Clausification
import lisa.automation.Problem

/**
 * The preprocessing phases of [[Prover.proveKernel]], which are the only part of the front end that *builds*
 * proof steps rather than moving problems around.
 *
 * Both are easy to get subtly wrong and hard to notice: an import renumbered to the wrong slot still yields a
 * kernel-valid proof, just one that proves something other than what was asked. So each test checks the whole
 * contract -- valid, concludes the goal, imports the caller's hypotheses in order -- not merely that a proof
 * came back.
 */
class ProverTest extends AnyFunSuite:

  private val p = Constant(Identifier("p"), Prop)
  private val q = Constant(Identifier("q"), Prop)
  private val r = Constant(Identifier("r"), Prop)

  private def hyp(e: Expression): K.Sequent = K.Sequent(Set.empty, Set(e))

  /** Every proving entry point owes this: kernel-valid, concluding the goal, importing the hypotheses in order
    * and then the library statements. */
  private def checkContract(proof: K.SCProof, problem: Problem): Unit =
    assert(K.SCProofChecker.checkSCProof(proof).isValid, s"proof is not kernel-valid:\n${proof.toString}")
    val goal = problem.conjecture.getOrElse(K.Sequent(Set.empty, Set.empty))
    assert(K.isSameSequent(proof.conclusion, goal), s"concluded ${proof.conclusion.repr}, expected ${goal.repr}")
    val hyps = problem.hypotheses.toIndexedSeq
    assert(proof.imports.take(hyps.size) == hyps, "the hypotheses must be the leading imports, in order")
    assert(proof.imports.drop(hyps.size) == Clausification.libImports, "the library imports must follow them")

  test("proveKernel: orthologic normalisation is discharged by Restate on each import and on the goal") {
    // `¬¬p ∧ ⊤` and `p ⟹ q` give `q`; the first hypothesis is not in orthologic normal form, so the phase
    // has to bridge the original import to the normalised one it actually clausified.
    val problem = Problem(
      hypotheses = Seq(hyp(and(neg(neg(p)))(top)), hyp(implies(p)(q))),
      conjecture = Some(hyp(q))
    )
    val plain = Prover.proveKernel(problem, SearchOptions(maxGiven = 5000))
    assert(plain.isRight, s"without orthologic: expected a proof, got $plain")
    checkContract(plain.toOption.get, problem)

    val normalised = Prover.proveKernel(problem, SearchOptions(maxGiven = 5000, orthologic = true))
    assert(normalised.isRight, s"with orthologic: expected a proof, got $normalised")
    checkContract(normalised.toOption.get, problem)
  }

  test("proveKernel: orthologic on a problem with no conjecture still concludes the empty sequent") {
    // `p` and `¬p` are contradictory, so the goal is `⊢` and the whole proof is the refutation.
    val problem = Problem(hypotheses = Seq(hyp(p), hyp(neg(p))), conjecture = None)
    val proof = Prover.proveKernel(problem, SearchOptions(maxGiven = 5000, orthologic = true))
    assert(proof.isRight, s"expected a proof, got $proof")
    checkContract(proof.toOption.get, problem)
  }

  test("proveKernel reports the outcome rather than throwing when the goal does not follow") {
    val problem = Problem(hypotheses = Seq(hyp(p)), conjecture = Some(hyp(q)))
    assert(Prover.proveKernel(problem, SearchOptions(maxGiven = 2000)).isLeft, "a non-theorem must come back as Left")
  }

  test("widenImports puts each kept import back in its caller-side slot") {
    // SInE's own gates need 500+ axioms, so the renumbering is exercised directly: an inner proof over
    // hypotheses 1 and 3 of four, plus one library import, presented over all four.
    val all: IndexedSeq[K.Sequent] = IndexedSeq(hyp(p), hyp(q), hyp(r), hyp(and(p)(q)))
    val keep = IndexedSeq(1, 3)
    val lib = Clausification.libImports
    val innerImports = keep.map(all) ++ lib
    // a one-step inner proof restating its first import, so the conclusion is traceable to a known slot
    val inner = K.SCProof(IndexedSeq(K.Restate(innerImports(0), -1)), innerImports)
    val outer = Prover.widenImports(inner, all, keep)

    assert(outer.imports == all ++ lib, "the widened proof must import every caller hypothesis, then the library ones")
    assert(K.SCProofChecker.checkSCProof(outer).isValid, s"widened proof is not kernel-valid:\n${outer.toString}")
    assert(K.isSameSequent(outer.conclusion, inner.conclusion), "widening must not change what is concluded")
    // and the conclusion is the hypothesis that was at slot 1, not at slot 0
    assert(K.isSameSequent(outer.conclusion, all(1)), "the premise must be the kept hypothesis, at its original slot")
  }
