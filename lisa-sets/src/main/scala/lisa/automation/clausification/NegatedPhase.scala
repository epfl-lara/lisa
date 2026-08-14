package lisa.automation.clausification

import lisa.utils.K.{_, given}
import Clausification.*

/**
 * Conjecture negation: move `φ` to the hypotheses as `¬φ` and hand a conjecture-free problem downstream.
 *
 * A goal `φ(x̄)` asserts `∀x̄. φ(x̄)`, so its free `Ind` variables must not be refutable by instantiation: the
 * prover would then close on the weaker `∃x̄. φ`. They are therefore added to `frozen`, which every phase
 * threads and which [[lisa.automation.superposition.Clausal]] turns into the prover's `symbolVars`, so they
 * reach the search as symbols rather than clause variables. This is what ∀-closing and Skolemizing them would
 * achieve, at no cost: no `∃` is introduced, so no Skolem definition and no reinstantiation are needed.
 *
 * The bridge below cuts the downstream subproof against the tautology `⊢ φ, ¬φ` on the pivot `¬φ`, and that cut
 * yields `⊢ φ` only if the subproof concludes exactly `¬φ ⊢`, which is where the prover contract's
 * empty-sequent requirement comes from.
 */
private[clausification] object NegatedPhase:

  def certifyNegated(problem: Problem, prover: ClausificationProver): ClausificationProof =
    problem.conjecture match
      case None => prover(problem)
      case Some(conjecture) =>
        val phi = singleRightFormula(conjecture, "conjecture")
        val freeInd: Set[Variable] = phi.freeVariables.filter(_.sort == Ind)
        val negPhi = neg(phi)
        val transformed = Problem(problem.hypotheses :+ (() |- negPhi), None, problem.frozen ++ freeInd)
        val downstream = prover(transformed)
        require(sameImportList(downstream.imports, transformed.imports ++ libImports), "Downstream imports must match transformed problem imports")

        // `csub` lifts `negPhi` to its LHS and carries the prover's conclusion otherwise unchanged, so for the
        // cut (pivot `negPhi`) to yield `⊢ φ`, `csub` must be exactly `¬φ ⊢`.
        val steps = scala.collection.mutable.ArrayBuffer.empty[ClausificationProofStep]
        steps += RestateTrue(() |- (phi, negPhi)) //                                    0: ⊢ φ, ¬φ
        steps += ClausificationSubproof( //                                             1: ¬φ ⊢
          downstream,
          problem.hypotheses.indices.map(problem.hypIndex).toIndexedSeq ++ libRefs(problem.imports.size),
          IndexedSeq(problem.hypotheses.size)
        )
        steps += Cut(() |- phi, 0, 1, negPhi) //                                        2: ⊢ φ (the original goal)

        ClausificationProof(steps.toIndexedSeq, problem.imports ++ libImports)
