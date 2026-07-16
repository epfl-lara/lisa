package lisa.automation.clausification

import lisa.utils.K.{_, given}
import Clausification.*

private[clausification] object NegatedPhase:

  def certifyNegated(problem: Problem, prover: ClausificationProver): ClausificationProof =
    problem.conjecture match
      case None => prover(problem)
      case Some(conjecture) =>
        val phi = singleRightFormula(conjecture, "conjecture")
        val negPhi = neg(phi)
        val transformed = Problem(problem.hypotheses :+ (() |- negPhi), None)
        val downstream = prover(transformed)
        require(sameImportList(downstream.imports, transformed.imports ++ libImports), "Downstream imports must match transformed problem imports")

        // Bridge: Hypothesis(φ ⊢ φ) and RightNot(() ⊢ φ, ¬φ), then cut against the
        // downstream subproof of `() ⊢ ¬φ`.
        //
        // This `Cut` is the origin of the clausal-prover contract's *empty-sequent conclusion*
        // requirement (see [[certifyClausal]]): `csub` lifts `negPhi` to its LHS as an assumption
        // and carries the downstream prover's conclusion otherwise unchanged, so for `cutStep`
        // (pivot `negPhi`, t1 = `⊢ φ, ¬φ`) to yield `⊢ φ`, `csub` must be exactly `¬φ ⊢` — i.e.
        // the prover proper must conclude the EMPTY sequent (empty RHS, empty LHS besides `¬φ`).
        val hypStep      = KernelStep(Hypothesis(phi |- phi, phi))
        val rightNotStep = KernelStep(RightNot(() |- (phi, negPhi), 0, phi))
        val csub = ClausificationSubproof(
          downstream,
          problem.hypotheses.indices.map(problem.hypIndex).toIndexedSeq ++ libRefs(problem.imports.size),
          IndexedSeq(Assumption(negPhi, problem.hypotheses.size))
        )
        val cutStep = KernelStep(Cut(() |- phi, 1, 2, negPhi))
        ClausificationProof(IndexedSeq(hypStep, rightNotStep, csub, cutStep), problem.imports ++ libImports)
