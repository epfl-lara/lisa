package lisa.automation.clausification

import lisa.utils.K.{_, given}
import Clausification.*

private[clausification] object NegatedPhase:

  def certifyNegated(problem: Problem, prover: ClausificationProver): ClausificationProof =
    problem.conjecture match
      case None => prover(problem)
      case Some(conjecture) =>
        val phi = singleRightFormula(conjecture, "conjecture")
        // Universally close the conjecture's free INDIVIDUAL variables before negating: a goal `φ(x̄)` means
        // `∀x̄. φ(x̄)`, so its negation is `∃x̄. ¬φ`, which the clausifier Skolemizes to fresh CONSTANTS — the
        // textbook goal handling. (Negating `φ(x̄)` as-is keeps x̄ as universal clause variables, i.e. refuting
        // only `∃x̄.φ`, which would not reconstruct into the intended `⊢ φ(x̄)`.) Non-`Ind` free variables
        // (predicate/function schemas) stay free — they are uninterpreted symbols, not object variables.
        val freeInd: Seq[Variable] = phi.freeVariables.toSeq.filter(_.sort == Ind).sortBy(_.id.toString)
        val phiClosed = freeInd.foldRight(phi)((v, acc) => forall(Lambda(v, acc)))
        val negPhi = neg(phiClosed)
        val transformed = Problem(problem.hypotheses :+ (() |- negPhi), None, problem.frozen)
        val downstream = prover(transformed)
        require(sameImportList(downstream.imports, transformed.imports ++ libImports), "Downstream imports must match transformed problem imports")

        // Bridge: Hypothesis(phiClosed ⊢ phiClosed) and RightNot(⊢ phiClosed, ¬phiClosed), then cut against the
        // downstream subproof of `¬phiClosed ⊢`. As in the closed case, `csub` lifts `negPhi` to its LHS and
        // carries the prover's conclusion otherwise unchanged, so for the cut (pivot `negPhi`) to yield
        // `⊢ phiClosed`, `csub` must be exactly `¬phiClosed ⊢` — i.e. the prover proper concludes the EMPTY
        // sequent (this is the origin of the clausal-prover contract's empty-sequent requirement).
        val steps = scala.collection.mutable.ArrayBuffer.empty[ClausificationProofStep]
        steps += KernelStep(Hypothesis(phiClosed |- phiClosed, phiClosed)) //           0
        steps += KernelStep(RightNot(() |- (phiClosed, negPhi), 0, phiClosed)) //        1: ⊢ phiClosed, ¬phiClosed
        steps += ClausificationSubproof( //                                             2: ¬phiClosed ⊢
          downstream,
          problem.hypotheses.indices.map(problem.hypIndex).toIndexedSeq ++ libRefs(problem.imports.size),
          IndexedSeq(Assumption(negPhi, problem.hypotheses.size))
        )
        steps += KernelStep(Cut(() |- phiClosed, 1, 2, negPhi)) //                       3: ⊢ phiClosed = ⊢ ∀x̄.φ

        if freeInd.nonEmpty then
          // Reinstantiate: recover the original goal sequent `⊢ φ(x̄)` from `⊢ ∀x̄.φ`, via the lemma
          // `∀x̄.φ ⊢ φ` (Hypothesis + one LeftForall per free variable, each instantiating the bound variable
          // back to its free self) and a final Cut on `∀x̄.φ`.
          val hyp2 = steps.length
          steps += KernelStep(Hypothesis(phi |- phi, phi)) //                            4: φ ⊢ φ
          var prev = hyp2
          var body: Expression = phi
          val n = freeInd.size
          var k = 0
          while k < n do
            val v = freeInd(n - 1 - k) //                                                innermost quantifier first
            val next = forall(Lambda(v, body))
            steps += KernelStep(LeftForall(Sequent(Set(next), Set(phi)), prev, body, v, v))
            prev = steps.length - 1
            body = next
            k += 1
          // `body` == `phiClosed`; step `prev` proves `phiClosed ⊢ φ`.
          steps += KernelStep(Cut(() |- phi, 3, prev, phiClosed)) //                      ⊢ φ (the original goal)

        ClausificationProof(steps.toIndexedSeq, problem.imports ++ libImports)
