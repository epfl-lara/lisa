package lisa.automation.clausification

import lisa.utils.K.{_, given}
import Clausification.*

/**
 * Conjecture negation — the phase that turns a *proof* obligation into a *refutation* one. It moves the
 * conjecture `φ` to the hypothesis list as `¬∀x̄.φ` and hands a conjecture-free problem downstream; every phase
 * below therefore `require`s `problem.conjecture.isEmpty`, and a `None` conjecture makes this phase a
 * pass-through.
 *
 * Two things here are load-bearing for the rest of the pipeline.
 *
 * '''The free variables are ∀-closed before negating.''' A Lisa goal `φ(x̄)` asserts `∀x̄. φ(x̄)`, so what must be
 * refuted is `∃x̄. ¬φ` — which Skolemizes to fresh *constants*. Negating `φ(x̄)` as it stands would leave x̄ as
 * universal clause variables, i.e. refute only `∃x̄. φ`, a strictly weaker claim that does not reconstruct into
 * `⊢ φ(x̄)`. Non-`Ind` free variables (predicate and function schemas) are left free: they are uninterpreted
 * symbols, not object variables. [[UncertifiedClausifier.clausalFormWithOrigins]] repeats this for the uncertified path.
 *
 * '''This is where the clausal-prover contract's empty-sequent requirement comes from.''' The bridge below cuts
 * the downstream subproof against `RightNot(⊢ φ, ¬φ)` on the pivot `¬φ`, so for the cut to yield `⊢ φ` the
 * downstream [[ClausificationSubproof]] must conclude exactly `¬φ ⊢` — meaning the prover proper must conclude
 * the *empty* sequent, not merely something falsity-shaped.
 */
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
