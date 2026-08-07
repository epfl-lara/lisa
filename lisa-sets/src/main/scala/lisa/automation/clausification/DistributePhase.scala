package lisa.automation.clausification

import lisa.utils.K.{_, given}
import Clausification.*

/**
 * Final clausification phase: **distributivity**. Runs last (after prenexing), turning each quantifier-free
 * NNF hypothesis matrix `φ` (a tree of `∧`/`∨` over literals) into its CNF clauses by distributing `∨` over
 * `∧`, and feeding the resulting literal-set clauses to the prover. This mirrors the uncertified
 * [[FastClausify]] (naming → NNF → Skolem → distribute); the earlier threshold-gated naming
 * ([[CertifiedFastClausifier.certifyFastNaming]]) is what keeps the `∨`-product — and hence this phase —
 * polynomial.
 *
 * '''Why it certifies cheaply.''' The forward direction `φ ⊢ CNF(φ)` (equivalently
 * `a∨(b∧c) ⊢ (a∨b)∧(a∨c)`) is the lattice inequality that holds in *every* ortholattice — only the reverse
 * `CNF(φ) ⊢ φ` needs true distributivity and fails orthologic. So each output clause `φ ⊢ Cᵢ` is derivable
 * with primitive kernel rules alone — no fresh symbols, no library lemmas, no schema instantiation:
 *   - a literal `L` : `Hypothesis(L ⊢ L)`
 *   - `a ∧ b`       : one `LeftAnd` lifts a child clause proof `a ⊢ c` (or `b ⊢ c`) to `a∧b ⊢ c`
 *   - `a ∨ b`       : one `LeftOr` joins `a ⊢ cₐ` and `b ⊢ c_b` to `a∨b ⊢ cₐ∪c_b` (the checker's `subset`
 *                     test absorbs the weakening of each side to the joined clause)
 * Each hypothesis `() ⊢ φ` then yields the clause sequent `() ⊢ Cᵢ` by `Cut(φ)` against the axiom import.
 */
private[clausification] object DistributePhase:

  def certifyDistribute(problem: Problem, prover: ClausificationProver): ClausificationProof =
    require(problem.conjecture.isEmpty, "certifyDistribute expects a conjecture-free problem (consumed by certifyNegated)")
    val hypotheses = problem.hypotheses.toIndexedSeq
    val n = hypotheses.size
    val outerImports = hypotheses ++ libImports

    // Flat layout: for each hypothesis `() ⊢ φ` (import ref -(i+1)), emit one `SCSubproof(φ ⊢ Cᵢ)` + `Cut`
    // per CNF clause, producing the clause sequent `() ⊢ Cᵢ`. Those become the prover's imports; one final
    // `ClausificationSubproof` wraps the prover call, mapping each clause slot to its `Cut` step.
    val steps      = scala.collection.mutable.ArrayBuffer.empty[ClausificationProofStep]
    val clauseSeqs = scala.collection.mutable.ArrayBuffer.empty[Sequent]
    val clauseRefs = scala.collection.mutable.ArrayBuffer.empty[Int]

    for (i <- 0 until n) {
      checkInterrupted()
      val phi = singleRightFormula(hypotheses(i), "distribute")
      for ((litSet, clauseProof) <- distributeClauses(phi)) {
        val clauseSeq = Sequent(Set.empty, litSet)
        steps += KernelStep(SCSubproof(clauseProof, IndexedSeq.empty)) //          φ ⊢ Cᵢ
        val spRef = steps.size - 1
        steps += KernelStep(Cut(clauseSeq, -(i + 1), spRef, phi)) //               () ⊢ Cᵢ
        clauseRefs += steps.size - 1
        clauseSeqs += clauseSeq
      }
    }

    val newProblem = Problem(clauseSeqs.toList, None, problem.frozen)
    val downstream = prover(newProblem)
    require(sameImportList(downstream.imports, newProblem.imports ++ libImports), "Downstream imports must match transformed problem imports")
    steps += ClausificationSubproof(downstream, clauseRefs.toIndexedSeq ++ libRefs(n))
    ClausificationProof(steps.toIndexedSeq, outerImports)

  /** Clauses of a quantifier-free NNF matrix `φ`, each as `(clauseLiterals, SCProof of φ ⊢ clause)`.
   *  Proofs are self-contained (no imports). The number of clauses is bounded by the earlier naming pass. */
  def distributeClauses(phi: Expression): Seq[(Set[Expression], SCProof)] = {
    checkInterrupted()
    phi match
      case And(a, b) =>
        // CNF(a ∧ b) = CNF(a) ∪ CNF(b); lift each child clause `child ⊢ c` to `a∧b ⊢ c`.
        distributeClauses(a).map { case (c, p) => (c, liftAnd(p, a, b, c)) } ++
          distributeClauses(b).map { case (c, p) => (c, liftAnd(p, a, b, c)) }
      case Or(a, b) =>
        // CNF(a ∨ b) = { cₐ ∪ c_b | cₐ ∈ CNF(a), c_b ∈ CNF(b) }; join with LeftOr.
        val la = distributeClauses(a)
        val lb = distributeClauses(b)
        for ((cA, pA) <- la; (cB, pB) <- lb) yield (cA ++ cB, joinOr(pA, a, pB, b, cA ++ cB))
      case lit =>
        require(isLeaf(lit), s"distributeClauses: non-literal leaf in the NNF matrix (expected atom/¬atom/⊤/⊥): $lit")
        Seq((Set(lit), SCProof(IndexedSeq(Hypothesis(lit |- lit, lit)), IndexedSeq.empty)))
  }

  /** From a child proof `child ⊢ c` (child = `a` or `b`) build `a∧b ⊢ c` with one `LeftAnd`. */
  private def liftAnd(child: SCProof, a: Expression, b: Expression, c: Set[Expression]): SCProof =
    SCProof(IndexedSeq(
      SCSubproof(child, IndexedSeq.empty),
      LeftAnd(Sequent(Set(and(a)(b)), c), 0, a, b)
    ), IndexedSeq.empty)

  /** From `a ⊢ cA` and `b ⊢ cB` build `a∨b ⊢ c` (with `cA ⊆ c` and `cB ⊆ c`) with one `LeftOr`. */
  private def joinOr(pA: SCProof, a: Expression, pB: SCProof, b: Expression, c: Set[Expression]): SCProof =
    SCProof(IndexedSeq(
      SCSubproof(pA, IndexedSeq.empty),
      SCSubproof(pB, IndexedSeq.empty),
      LeftOr(Sequent(Set(or(a)(b)), c), Seq(0, 1), Seq(a, b))
    ), IndexedSeq.empty)

  /** A literal leaf of an NNF matrix: an atom, a negated atom, or `⊤`/`⊥` — never a connective/quantifier. */
  private def isLeaf(f: Expression): Boolean = f match
    case `top` | `bot`                                                                 => true
    case Neg(g)                                                                         => isLeaf(g)
    case And(_, _) | Or(_, _) | Implies(_, _) | Iff(_, _) | Forall(_, _) | Exists(_, _) => false
    case _                                                                              => f.sort == Prop
