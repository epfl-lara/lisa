package lisa.automation.clausification

import lisa.utils.K.{_, given}
import lisa.automation.Problem
import Clausification.*

/**
 * The last phase: distribute `∨` over `∧` in each quantifier-free NNF matrix `φ` and hand the resulting clauses
 * to the prover.
 *
 * Only `φ ⊢ CNF(φ)` is needed, and its instance `a ∨ (b ∧ c) ⊢ (a ∨ b) ∧ (a ∨ c)` holds in every ortholattice
 * (README §1.3); only the converse needs genuine distributivity. So each clause is one `Weakening` from the
 * hypothesis import, whose rule is `isImplyingSequent`, the kernel's ortholattice entailment. [[clausesOf]]
 * computes the clause set, and nothing takes `φ` apart with primitive steps.
 */
private[clausification] object DistributePhase:

  def certifyDistribute(problem: Problem, prover: ClausificationProver): ClausificationProof =
    require(problem.conjecture.isEmpty, "certifyDistribute expects a conjecture-free problem (consumed by certifyNegated)")
    val hypotheses = problem.hypotheses.toIndexedSeq
    val n = hypotheses.size
    val outerImports = hypotheses ++ libImports

    // Layout: for each hypothesis `() ⊢ φ` (import ref -(i+1)), one `Weakening` per CNF clause. Those become the
    // prover's imports; one final `ClausificationSubproof` wraps the prover call, mapping each clause slot to
    // its `Weakening`.
    val steps      = scala.collection.mutable.ArrayBuffer.empty[ClausificationProofStep]
    val clauseSeqs = scala.collection.mutable.ArrayBuffer.empty[Sequent]
    val clauseRefs = scala.collection.mutable.ArrayBuffer.empty[Int]

    for (i <- 0 until n) {
      checkInterrupted()
      val phi = singleRightFormula(hypotheses(i), "distribute")
      for (clauseSeq <- clausesOf(phi)) {
        steps += Weakening(clauseSeq, -(i + 1)) //                                  a₁, …, aₘ ⊢ b₁, …, bₙ
        clauseRefs += steps.size - 1
        clauseSeqs += clauseSeq
      }
    }

    val newProblem = Problem(clauseSeqs.toList, None, problem.frozen)
    val downstream = prover(newProblem)
    require(sameImportList(downstream.imports, newProblem.imports ++ libImports), "Downstream imports must match transformed problem imports")
    steps += ClausificationSubproof(downstream, clauseRefs.toIndexedSeq ++ libRefs(n))
    ClausificationProof(steps.toIndexedSeq, outerImports)

  /** The clauses of the quantifier-free NNF matrix `φ`, each as `a₁, …, aₘ ⊢ b₁, …, bₙ` (README §1.2): a
   *  negative literal is carried as its atom on the left, a positive one on the right. The sides are separated
   *  at the leaves, as [[UncertifiedClausifier]] does on its own side. */
  def clausesOf(phi: Expression): Seq[Sequent] = {
    checkInterrupted()
    phi match
      case And(a, b) => clausesOf(a) ++ clausesOf(b) //  CNF(a ∧ b) = CNF(a) ∪ CNF(b)
      case Or(a, b) => //                                CNF(a ∨ b) = { cₐ ∪ c_b | cₐ ∈ CNF(a), c_b ∈ CNF(b) }
        val la = clausesOf(a)
        val lb = clausesOf(b)
        for (ca <- la; cb <- lb) yield Sequent(ca.left ++ cb.left, ca.right ++ cb.right)
      case lit =>
        require(isLeaf(lit), s"clausesOf: non-literal leaf in the NNF matrix (expected atom/¬atom/⊤/⊥). " +
          s"An η-reduced `∀(p)`/`∃(p)` reaching here means prenexing did not strip it: β-normalisation " +
          s"η-reduced the body and `Clausification.etaExpandQuantifiers` was not applied. Got: $lit")
        lit match
          case Neg(atom) => Seq(Sequent(Set(atom), Set.empty))
          case _         => Seq(Sequent(Set.empty, Set(lit)))
  }

  /** A literal leaf of an NNF matrix: an atom, a negated atom, or `⊤`/`⊥`, never a connective or quantifier.
    */
  private def isLeaf(f: Expression): Boolean = f match
    case `top` | `bot`                                                                  => true
    case Neg(g)                                                                         => isLeaf(g)
    case And(_, _) | Or(_, _) | Implies(_, _) | Iff(_, _) | Forall(_, _) | Exists(_, _) => false
    case Application(`forall`, _) | Application(`exists`, _)                            => false // η-reduced `∀(p)`
    case _                                                                              => f.sort == Prop
