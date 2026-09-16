package lisa.automation.clausification

import lisa.automation.Problem
import lisa.utils.K.{_, given}

import Clausification._

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

  def certifyDistribute(problem: Problem, prover: ClausificationProver, goal: Set[Int] = Set.empty)(using o: ClausifierOptions): ClausificationProof =
    require(problem.conjecture.isEmpty, "certifyDistribute expects a conjecture-free problem (consumed by certifyNegated)")
    val hypotheses = problem.hypotheses.toIndexedSeq
    val n = hypotheses.size
    val outerImports = hypotheses ++ libImports

    // Layout: for each hypothesis `() ⊢ φ` (import ref -(i+1)), the steps deriving its CNF clauses. Those become
    // the prover's imports; one final `ClausificationSubproof` wraps the prover call, mapping each clause slot to
    // the step concluding it.
    val steps = scala.collection.mutable.ArrayBuffer.empty[ClausificationProofStep]
    val clauseSeqs = scala.collection.mutable.ArrayBuffer.empty[Sequent]
    val clauseRefs = scala.collection.mutable.ArrayBuffer.empty[Int]
    // The goal as clause indices: the clauses of the hypotheses in `goal`.
    val goalClauses = scala.collection.mutable.HashSet.empty[Int]

    for (i <- 0 until n) {
      checkInterrupted()
      val phi = singleRightFormula(hypotheses(i), "distribute")
      o.distribute match
        case Distribute.Weakening =>
          for (clauseSeq <- clausesOf(phi)) {
            steps += Weakening(clauseSeq, -(i + 1)) //                              a₁, …, aₘ ⊢ b₁, …, bₙ
            clauseRefs += steps.size - 1
            if goal.contains(i) then goalClauses += clauseSeqs.size
            clauseSeqs += clauseSeq
          }
        case Distribute.Primitive =>
          // Each clause arrives as `φ, a₁, …, aₘ ⊢ b₁, …, bₙ`, so one `Cut` against the import discharges `φ`.
          for ((negative, positive, ref) <- byPrimitiveRules(phi, steps)) {
            val clauseSeq = Sequent(negative, positive)
            steps += Cut(clauseSeq, -(i + 1), ref, phi)
            clauseRefs += steps.size - 1
            if goal.contains(i) then goalClauses += clauseSeqs.size
            clauseSeqs += clauseSeq
          }
    }

    val newProblem = Problem(clauseSeqs.toList, None, problem.frozen)
    val downstream = prover(newProblem, goalClauses.toSet)
    require(sameImportList(downstream.imports, newProblem.imports ++ libImports), "Downstream imports must match transformed problem imports")
    steps += ClausificationSubproof(downstream, clauseRefs.toIndexedSeq ++ libRefs(n))
    ClausificationProof(steps.toIndexedSeq, outerImports)

  /**
   * The clauses of the quantifier-free NNF matrix `φ`, each as `a₁, …, aₘ ⊢ b₁, …, bₙ` (README §1.2): a
   *  negative literal is carried as its atom on the left, a positive one on the right. The sides are separated
   *  at the leaves, as [[UncertifiedClausifier]] does on its own side.
   */
  def clausesOf(phi: Expression): Seq[Sequent] = {
    checkInterrupted()
    phi match
      case And(a, b) => clausesOf(a) ++ clausesOf(b) //  CNF(a ∧ b) = CNF(a) ∪ CNF(b)
      case Or(a, b) => //                                CNF(a ∨ b) = { cₐ ∪ c_b | cₐ ∈ CNF(a), c_b ∈ CNF(b) }
        val la = clausesOf(a)
        val lb = clausesOf(b)
        for (ca <- la; cb <- lb) yield Sequent(ca.left ++ cb.left, ca.right ++ cb.right)
      // `⊤` and `⊥` are absorbed rather than kept as literals, as in [[UncertifiedClausifier]]. Dropping a
      // clause is sound since each is its own `Weakening`, and the `∨` product propagates `⊤ ∨ b ≡ ⊤`.
      case `top` => Seq.empty
      case `bot` => Seq(Sequent(Set.empty, Set.empty)) //     the empty clause
      case lit =>
        require(
          isLeaf(lit),
          s"clausesOf: non-literal leaf in the NNF matrix (expected atom/¬atom/⊤/⊥). " +
            s"An η-reduced `∀(p)`/`∃(p)` reaching here means prenexing did not strip it: β-normalisation " +
            s"η-reduced the body and `Clausification.etaExpandQuantifiers` was not applied. Got: $lit"
        )
        lit match
          case Neg(atom) => Seq(Sequent(Set(atom), Set.empty))
          case _ => Seq(Sequent(Set.empty, Set(lit)))
  }

  /**
   * The clauses of [[clausesOf]], each derived from `φ` by `LeftAnd`, `LeftOr`, `Hypothesis` and `LeftNot`
   * instead of one `Weakening`. Appends to `steps` and returns, per clause, its two sides and the step concluding
   * `φ, negative ⊢ positive`. Step count grows with products up the `∧`/`∨` tree, not with the clause count.
   */
  def byPrimitiveRules(
      phi: Expression,
      steps: scala.collection.mutable.ArrayBuffer[ClausificationProofStep]
  ): Seq[(Set[Expression], Set[Expression], Int)] =
    checkInterrupted()
    def emit(step: SCProofStep): Int = { steps += step; steps.size - 1 }
    phi match
      case And(a, b) =>
        val conjunction = and(a)(b)
        def lift(clause: (Set[Expression], Set[Expression], Int)) =
          val (negative, positive, ref) = clause
          (negative, positive, emit(LeftAnd(Sequent(negative + conjunction, positive), ref, a, b)))
        byPrimitiveRules(a, steps).map(lift) ++ byPrimitiveRules(b, steps).map(lift)
      case Or(a, b) =>
        val disjunction = or(a)(b)
        val la = byPrimitiveRules(a, steps)
        val lb = byPrimitiveRules(b, steps)
        for ((negA, posA, rA) <- la; (negB, posB, rB) <- lb) yield
          val negative = negA ++ negB
          val positive = posA ++ posB
          (negative, positive, emit(LeftOr(Sequent(negative + disjunction, positive), Seq(rA, rB), Seq(a, b))))
      case lit =>
        require(isLeaf(lit), s"byPrimitiveRules: non-literal leaf in the NNF matrix. Got: $lit")
        lit match
          // `¬a` goes left as its atom: `a ⊢ a` then `LeftNot` gives `¬a, a ⊢`.
          case Neg(atom) =>
            val hyp = emit(Hypothesis(atom |- atom, atom))
            Seq((Set(atom), Set.empty[Expression], emit(LeftNot(Sequent(Set(lit, atom), Set.empty), hyp, atom))))
          case _ => Seq((Set.empty[Expression], Set(lit), emit(Hypothesis(lit |- lit, lit))))

  /**
   * A literal leaf of an NNF matrix: an atom, a negated atom, or `⊤`/`⊥`, never a connective or quantifier.
   */
  private def isLeaf(f: Expression): Boolean = f match
    case `top` | `bot` => true
    case Neg(g) => isLeaf(g)
    case And(_, _) | Or(_, _) | Implies(_, _) | Iff(_, _) | Forall(_, _) | Exists(_, _) => false
    case Application(`forall`, _) | Application(`exists`, _) => false // η-reduced `∀(p)`
    case _ => f.sort == Prop
