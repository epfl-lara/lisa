package lisa.automation.clausification

import lisa.utils.K.{_, given}
import Clausification.*

/**
 * The last phase: distribute `∨` over `∧` in each quantifier-free NNF matrix `φ` and hand the resulting clauses
 * to the prover. Only `φ ⊢ CNF(φ)` is needed, which holds in OL (README §1.3), so a clause
 * `N ⊢ P` is derived from primitive rules alone: `Hypothesis` at a positive literal, `Hypothesis` plus
 * `LeftNot` at a negative one to put its atom on the left, one `LeftAnd` to lift a child derivation, one
 * `LeftOr` to join two (whose `subset` check absorbs the weakening of each premise to the joined clause), and a
 * closing `Cut` against the hypothesis import to drop `φ` from the left.
 *
 * '''Why the derivation is emitted flat.''' Under `a ∨ b` the derivation of `a`'s clause is a premise of every
 * one of the `|CNF(b)|` joins. Nested `SCSubproof`s would present it as that many occurrences, and although
 * they share one object in memory, `SCProofChecker` walks each, so re-checking multiplies up the `∧`/`∨` tree.
 * [[distributeClauses]] therefore emits one flat step list where each derivation exists once and later steps
 * cite it by index, making the step count linear in the clause count.
 */
private[clausification] object DistributePhase:

  def certifyDistribute(problem: Problem, prover: ClausificationProver): ClausificationProof =
    require(problem.conjecture.isEmpty, "certifyDistribute expects a conjecture-free problem (consumed by certifyNegated)")
    val hypotheses = problem.hypotheses.toIndexedSeq
    val n = hypotheses.size
    val outerImports = hypotheses ++ libImports

    // Layout: for each hypothesis `() ⊢ φ` (import ref -(i+1)), splice in the derivation of every CNF clause,
    // then one `Cut` per clause turning `φ, N ⊢ P` into the clause sequent `N ⊢ P`. Those become the prover's
    // imports; one final `ClausificationSubproof` wraps the prover call, mapping each clause slot to its `Cut`.
    val steps      = scala.collection.mutable.ArrayBuffer.empty[ClausificationProofStep]
    val clauseSeqs = scala.collection.mutable.ArrayBuffer.empty[Sequent]
    val clauseRefs = scala.collection.mutable.ArrayBuffer.empty[Int]

    for (i <- 0 until n) {
      checkInterrupted()
      val phi = singleRightFormula(hypotheses(i), "distribute")
      for ((negative, positive, clauseRef) <- distributeClauses(phi, steps)) {
        val clauseSeq = Sequent(negative, positive)
        steps += Cut(clauseSeq, -(i + 1), clauseRef, phi) //                        a₁, …, aₘ ⊢ b₁, …, bₙ
        clauseRefs += steps.size - 1
        clauseSeqs += clauseSeq
      }
    }

    val newProblem = Problem(clauseSeqs.toList, None, problem.frozen)
    val downstream = prover(newProblem)
    require(sameImportList(downstream.imports, newProblem.imports ++ libImports), "Downstream imports must match transformed problem imports")
    steps += ClausificationSubproof(downstream, clauseRefs.toIndexedSeq ++ libRefs(n))
    ClausificationProof(steps.toIndexedSeq, outerImports)

  /** Append to `steps` the derivation of every clause of the quantifier-free NNF matrix `φ`, returning each
   *  clause as its pair of literal sides (negative atoms, positive literals) together with the index in `steps`
   *  of the step concluding `φ, negative ⊢ positive`.
   *
   *  The two sides are separated at the leaves rather than at the end, so that every intermediate sequent is
   *  already in the emitted clause shape (README §1.2) and the closing `Cut` against the
   *  hypothesis import removes `φ` and leaves the clause. The alternative, deriving `φ ⊢ literals` and moving
   *  the negations afterwards, would need one extra `Restate` per clause.
   *
   *  Appends to the *caller's* buffer rather than returning its own, so the indices it hands back are already
   *  absolute; collecting them separately would mean rebuilding every step to re-base its premises. See the
   *  class doc for why the derivation is flat. */
  def distributeClauses(phi: Expression, steps: scala.collection.mutable.ArrayBuffer[ClausificationProofStep]): Seq[(Set[Expression], Set[Expression], Int)] = {
    checkInterrupted()
    def emit(step: SCProofStep): Int = { steps += step; steps.size - 1 }
    phi match
      case And(a, b) =>
        // CNF(a ∧ b) = CNF(a) ∪ CNF(b); lift each child clause `child, N ⊢ P` to `a∧b, N ⊢ P` with one `LeftAnd`.
        val conjunction = and(a)(b)
        def lift(clause: (Set[Expression], Set[Expression], Int)): (Set[Expression], Set[Expression], Int) =
          val (negative, positive, ref) = clause
          (negative, positive, emit(LeftAnd(Sequent(negative + conjunction, positive), ref, a, b)))
        val la = distributeClauses(a, steps).map(lift)
        la ++ distributeClauses(b, steps).map(lift)
      case Or(a, b) =>
        // CNF(a ∨ b) = { cₐ ∪ c_b | cₐ ∈ CNF(a), c_b ∈ CNF(b) }; join with `LeftOr`, taking the union side by side.
        val disjunction = or(a)(b)
        val la = distributeClauses(a, steps)
        val lb = distributeClauses(b, steps)
        for ((negA, posA, rA) <- la; (negB, posB, rB) <- lb) yield
          val negative = negA ++ negB
          val positive = posA ++ posB
          (negative, positive, emit(LeftOr(Sequent(negative + disjunction, positive), Seq(rA, rB), Seq(a, b))))
      case lit =>
        require(isLeaf(lit), s"distributeClauses: non-literal leaf in the NNF matrix (expected atom/¬atom/⊤/⊥). " +
          s"An η-reduced `∀(p)`/`∃(p)` reaching here means prenexing did not strip it: β-normalisation " +
          s"η-reduced the body and `Clausification.etaExpandQuantifiers` was not applied. Got: $lit")
        lit match
          // A negative literal is placed on the left as its atom: `Hypothesis(a ⊢ a)` then one `LeftNot`,
          // which turns `a ⊢ a` into `¬a, a ⊢`. The subformula `¬a` stays on the left, where the `LeftAnd`
          // and `LeftOr` above expect it, and the clause's own literal is the `a` beside it.
          case Neg(atom) =>
            val hyp = emit(Hypothesis(atom |- atom, atom))
            Seq((Set(atom), Set.empty[Expression], emit(LeftNot(Sequent(Set(lit, atom), Set.empty), hyp, atom))))
          case _ =>
            Seq((Set.empty[Expression], Set(lit), emit(Hypothesis(lit |- lit, lit))))
  }

  /** A literal leaf of an NNF matrix: an atom, a negated atom, or `⊤`/`⊥`, never a connective or quantifier.
    *
    * '''The η-reduced quantifier is matched head-on, not left to the sort test.''' [[Forall]]/[[Exists]] destructure
    * only an explicit `Lambda` argument, so `∀(p)` / `∃(p)`, the very shape
    * [[Clausification.etaExpandQuantifiers]] exists to repair, and the one form of quantifier that survives
    * [[PrenexPhase]] (whose `hasForall` misses it for the same reason), does not match them. It is `Prop`-sorted,
    * so it would reach the catch-all and be accepted as an *atom*: the clause would carry an opaque quantified
    * literal, whose head [[lisa.automation.superposition.Bridge]] then interns as an ordinary unary predicate
    * `forall/1` over a clause variable. Nothing detects that; the problem merely looks unprovable. Rejecting it
    * here turns a silently mis-clausified problem into the `require` failure in [[distributeClauses]].
    *
    * Partial applications of the *connectives* need no such case: `∧(a)` is `Prop → Prop`, not `Prop`, so the
    * sort test already excludes it. Only the quantifiers take a single argument and land back at `Prop`. */
  private def isLeaf(f: Expression): Boolean = f match
    case `top` | `bot`                                                                  => true
    case Neg(g)                                                                         => isLeaf(g)
    case And(_, _) | Or(_, _) | Implies(_, _) | Iff(_, _) | Forall(_, _) | Exists(_, _) => false
    case Application(`forall`, _) | Application(`exists`, _)                            => false // η-reduced `∀(p)`
    case _                                                                              => f.sort == Prop
