package lisa.automation.clausification

import lisa.utils.K.{_, given}
import Clausification.*

/**
 * Uncertified clausification: computes the **same clausal form** as [[Clausification.certifyClausal]] but with
 * **no proof reconstruction** — it runs only the pure formula transforms (NNF → Skolem → Prenex → Tseitin) to
 * produce the clause set, hands it to the prover, and returns the prover's proof verbatim. It trades the
 * kernel-checkable clausification certificate for speed; use it to measure how much of the certified
 * pipeline's cost is proof-building.
 *
 * The fresh-symbol naming (prenex witnesses `Vᵢ`, Tseitin atoms `tsᵢ`) matches the certified pipeline exactly:
 * one shared [[Clausification.Counter]] per phase, hypotheses processed in order with the negated conjecture
 * appended last — mirroring the separate `certifyAxiomwise`/`certifyTseitinFlat` calls. Only the pure cores of
 * each phase are reused ([[NnfPhase.toNNF]], [[SkolemPhase.skolemizeOne]], [[PrenexPhase.extractUniversalMatrix]],
 * [[TseitinPhase.tseitinStep]]); no proof is built.
 */
object UncertifiedClausification:

  /**
   * The clausal form of `problem`: exactly the conjecture-free `Problem` of literal-set clauses that
   * [[Clausification.certifyClausal]] feeds its prover, computed by the pure transforms alone.
   */
  def clausalForm(problem: Problem): Problem =
    // Negated (certifyNegated): consume the conjecture by appending `¬conjecture` as the last hypothesis.
    val hyps0: IndexedSeq[Sequent] = problem.conjecture match
      case Some(c) => problem.hypotheses.toIndexedSeq :+ (() |- neg(singleRightFormula(c, "conjecture")))
      case None    => problem.hypotheses.toIndexedSeq

    // NNF → Skolem → Prenex, each phase with its own counter (matching the separate certifyAxiomwise calls).
    val skolemCounter = Counter()
    val prenexCounter = Counter()
    val transformed: IndexedSeq[Expression] = hyps0.map { h =>
      val phiNnf    = NnfPhase.toNNF(singleRightFormula(h, "hypothesis"), negated = false) // certifyNnf
      val phiSkolem = skolemizeAll(phiNnf, skolemCounter)                                  // certifySkolem
      if PrenexPhase.hasForall(phiSkolem) then                                             // certifyPrenex
        PrenexPhase.extractUniversalMatrix(phiSkolem, prenexCounter)._1
      else phiSkolem
    }

    // Tseitin (certifyTseitinFlat): iterate tseitinStep per axiom, emit new-clauses + the residual clause,
    // every clause in the same literal-set form `Sequent(∅, {literals})`.
    val tseitinCounter = Counter()
    val finalAxioms: IndexedSeq[Sequent] = transformed.flatMap { phi =>
      val ts            = tseitinAll(phi, tseitinCounter)
      val newClauseSeqs = ts.flatMap(_.newClauses).map(lits => Sequent(Set.empty, lits.toSet))
      val finalFormula  = if ts.isEmpty then phi else ts.last.tsRewrite
      val finalSeq      = Sequent(Set.empty, TseitinPhase.clauseLiterals(finalFormula).toSet)
      if ts.isEmpty then IndexedSeq(finalSeq) else newClauseSeqs :+ finalSeq
    }
    Problem(finalAxioms.toList, None)

  /**
   * Compute the clausal form (uncertified) and hand it to `prover`, returning the prover's proof verbatim
   * (imports = the clauses, conclusion `∅ ⊢`). Same signature as [[Clausification.certifyClausal]], but the
   * clausification is **not** certified — there is no proof linking the clauses back to the original conjecture.
   */
  def uncertifyClausal(problem: Problem, prover: Problem => SCProof): SCProof =
    prover(clausalForm(problem))

  /** Fully Skolemize by iterating [[SkolemPhase.skolemizeOne]] (leftmost-outermost `∃` per step) to a fixpoint. */
  private def skolemizeAll(f: Expression, counter: Counter): Expression =
    var current = f
    var continue = true
    while continue do
      SkolemPhase.skolemizeOne(current, counter) match
        case None                                 => continue = false
        case Some(SkolemPhase.SkolemStep(sko, _)) => current = sko
    current

  /** Run [[TseitinPhase.tseitinStep]] to a fixpoint, chaining each step on the previous rewrite. */
  private def tseitinAll(f: Expression, counter: Counter): IndexedSeq[TseitinPhase.TseitinStep] =
    val buf = scala.collection.mutable.ArrayBuffer.empty[TseitinPhase.TseitinStep]
    var current = f
    var continue = true
    while continue do
      TseitinPhase.tseitinStep(current, counter) match
        case None    => continue = false
        case Some(t) => buf += t; current = t.tsRewrite
    buf.toIndexedSeq
