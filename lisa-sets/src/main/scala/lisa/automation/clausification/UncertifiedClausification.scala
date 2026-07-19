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
    // Single-pass, non-proof-producing pipeline (Vampire/E-style): selective definitional naming → NNF →
    // one Skolemization pass (fresh Skolem functions) → distribution. See [[FastClausify]]. This supersedes the
    // former quadratic NNF→Skolem→Prenex→Tseitin certification-mirroring pipeline (which is still what the
    // *certified* [[Clausification]] path uses, phase by phase); the two need only agree up to equisatisfiability.
    FastClausify.clausalForm(problem)

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
