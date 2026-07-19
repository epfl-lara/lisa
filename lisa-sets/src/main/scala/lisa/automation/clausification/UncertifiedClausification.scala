package lisa.automation.clausification

import lisa.utils.K.{_, given}
import Clausification.*

/**
 * Uncertified clausification: an equisatisfiable clause set with **no proof reconstruction**, for when the
 * kernel-checkable certificate isn't needed (e.g. measuring how much of the certified pipeline's cost is
 * proof-building). A thin wrapper over the single-pass [[FastClausify]] (Vampire/E-style: selective definitional
 * naming → NNF → one Skolemization pass with fresh Skolem functions → distribution). The certified
 * [[Clausification.certifyClausal]] need only agree with it up to equisatisfiability, not clause-for-clause.
 */
object UncertifiedClausification:

  /** The conjecture-free clause set for `problem` (literal-set sequents), computed by [[FastClausify]] alone. */
  def clausalForm(problem: Problem): Problem =
    FastClausify.clausalForm(problem)

  /** Like [[clausalForm]] but pairs each clause with the index of the source formula it was clausified from —
   *  an index into `hypotheses ++ [¬conjecture]` (so `hypotheses.size` is the negated conjecture). For proof
   *  printers that attribute each clause to its single origin formula. */
  def clausalFormWithOrigins(problem: Problem): IndexedSeq[(Sequent, Int)] =
    FastClausify.clausalFormWithOrigins(problem)

  /**
   * Compute the clausal form (uncertified) and hand it to `prover`, returning the prover's proof verbatim
   * (imports = the clauses, conclusion `∅ ⊢`). Same signature as [[Clausification.certifyClausal]], but the
   * clausification is **not** certified — there is no proof linking the clauses back to the original conjecture.
   */
  def uncertifyClausal(problem: Problem, prover: Problem => SCProof): SCProof =
    prover(clausalForm(problem))
