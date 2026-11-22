package lisa.utils.prooflib

import lisa.utils.fol.FOL.Sequent

import ProofHelpers._

/**
 * Some variations of ProofHelpers for use in tactics.
 */
object TacticHelpers:

  class MaybeSequent(conclusion: Sequent):
    infix def by[T](using lib: Library, proof: ProofBuilder, file: sourcecode.File, line: sourcecode.Line)(tactic: SequentTacticM[T]): ProofCarrier[T] =
      by(using lib, proof, file, line)(tactic(using file, line)(using lib))

    infix def by[T](using lib: Library, proof: ProofBuilder, file: sourcecode.File, line: sourcecode.Line)(tactic: Sequent => ProofCarrier[T]): ProofCarrier[T] =
      proof.absorb(tactic(proof.withAssumptions(conclusion)))

  /**
   * Runs a tactic and records its result only on success. Expected failures are
   * returned unchanged without logging; thrown exceptions propagate.
   *
   * Use [[or]] or [[orFailWith]] to chain maybes or fail the current subproof.
   */
  def maybe(conclusion: Sequent): MaybeSequent =
    new MaybeSequent(conclusion)

  extension [T](carrier: ProofCarrier[T])
    def or(other: => ProofCarrier[T]): ProofCarrier[T] =
      if carrier.isValid then carrier else other

    def orFailWith(using bdr: SubproofLabel[T])(err: ProofCarrier[T] => ProofCarrier[T]): ProofCarrier[T] =
      if carrier.isValid then carrier
      else
        val error = err(carrier)
        // ideally: error.isValid == false, but we don't enforce that
        // just use `or` in that case
        bdr.breakWith(error)

  /**
   * Stops the nearest independent subproof with an expected failure.
   */
  def failWith[T](using bdr: SubproofLabel[T])(msg: String): Nothing =
    bdr.breakWith(ProofCarrier.Failure(msg))

  /**
   * Stops the nearest subproof with an existing carrier.
   */
  def failWith[T](using bdr: SubproofLabel[T])(err: => ProofCarrier[T]): Nothing =
    bdr.breakWith(err)
