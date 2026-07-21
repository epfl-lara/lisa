package lisa.utils.prooflib

import lisa.utils.fol.FOL.Sequent

import ProofHelpers.*

/**
  * Some variations of ProofHelpers for use in tactics.
  */
object TacticHelpers:

  private inline def target(using proof: Proof)(statement: Sequent): Sequent =
    proof.withAssumptions(statement)

  class MaybeSequent(conclusion: Sequent):
    infix def by[T](using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line)(tactic: SequentTacticM[T]): ProofCarrier[T] =
      by(using lib, proof, file, line)(tactic(using file, line)(using lib))

    infix def by[T](using lib: Library, proof: Proof, file: sourcecode.File, line: sourcecode.Line)(tactic: Sequent => ProofCarrier[T]): ProofCarrier[T] =
      val carrier = tactic(target(conclusion))
      if carrier.isValid then
        // valid proof step, absorb and continue
        proof.absorb(carrier)
      else
        // failed, pass on the error
        carrier

  /**
    * Like [[have]], but a `maybe(...) by Tactic` generates a [[ProofJudgment]],
    * absorbing it into the proof if it succeeds, and a no-op if it fails.
    *
    * Use [[or]] or [[orFailWith]] to chain maybes or fail the current subproof.
    *
    */
  def maybe(conclusion: Sequent): MaybeSequent =
    new MaybeSequent(conclusion)

  extension [T] (carrier: ProofCarrier[T])
    def or(other: => ProofCarrier[T]): ProofCarrier[T] =
      if carrier.isValid then carrier else other

    def orFailWith(using bdr: SubproofLabel[T])(err: ProofCarrier[T] => ProofCarrier[T]): ProofCarrier[T] =
      if carrier.isValid then carrier
      else
        val error = err(carrier)
        // ideally: error.isValid == false, but we don't enforce that
        // just use `or` in that case
        bdr.breakWith(error)

  /** Stops the nearest subproof with a fatal error at the call site. */
  def failWith[T](using bdr: SubproofLabel[T], file: sourcecode.File, line: sourcecode.Line)(msg: String): Nothing =
    val error = FatalError(msg, file, line)
    bdr.breakWith(FatalCarrier(error, Set.empty))

  /** Stops the nearest subproof with an existing carrier. */
  def failWith[T](using bdr: SubproofLabel[T])(err: => ProofCarrier[T]): Nothing =
    bdr.breakWith(err)
