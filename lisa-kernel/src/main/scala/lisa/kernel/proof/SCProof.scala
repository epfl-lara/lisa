package lisa.kernel.proof

import lisa.kernel.proof.SequentCalculus._

/**
 * A SCPRoof (for Sequent Calculus Proof) is a (dependant) proof. While technically a proof is an Directed Acyclic Graph,
 * here proofs are linearized and represented as a list of proof steps.
 * Moreover, a proof can depend on some assumed, unproved, sequents specified in the second argument
 * @param steps A list of Proof Steps that should form a valid proof. Each individual step should only refer to earlier
 *              proof steps as premisces.
 * @param imports A list of assumed sequents that further steps may refer to. Imports are refered to using negative integers
 *                To refer to the first sequent of imports, use integer -1.
 */
case class SCProof(steps: IndexedSeq[SCProofStep], imports: IndexedSeq[Sequent] = IndexedSeq.empty) {
  def numberedSteps: Seq[(SCProofStep, Int)] = steps.zipWithIndex

  /**
   * Fetches the <code>i</code>th step of the proof.
   * @param i the index
   * @return a step
   */
  def apply(i: Int): SCProofStep = {
    if (i >= 0)
      if (i >= steps.length) throw new IndexOutOfBoundsException(s"index $i is out of bounds of the steps Seq")
      else steps(i)
    else throw new IndexOutOfBoundsException(s"index $i is out of bounds of the steps Seq")
  }

  /**
   * Get the ith sequent of the proof. If the index is positive, give the bottom sequent of proof step number i.
   * If the index is negative, return the <code>(-i-1)</code>th imported sequent.
   *
   * @param i The reference number of a sequent in the proof
   * @return A sequent, either imported or reached during the proof.
   */
  def getSequent(i: Int): Sequent = {
    if (i >= 0)
      if (i >= steps.length) throw new IndexOutOfBoundsException(s"index $i is out of bounds of the steps Seq")
      else steps(i).bot
    else {
      val i2 = -(i + 1)
      if (i2 >= imports.length) throw new IndexOutOfBoundsException(s"index $i is out of bounds of the imports Seq")
      else imports(i2)
    }
  }

  /**
   * The length of the proof in terms of top-level steps, without including the imports.
   */
  def length: Int = steps.length

  /**
   * The total length of the proof in terms of proof-step, including steps in subproof, but excluding the imports.
   */
  def totalLength: Int = steps.foldLeft(0)((i, s) =>
    i + (s match {
      case s: SCSubproof => s.sp.totalLength + 1
      case _ => 1
    })
  )

  /**
   * The conclusion of the proof, namely the bottom sequent of the last proof step.
   * Can be undefined if the proof is empty.
   */
  def conclusion: Sequent = {
    if (steps.isEmpty && imports.isEmpty) throw new NoSuchElementException("conclusion of an empty proof")
    this.getSequent(length - 1)
  }

  /**
   * A helper method that creates a new proof with a new step appended at the end.
   * @param newStep the new step to be added
   * @return a new proof
   */
  def appended(newStep: SCProofStep): SCProof = copy(steps = steps appended newStep)

  /**
   * A helper method that creates a new proof with a sequence of new steps appended at the end.
   * @param newSteps the sequence of steps to be added
   * @return a new proof
   */
  def withNewSteps(newSteps: IndexedSeq[SCProofStep]): SCProof = copy(steps = steps ++ newSteps)
}

object SCProof {

  /**
   * Instantiates a proof from an indexed list of proof steps.
   * @param steps the steps of the proof
   * @return the corresponding proof
   */
  def apply(steps: SCProofStep*): SCProof = {
    SCProof(steps.toIndexedSeq)
  }

}
