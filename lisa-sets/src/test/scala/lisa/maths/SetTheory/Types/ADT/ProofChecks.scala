package lisa.maths.SetTheory.Types.ADT

import lisa.utils.prooflib.Theorem
import lisa.utils.prooflib.Thm

/**
 * Checks both front errors and kernel admission dependencies in generated proofs.
 */
object ProofChecks:
  extension (theorem: Theorem) def hasErrorsOrSorry: Boolean = theorem.errors.nonEmpty || theorem.kernel.usesSorry

  extension (theorem: Thm) def hasErrorsOrSorry: Boolean = theorem.kernel.usesSorry
