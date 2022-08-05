package lisa.proven.mathematics

import lisa.utils.Helpers.{given, *}
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.*
import lisa.proven.tactics.ProofTactics.*
import lisa.proven.PeanoArithmeticsLibrary
import lisa.utils.Helpers.{_, given}
import lisa.utils.Library

object Peano {
  export lisa.proven.PeanoArithmeticsLibrary.{*, given}
  given output: (String => Unit) = println
}
