package lisa.utilcfs.prooflib

import lisa.kernelcf.proof.{Sequent, Theory}

abstract class Library:
  val theory: Theory = Theory.empty
  given Theory = theory
