package lisa.utilcfs.prooflib

object Exports:
  import lisa.utilcfs.prooflib as P

  export P.ProofHelpers.*
  export P.BasicStep.*
  export P.{Lemma, Theorem}
  export P.{Congruence, Generalize, InstantiateForall, Substitute, Tableau, Tautology}
