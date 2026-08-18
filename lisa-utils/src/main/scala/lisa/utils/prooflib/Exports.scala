package lisa.utils.prooflib

object Exports:
  import lisa.utils.prooflib as P

  export P.ProofHelpers.*
  export P.BasicStep.*
  export P.ProofJudgement
  export P.{Lemma, Theorem}
  export P.{Congruence, Discharge, Generalize, InstantiateForall, Substitute, Tableau, Tautology}
