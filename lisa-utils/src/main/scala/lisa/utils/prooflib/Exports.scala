package lisa.utils.prooflib

object Exports:
  import lisa.utils.prooflib as P

  export P.ProofHelpers.*
  export P.BasicStep.*
  export P.ProofJudgement
  export P.{Corollary, Lemma, Theorem}
  export lisa.utils.automation.{Congruence, Discharge, Generalize, Horn, HornSolver, InstantiateForall, Substitute, Tableau, Tautology}
