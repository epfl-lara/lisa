package lisa

import lisa.SetTheoryLibrary
import lisa.prooflib.BasicMain

/**
 * The parent trait of all theory files containing mathematical development
 */
trait HOL extends BasicMain {
  export lisa.maths.settheory.types.TypeSystem.*
  export lisa.maths.settheory.types.TypeLib.{Zero, One, 𝔹, |=>}
  export lisa.hol.VarsAndFunctions.*
  export SetTheoryLibrary.{given, _}

  export lisa.fol.FOL as F

}