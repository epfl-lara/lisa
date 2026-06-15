package lisa.maths.SetTheory.Types.ADTv2.support.proofs

/**
 * Backwards-compatibility facade. The integer / ω theory now lives in the
 * library at [[lisa.maths.SetTheory.Ordinals.Integer]]. Members are re-exported
 * here, with the former ADT-era "Nat" names kept as aliases so existing imports
 * keep resolving.
 */
object ExtendedInteger {
  export lisa.maths.SetTheory.Ordinals.Integer.{
    selfInSuccessor as nInSuccN,
    emptyInOmega as zeroIsNat,
    omegaNotEmpty as natNotEmpty,
    successorInOmega as successorIsNat,
    omegaSuccessorInduction as natInduction,
    omegaDownwardClosed as subsetIsNat,
    unionInOmega as unionOfTwoNats,
    existsInOmega as existsNat,
    *
  }
}
