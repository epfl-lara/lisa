package lisa.maths.SetTheory.Types.ADTv2.support.proofs

import lisa.maths.SetTheory.Ordinals.Integer
import lisa.maths.SetTheory.Ordinals.Ordinal.S

/**
 * Backwards-compatibility facade. The integer / ω theory now lives in the
 * library at [[lisa.maths.SetTheory.Ordinals.Integer]], stated in terms of the
 * ordinal successor `S`.
 *
 * TEMPORARY: the ADT layer is phrased with the set-theoretic `successor`
 * (`x ∪ {x}`), so the lemmas whose statements mention the successor are
 * re-derived here in `successor`-form (bridged through `successor === S`), and
 * the remaining members are re-exported, with the former "Nat" names kept as
 * aliases.
 */
object ExtendedInteger extends lisa.Main {

  export lisa.maths.SetTheory.Ordinals.Integer.{
    emptyInOmega as zeroIsNat,
    omegaNotEmpty as natNotEmpty,
    omegaDownwardClosed as subsetIsNat,
    unionInOmega as unionOfTwoNats,
    existsInOmega as existsNat,

    successorInjectivity as successorInjectivity,
    zeroIsNotSucc as zeroIsNotSucc,
    subsetSuccessor as subsetSuccessor,
    subsetBelowSucc as subsetBelowSucc,
    succMembership as succMembership,

    omegaSuccessorInduction as natInduction,
    successorInOmega as successorIsNat,
    selfInSuccessor as nInSuccN,
    *
  }
}
