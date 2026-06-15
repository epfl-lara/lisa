package lisa.maths.SetTheory.Types.ADTv2.support.proofs

/**
 * Backwards-compatibility facade. The ω / S facts now live in the
 * library at [[lisa.maths.SetTheory.Ordinals.Integer]] and are re-exported here
 * so existing imports keep resolving.
 */
object NatFacts {
  export lisa.maths.SetTheory.Ordinals.Integer.elementsTransitive
  // S-form bridge (the library version is stated with `S`)
  export ExtendedInteger.subsetBelowSucc
}
