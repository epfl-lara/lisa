package lisa.maths.SetTheory.Types.ADTv2.support.proofs

/**
 * Backwards-compatibility facade. The ω-ordinal facts now live in the library
 * at [[lisa.maths.SetTheory.Ordinals.OmegaFacts]] and are re-exported here so
 * existing imports keep resolving.
 */
object OmegaFacts {
  export lisa.maths.SetTheory.Ordinals.OmegaFacts.*
}
