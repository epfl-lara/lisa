package lisa.maths.SetTheory.Types.ADTv2.support.proofs

/**
 * Backwards-compatibility facade. The strengthened transfinite-recursion DEF
 * (the ε-selector additionally requires `functionOn`) and its spec theorem now
 * live in the library at [[lisa.maths.SetTheory.Ordinals.TransfiniteRecursion]]
 * and are re-exported here so existing imports keep resolving.
 */
object TransfiniteRecursionExt {
  export lisa.maths.SetTheory.Ordinals.TransfiniteRecursion.*
}
