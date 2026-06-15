package lisa.maths.SetTheory.Types.ADTv2.support.proofs

/**
 * Backwards-compatibility facade. The generic subset / union / range /
 * (restricted) function lemmas now live in the library and are re-exported here
 * so existing imports keep resolving:
 *   - [[lisa.maths.SetTheory.Base.Union]] — `unionMonotonic`, `unionNull`
 *   - [[lisa.maths.SetTheory.Base.Subset]] — `subsetNotEmpty`
 *   - [[lisa.maths.SetTheory.Functions.BasicTheorems]] — `nonEmptyDomain`
 *   - [[lisa.maths.SetTheory.Functions.Operations.Restriction]] — `restrictedFunctionNotEmpty`, `restrictedFunctionDomainMonotonic`
 *   - [[lisa.maths.SetTheory.Functions.UnionRange]] — `unionRangeMonotonic`
 *   - [[lisa.maths.SetTheory.Types.TypingTheorems]] — `funEqDef`
 */
object FunctionFacts {
  export lisa.maths.SetTheory.Base.Union.{unionMonotonic, unionNull}
  export lisa.maths.SetTheory.Base.Subset.subsetNotEmpty
  export lisa.maths.SetTheory.Functions.BasicTheorems.nonEmptyDomain
  export lisa.maths.SetTheory.Functions.Operations.Restriction.{restrictedFunctionNotEmpty, restrictedFunctionDomainMonotonic}
  export lisa.maths.SetTheory.Functions.UnionRange.unionRangeMonotonic
  export lisa.maths.SetTheory.Types.TypingTheorems.funEqDef
}
