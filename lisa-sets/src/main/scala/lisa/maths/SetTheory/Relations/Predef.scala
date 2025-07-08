package lisa.maths.SetTheory.Relations

/**
 * Base exports for the `Relations` package.
 */
object Predef {
  export lisa.maths.SetTheory.Relations.Definitions.{
    relationBetween,
    relationOn,
    relation,
    dom,
    range,
    field,
    reflexive,
    irreflexive,
    antiReflexive,
    symmetric,
    asymmetric,
    antisymmetric,
    transitive,
    connected,
    total,
    stronglyConnected,
    equivalence
  }
  export lisa.maths.SetTheory.Relations.Properties
  export lisa.maths.SetTheory.Relations.Operations.Closure
  export lisa.maths.SetTheory.Relations.Operations.Restriction as RelationRestriction
  export lisa.maths.SetTheory.Relations.Operations.Restriction.{↾}
}
