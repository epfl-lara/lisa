package lisa.maths.SetTheory.Relations

/**
 * Base exports for the `Relations` package.
 */
object Predef {
  export lisa.maths.SetTheory.Relations.Relation
  export lisa.maths.SetTheory.Relations.Relation.{R, relationBetween, relationOn, relation, dom, range, field}
  export lisa.maths.SetTheory.Relations.Properties.{reflexive, irreflexive, symmetric, asymmetric, antisymmetric, transitive, connected, total, stronglyConnected}
  export lisa.maths.SetTheory.Relations.Equivalence.{equivalence, equivalenceClass, /}
  export lisa.maths.SetTheory.Relations.WellFoundedRelation
  export lisa.maths.SetTheory.Relations.WellFoundedRelation.wellFounded
  export lisa.maths.SetTheory.Relations.Operations.Closure
}
