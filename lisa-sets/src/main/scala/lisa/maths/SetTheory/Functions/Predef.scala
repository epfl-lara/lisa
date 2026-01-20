package lisa.maths.SetTheory.Functions

/**
 * Base exports for the `Functions` package.
 *
 * The `Functions` package re-exports all of the `Relations` package, hence there is
 * no need to import them both.
 */
object Predef {
  export lisa.maths.SetTheory.Relations.Predef.*
  export lisa.maths.SetTheory.Functions.Function.{functionBetween, ::, function, functionOn, app, apply, injective, surjective, bijective}
  export lisa.maths.SetTheory.Functions.Operations.Restriction
  export lisa.maths.SetTheory.Functions.Operations.Restriction.{↾}
  export lisa.maths.SetTheory.Functions.Operations.Composition
  export lisa.maths.SetTheory.Functions.Operations.Composition.{∘}
  export lisa.maths.SetTheory.Functions.Operations.Identity
}
