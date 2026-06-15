package lisa.maths.SetTheory.Functions

/**
 * Base exports for the `Functions` package.
 *
 * The `Functions` package re-exports all of the `Relations` package, hence there is
 * no need to import them both.
 */
object Predef {
  export lisa.maths.SetTheory.Relations.Predef.*
  export lisa.maths.SetTheory.Functions.Function.{functionBetween, function, functionOn, app, injective, surjective, bijective, abs, Sabs, given}
  export lisa.maths.SetTheory.Functions.Pi.{Pi, SPi, SArrow, ->:}
  export lisa.maths.SetTheory.Functions.Operations.Restriction
  export lisa.maths.SetTheory.Functions.Operations.Restriction.{↾}
}
