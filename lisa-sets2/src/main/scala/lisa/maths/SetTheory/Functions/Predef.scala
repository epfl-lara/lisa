package lisa.maths.SetTheory.Functions

/** Base exports for the `Functions` package. */
object Predef {
  export lisa.maths.SetTheory.Relations.Predef.{dom as _, range as _, ↾ as _, *}
  export lisa.maths.SetTheory.Functions.Definitions.{
    functionBetween,
    ::,
    function,
    functionOn,
    dom,
    range,
    app,
    apply,
    injective,
    surjective,
    bijective
  }
  export lisa.maths.SetTheory.Relations.Operations.Restriction as FunctionRestriction
  export lisa.maths.SetTheory.Functions.Operations.Restriction.{↾}
}

