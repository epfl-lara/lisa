package lisa.maths.settheory

/**
 * Set-theoretic functions library
 *
 * Develops the set-theoretic functions, their properties, and common theorems.
 */
package object functions {
  export lisa.maths.settheory.functions.Functionals.{
    functional,
    functionalOver,
    functionalMembership,
    violatingPairInFunction,
    pairSingletonIsFunctional,
    setOfFunctionsUniqueness,
    setOfFunctions,
    functionFrom,
    functionFromImpliesFunctional,
    functionApplicationUniqueness,
    app,
    pairInFunctionIsApp,
    functionalOverApplication,
    elemOfFunctional,
    elemOfFunctionalOver,
    elemOfFunctionFrom,
    functionsEqualIfEqualOnDomain,
    functionsSubsetIfEqualOnSubsetDomain,
    restrictedFunctionUniqueness,
    restrictedFunction,
    restrictedFunctionPairMembership,
    restrictedFunctionDomain,
    restrictedFunctionIsFunctionalOver,
    restrictedFunctionApplication,
    restrictedFunctionCancellation,
    restrictedFunctionAbsorption,
    functionalOverImpliesDomain,
    functionFromImpliesDomainEq,
    functionImpliesRangeSubsetOfCodomain,
    inRangeImpliesPullbackExists,
    unionOfFunctionsIsAFunction,
    unionOfFunctionsWithDisjointDomains,
    unionOfFunctionSet,
    domainOfFunctionalUnion,
    |=>,
    functionRange,
    functionDomain
  }
  export lisa.maths.settheory.functions.FunctionProperties.{surjective, onto, injective, oneone, bijective, invertibleFunction, inverseFunctionOf, surjectiveImpliesRangeIsCodomain, cantorTheorem}
}
