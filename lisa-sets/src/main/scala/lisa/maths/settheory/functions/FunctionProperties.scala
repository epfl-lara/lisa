package lisa.maths.settheory.functions

import lisa.automation.kernel.CommonTactics.ExistenceAndUniqueness

/**
 * Classes/properties of functions.
 *
 * Describes properties of functions such as being injective ([[FunctionPoperties.injective]]), being invertible
 * ([[FunctionPoperties.invertibleFunction]]), or being constant ([[FunctionProperties.constantFunction]]).
 */
object FunctionProperties extends lisa.Main {
  import lisa.maths.settheory.SetTheory.{
    relation,
    pair,
    relationBetween,
    emptySetIsASubset,
    cartesianProduct,
    subsetEqualitySymmetry,
    singleton,
    pairInCartesianProduct,
    singletonHasNoExtraElements,
    cartesianProductIsRelation,
    elemInItsPowerSet
  }
  import lisa.maths.Quantifiers.{equalityTransitivity}
  import lisa.maths.settheory.functions.Functionals.{
    functionFromImpliesFunctional,
    functionFrom,
    app,
    functionRange,
    functionDomain,
    functionImpliesRangeSubsetOfCodomain,
    inRangeImpliesPullbackExists,
    functionFromImpliesDomainEq
  }

  // var defs
  private val x = variable
  private val y = variable
  private val z = variable
  private val t = variable
  private val a = variable
  private val b = variable
  private val p = variable

  // relation and function symbols
  private val r = variable
  private val f = variable
  private val g = variable

  /**
   * Surjective (function) --- a function `f: x → y` is surjective iff it
   * maps to every `b ∈ y` from atleast one `a ∈ x`.
   *
   * `surjective(f, x, y) = f ∈ x → y ∧ ∀ b ∈ y. (∃ a ∈ x. f(a) = b)`
   */
  val surjective = DEF(f, x, y) --> functionFrom(f, x, y) /\ ∀(b, in(b, y) ==> ∃(a, in(pair(a, b), f)))

  /**
   * Alias for [[surjective]]
   */
  val onto = surjective

  /**
   * Injective (function) --- a function `f: x → y` is injective iff it maps
   * to every `b ∈ y` from atmost one `a ∈ x`.
   *
   * `injective(f, x, y) = f ∈ x → y ∧ ∀ b ∈ y. (∃ a ∈ x. f(a) = b) ⟹ (∃! a ∈ x. f(a) = b)`
   */
  val injective = DEF(f, x, y) --> functionFrom(f, x, y) /\ ∀(b, in(b, y) ==> (∃(a, in(a, x) /\ in(pair(a, b), f)) ==> ∃!(a, in(a, x) /\ in(pair(a, b), f))))

  /**
   * Alias for [[injective]]
   */
  val oneone = injective

  /**
   * Bijective function --- a function `f: x → y` is bijective iff it is
   * [[injective]] and [[surjective]].
   */
  val bijective = DEF(f, x, y) --> injective(f, x, y) /\ surjective(f, x, y)

  /**
   * Invertible Function --- a function from `x` to `y` is invertible iff it is
   * [[bijective]]. See also, [[inverseFunction]]
   */
  val invertibleFunction = DEF(f, x, y) --> bijective(f, x, y)

  /**
   * Inverse Function --- the inverse of a function `f: x → y`, denoted
   * `f^-1`, is a function from `y` to `x` such that `∀ a ∈ x, b ∈ y.
   * f(f^-1(b)) = b ∧ f^-1(f(b)) = b`.
   */
  val inverseFunctionOf = DEF(g, f, x, y) --> functionFrom(g, y, x) /\ functionFrom(f, x, y) /\ ∀(a, (in(a, y) ==> (a === app(f, app(g, a)))) /\ (in(a, x) ==> (a === app(g, app(f, a)))))

  // val inverseFunctionExistsIfInvertible = Theorem(
  //    invertibleFunction(f, x, y) <=> ∃(g, inverseFunctionOf(g, f, x, y))
  // ) {
  //   ???
  // }

  // val inverseFunctionIsUniqueIfItExists = Theorem(
  //   ∃(g, inverseFunctionOf(g, f, x, y)) |- ∃!(g, inverseFunctionOf(g, f, x, y))
  // ) {
  //   ???
  // }

  // val inverseFunctionUniqueness = Theorem(
  //    ∃!(g, invertibleFunction(f) ==> inverseFunctionOf(g, f, x, y))
  // ) {
  //   ???
  // }

  // val inverseFunction = DEF (f, x, y) --> The(g, invertibleFunction(f) ==> inverseFunctionOf(g, f, x, y))(inverseFunctionUniqueness)

  /**
   * Theorem --- if a function is [[surjective]], its range is equal to its codomain.
   */
  val surjectiveImpliesRangeIsCodomain = Theorem(
    surjective(f, x, y) |- (y === functionRange(f))
  ) {
    have(surjective(f, x, y) |- ∀(b, in(b, y) ==> ∃(a, in(pair(a, b), f)))) by Tautology.from(surjective.definition)
    val surjDef = thenHave(surjective(f, x, y) |- in(b, y) ==> ∃(a, in(pair(a, b), f))) by InstantiateForall(b)
    have(∀(t, in(t, functionRange(f)) <=> (∃(a, in(pair(a, t), f))))) by InstantiateForall(functionRange(f))(functionRange.definition of (r -> f))
    val rangeDef = thenHave(in(b, functionRange(f)) <=> (∃(a, in(pair(a, b), f)))) by InstantiateForall(b)

    have(surjective(f, x, y) |- in(b, y) ==> in(b, functionRange(f))) by Tautology.from(surjDef, rangeDef)
    thenHave(surjective(f, x, y) |- ∀(b, in(b, y) ==> in(b, functionRange(f)))) by RightForall
    val surjsub = andThen(Substitution.applySubst(subsetAxiom of (x -> y, y -> functionRange(f))))

    have((surjective(f, x, y), functionFrom(f, x, y)) |- subset(y, functionRange(f)) /\ subset(functionRange(f), y)) by RightAnd(surjsub, functionImpliesRangeSubsetOfCodomain)
    val funceq = andThen(Substitution.applySubst(subsetEqualitySymmetry of (x -> y, y -> functionRange(f))))

    val surjfunc = have(surjective(f, x, y) |- functionFrom(f, x, y)) by Tautology.from(surjective.definition)

    have(thesis) by Cut(surjfunc, funceq)
  }

  /**
   * Theorem --- Cantor's Theorem
   *
   * There is no [[surjective]] mapping ([[functionFrom]]) a set to its [[powerSet]].
   *
   * In terms of cardinality, it asserts that a set is strictly smaller than
   * its power set.
   */
  val cantorTheorem = Theorem(
    surjective(f, x, powerSet(x)) |- ()
  ) {
    // define y = {z \in x | ! z \in f(z)}
    val ydef = ∀(t, in(t, y) <=> (in(t, x) /\ !in(t, app(f, t))))

    // y \subseteq x
    // y \in P(x)
    have(ydef |- ydef) by Hypothesis
    thenHave(ydef |- in(t, y) <=> (in(t, x) /\ !in(t, app(f, t)))) by InstantiateForall(t)
    thenHave(ydef |- in(t, y) ==> in(t, x)) by Weakening
    thenHave(ydef |- ∀(t, in(t, y) ==> in(t, x))) by RightForall
    andThen(Substitution.applySubst(subsetAxiom of (x -> y, y -> x)))
    andThen(Substitution.applySubst(powerAxiom of (x -> y, y -> x)))
    val yInPower = thenHave(ydef |- in(y, powerSet(x))) by Restate

    // y \in range(f)
    have(surjective(f, x, powerSet(x)) |- (powerSet(x) === functionRange(f))) by Restate.from(surjectiveImpliesRangeIsCodomain of (y -> powerSet(x)))
    andThen(Substitution.applySubst(extensionalityAxiom of (x -> powerSet(x), y -> functionRange(f))))
    val surjRange = thenHave(surjective(f, x, powerSet(x)) |- in(y, powerSet(x)) <=> in(y, functionRange(f))) by InstantiateForall(y)
    val yInRange = have((ydef, surjective(f, x, powerSet(x))) |- in(y, functionRange(f))) by Tautology.from(yInPower, surjRange)

    // \exists z. z \in x /\ f(z) = y
    val surjToFunFrom = have(surjective(f, x, powerSet(x)) |- functionFrom(f, x, powerSet(x))) by Tautology.from(surjective.definition of (y -> powerSet(x)))
    val existsZdom = have((ydef, surjective(f, x, powerSet(x))) |- ∃(z, in(z, functionDomain(f)) /\ (app(f, z) === y))) by Tautology.from(
      yInRange,
      surjective.definition of (y -> powerSet(x)),
      inRangeImpliesPullbackExists of (z -> y),
      functionFromImpliesFunctional of (y -> powerSet(x))
    )
    val xeqdom = thenHave((ydef, surjective(f, x, powerSet(x)), (functionDomain(f) === x)) |- ∃(z, in(z, x) /\ (app(f, z) === y))) by RightSubstEq.withParametersSimple(
      List((x, functionDomain(f))),
      lambda(x, ∃(z, in(z, x) /\ (app(f, z) === y)))
    )
    val existsZ = have((ydef, surjective(f, x, powerSet(x))) |- ∃(z, in(z, x) /\ (app(f, z) === y))) by Tautology.from(
      surjective.definition of (y -> powerSet(x)),
      functionFromImpliesDomainEq of (y -> powerSet(x)),
      xeqdom
    )

    // z \in Y <=> z \in x /\ ! z \in f(z)
    // y = f(z) so z \in f(z) <=> ! z \in f(z)
    have(ydef |- ydef) by Hypothesis
    thenHave(ydef |- in(z, y) <=> (in(z, x) /\ !in(z, app(f, z)))) by InstantiateForall(z)
    thenHave((ydef, in(z, x), (app(f, z) === y)) |- in(z, y) <=> (in(z, x) /\ !in(z, app(f, z)))) by Weakening
    thenHave((ydef, in(z, x), (app(f, z) === y)) |- in(z, app(f, z)) <=> (in(z, x) /\ !in(z, app(f, z)))) by RightSubstEq.withParametersSimple(
      List((y, app(f, z))),
      lambda(y, in(z, y) <=> (in(z, x) /\ !in(z, app(f, z))))
    )
    thenHave((ydef, in(z, x) /\ (app(f, z) === y)) |- ()) by Tautology
    val existsToContra = thenHave((ydef, ∃(z, in(z, x) /\ (app(f, z) === y))) |- ()) by LeftExists

    have((ydef, surjective(f, x, powerSet(x))) |- ()) by Cut(existsZ, existsToContra)
    val yToContra = thenHave((∃(y, ydef), surjective(f, x, powerSet(x))) |- ()) by LeftExists
    val yexists = have(∃(y, ydef)) by Restate.from(comprehensionSchema of (z -> x, φ -> lambda(t, !in(t, app(f, t)))))

    have(thesis) by Cut(yexists, yToContra)
  }

  /**
   * Constant function --- for every element in its domain, the value is the same.
   */
  val constantFunction = DEF(x, t) --> cartesianProduct(x, singleton(t))

  /**
   * Theorem --- the value of a constant function is the same for all elements in its domain.
   *
   *  `a ∈ x |- app(constantFunction(x, t), a) = t`
   */
  val constantFunctionApplication = Theorem(
    in(a, x) |- app(constantFunction(x, t), a) === t
  ) {
    assume(in(a, x))
    have(functionFrom(constantFunction(x, t), x, singleton(t))) by Weakening(constantFunctionFunctionFrom)

    have(in(app(constantFunction(x, t), a), singleton(t))) by Tautology.from(
      functionFromApplication of (f := constantFunction(x, t), y := singleton(t)),
      lastStep
    )

    have(thesis) by Tautology.from(
      singletonHasNoExtraElements of (y := app(constantFunction(x, t), a), x := t),
      lastStep
    )
  }

  /**
   * Theorem --- the domain of a constant function is the set it is defined on.
   *
   *  `dom(constantFunction(x, t)) = x`
   */
  val constantFunctionDomain = Theorem(
    functionDomain(constantFunction(x, t)) === x
  ) {
    // since we define constant function using the cartesian product, this requires a bit more effort
    val constFunDef = have((constantFunction(x, t) === cartesianProduct(x, singleton(t)))) by Weakening(constantFunction.definition of constantFunction(x, t))

    have(∀(p, in(p, functionDomain(constantFunction(x, t))) <=> ∃(a, in(pair(p, a), constantFunction(x, t))))) by InstantiateForall(functionDomain(constantFunction(x, t)))(
      functionDomain.definition of (r := constantFunction(x, t))
    )
    val domainDef = thenHave(in(p, functionDomain(constantFunction(x, t))) <=> ∃(a, in(pair(p, a), constantFunction(x, t)))) by InstantiateForall(p)

    val rhs = have(∃(a, in(pair(p, a), constantFunction(x, t))) ==> in(p, x)) subproof {
      val assumption = assume(∃(a, in(pair(p, a), constantFunction(x, t))))
      val aw = witness(assumption)
      have(in(pair(p, aw), constantFunction(x, t))) by Restate
      thenHave(in(pair(p, aw), cartesianProduct(x, singleton(t)))) by Substitution.ApplyRules(constFunDef)

      have(thesis) by Tautology.from(lastStep, pairInCartesianProduct of (a := p, b := aw, y := singleton(t)))
    }

    val lhs = have(in(p, x) ==> ∃(a, in(pair(p, a), constantFunction(x, t)))) subproof {
      assume(in(p, x))
      val tIn = have(in(t, singleton(t))) by Tautology.from(singletonHasNoExtraElements of (y := t, x := t))

      have(in(pair(p, t), cartesianProduct(x, singleton(t)))) by Tautology.from(
        pairInCartesianProduct of (a := p, b := t, y := singleton(t)),
        tIn
      )
      thenHave(∃(a, in(pair(p, a), cartesianProduct(x, singleton(t))))) by RightExists
      thenHave(∃(a, in(pair(p, a), constantFunction(x, t)))) by Substitution.ApplyRules(constFunDef)
    }

    have(in(p, x) <=> in(p, functionDomain(constantFunction(x, t)))) by Tautology.from(domainDef, rhs, lhs)
    val ext = thenHave(∀(p, in(p, x) <=> in(p, functionDomain(constantFunction(x, t))))) by RightForall

    have(thesis) by Tautology.from(ext, extensionalityAxiom of (y := functionDomain(constantFunction(x, t))))
  }

  /**
   * Theorem --- a constant function is functional.
   */
  val constantFunctionIsFunctional = Theorem(
    functional(constantFunction(x, t))
  ) {
    val constFunDef = have((constantFunction(x, t) === cartesianProduct(x, singleton(t)))) by Weakening(constantFunction.definition of constantFunction(x, t))

    val isRelation = have(relation(constantFunction(x, t))) subproof {
      have(relation(cartesianProduct(x, singleton(t)))) by Weakening(cartesianProductIsRelation of (y := singleton(t)))
      thenHave(thesis) by Substitution.ApplyRules(constFunDef)
    }

    val uniqueY = have(∀(a, ∃(y, in(pair(a, y), constantFunction(x, t))) ==> ∃!(y, in(pair(a, y), constantFunction(x, t))))) subproof {
      have(∃(y, in(pair(a, y), constantFunction(x, t))) ==> ∃!(y, in(pair(a, y), constantFunction(x, t)))) subproof {
        val existence = assume(∃(y, in(pair(a, y), constantFunction(x, t))))

        val uniqueness = have((in(pair(a, y), constantFunction(x, t)), in(pair(a, p), constantFunction(x, t))) |- (y === p)) subproof {
          val assumption1 = assume(in(pair(a, y), constantFunction(x, t)))
          val assumption2 = assume(in(pair(a, p), constantFunction(x, t)))

          have(in(pair(a, y), cartesianProduct(x, singleton(t)))) by Substitution.ApplyRules(constFunDef)(assumption1)
          val eq1 = have(y === t) by Tautology.from(
            pairInCartesianProduct of (b := y, y := singleton(t)),
            lastStep,
            singletonHasNoExtraElements of (x := t)
          )

          have(in(pair(a, p), cartesianProduct(x, singleton(t)))) by Substitution.ApplyRules(constFunDef)(assumption2)
          val eq2 = have(p === t) by Tautology.from(
            pairInCartesianProduct of (b := p, y := singleton(t)),
            lastStep,
            singletonHasNoExtraElements of (x := t, y := p)
          )

          have(y === p) by Tautology.from(eq1, eq2, equalityTransitivity of (x := y, y := t, z := p))
        }

        have(∃!(y, in(pair(a, y), constantFunction(x, t)))) by ExistenceAndUniqueness(in(pair(a, y), constantFunction(x, t)))(existence, uniqueness)
      }
      thenHave(thesis) by RightForall
    }

    have(thesis) by Tautology.from(isRelation, uniqueY, functional.definition of (f := constantFunction(x, t)))
  }

  /**
   * Theorem --- a constant function is a function from `x` to the singleton of `t`.
   *
   *    `constantFunction(x, t) ∈ x → {t}`
   */
  val constantFunctionFunctionFrom = Theorem(
    functionFrom(constantFunction(x, t), x, singleton(t))
  ) {
    val constFunDef = have((constantFunction(x, t) === cartesianProduct(x, singleton(t)))) by Weakening(constantFunction.definition of constantFunction(x, t))

    have(∀(a, in(a, setOfFunctions(x, singleton(t))) <=> (in(a, powerSet(cartesianProduct(x, singleton(t)))) /\ functionalOver(a, x)))) by InstantiateForall(setOfFunctions(x, singleton(t)))(
      setOfFunctions.definition of (y := singleton(t))
    )
    val setOfFunctionsDef = thenHave(
      in(constantFunction(x, t), setOfFunctions(x, singleton(t))) <=> (in(constantFunction(x, t), powerSet(cartesianProduct(x, singleton(t)))) /\ functionalOver(constantFunction(x, t), x))
    ) by InstantiateForall(constantFunction(x, t))

    have(in(cartesianProduct(x, singleton(t)), powerSet(cartesianProduct(x, singleton(t))))) by Weakening(elemInItsPowerSet of (x := cartesianProduct(x, singleton(t))))
    val inPowerSet = thenHave(in(constantFunction(x, t), powerSet(cartesianProduct(x, singleton(t))))) by Substitution.ApplyRules(constFunDef)

    val funcOver = have(functionalOver(constantFunction(x, t), x)) by Tautology.from(
      constantFunctionIsFunctional,
      constantFunctionDomain,
      functionalOver.definition of (f := constantFunction(x, t))
    )

    have(thesis) by Tautology.from(
      inPowerSet,
      funcOver,
      setOfFunctionsDef,
      functionFrom.definition of (f := constantFunction(x, t), y := singleton(t))
    )
  }
}
