package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.maths.SetTheory.Types.ADTv2.encoding.Utils.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.Pair.given
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Types.ADTv2.encoding.UsefullTheorems.*
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.SimpleDeducedSteps.*

private[encoding] trait SyntacticADTIntroduction[N <: Arity]
    extends SyntacticADTInjectivity[N] {
  this: SyntacticADT[N] =>

  private val P = variable[Ind >>: Prop]

  // *************************
  // * INTRODUCTION FUNCTION *
  // *************************

  /**
   *  Lemma --- The introduction function is monotonic with respect to set inclusion.
   *
   *  `s ⊆ t |- introductionFunction(s) ⊆ introductionFunction(t)`
   */
  private[encoding] val introductionFunctionMononotic = Lemma(
    subset(s, t) |- isInIntroductionFunctionImage(s)(x) ==> isInIntroductionFunctionImage(
      t
    )(x)
  ) {
    // In the rest of the proof we assume that s ⊆ t

    // STEP 0: Caching predicates that are often used
    val subsetST = s ⊆ t
    val isConstructorXS = isConstructor(x, s)
    val isConstructorXT = isConstructor(x, t)

    // STEP 1: Prove x ∈ s implies x ∈ t
    have(s ⊆ t |- forall(z, in(z, s) ==> in(z, t))) by Congruence.from(
      subsetAxiom of (x := s, y := t)
    )
    val subsetElimination =
      thenHave(s ⊆ t |- in(z, s) ==> in(z, t)) by InstantiateForall(z)

    // STEP 2: For each constructor, prove that if x is an instance of that constructor with self referencing arguments in s
    // then it is also an instance of some constructor with self referencing arguments in t
    val isConstructorXSImpliesT =
      for c <- constructors yield
        // STEP 2.0: Caching predicates that are often used
        // TODO change identifier
        val labelEq = x === c.term2
        val isConstructorCXS = isConstructor(c, x, s)
        val isConstructorCXT = isConstructor(c, x, t)
        val varsWellTypedS = wellTypedFormula(c.signature2)(s)
        val varsWellTypedT = wellTypedFormula(c.signature2)(t)

        if c.arity == 0 then
          have((subsetST, isConstructorCXS) |- isConstructorXT) by Restate
        else
          // STEP 2.1: Prove that we can expand the domain of the (quantified) variables of the constructor
          val andSeq =
            for (v, ty) <- c.signature2
            yield have((subsetST, varsWellTypedS) |- in(v, ty.getOrElse(t))) by Weakening(
              subsetElimination of (z := v)
            )
          val expandingDomain =
            have((subsetST, varsWellTypedS) |- varsWellTypedT) by RightAnd(andSeq*)
          val weakeningLabelEq = have(labelEq |- labelEq) by Hypothesis
          have(
            (subsetST, varsWellTypedS, labelEq) |- varsWellTypedT /\ labelEq
          ) by RightAnd(expandingDomain, weakeningLabelEq)

          // STEP 2.2: Prove that x stays an instance of this constructor if we expand the domain of the variables
          thenHave(
            (subsetST, varsWellTypedS, labelEq) |- isConstructorCXT
          ) by QuantifiersIntro(c.variables2)
          thenHave((subsetST, varsWellTypedS /\ labelEq) |- isConstructorCXT) by LeftAnd
          thenHave((subsetST, isConstructorCXS) |- isConstructorCXT) by QuantifiersIntro(
            c.variables2
          )

          // STEP 2.3: Weaken the conclusion to some constructor instead of a specific one
          thenHave((subsetST, isConstructorCXS) |- isConstructorXT) by Weakening

    // STEP 3: Prove that this holds for any constructor
    // ? Steps 2 and 3 can be merged and optimized through the repeated use of an external theorem like [[ADTHelperTheorems.unionPreimageMonotonic]]
    if constructors.isEmpty then
      have((subsetST, isConstructorXS) |- isConstructorXT) by Restate
    else
      have((subsetST, isConstructorXS) |- isConstructorXT) by LeftOr(
        isConstructorXSImpliesT*
      )

    // STEP 4: Prove the thesis by showing that making the union with the function argument does not change the monotonicity
    thenHave(subsetST |- isConstructorXS ==> isConstructorXT) by RightImplies
    have(thesis) by Cut(
      lastStep,
      unionPreimageMonotonic of (P := λ(s, isConstructorXS))
    )
  }

    /**
   *  Lemma --- Every constructor is in the image of the introduction function.
   *
   *  `For every c ∈ constructors, xi ∈ s, ..., xj ∈ s |- c(x1, ..., xn) ∈ introductionFunction(s)`
   */
  private[encoding] val constructorIsInIntroductionFunction = constructors.map(c =>
    // Caching
    val constructorVarsInDomainCS = constructorVarsInDomain(c, s)

    c -> Lemma(constructorVarsInDomainCS |- isInIntroductionFunctionImage(s)(c.term)) {

      have(
        constructorVarsInDomainCS |- constructorVarsInDomainCS /\ (c.term === c.term)
      ) by Restate

      // Replace each variable on the LHS of the equality by a quantified variable and then introduce an existential quantifier
      c.variables2.foldRight((c.variables1, List[Variable[Ind]]()))((v, acc) =>

        // At each step remove a variable and add a quantified one
        val oldVariables = acc._1.init
        val newVariables = v :: acc._2
        val vars = oldVariables ++ newVariables

        thenHave(
          constructorVarsInDomainCS |- existsSeq(
            newVariables,
            wellTypedFormula(vars.zip(c.specification))(s) /\ (c.term(vars) === c.term)
          )
        ) by RightExists

        (oldVariables, newVariables)
      )

      thenHave(
        constructorVarsInDomainCS |- isInIntroductionFunctionImage(s)(c.term)
      ) by Weakening
    }
  ).toMap
}
