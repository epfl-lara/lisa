package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.UsefulTheorems.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Base.Pair
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.utils.prooflib.BasicStepTactic.Restate

private[encoding] trait SyntacticADTTerm[N <: Arity] extends SyntacticADTHeight[N] {
  this: SyntacticADT[N] =>

  // ********
  // * TERM *
  // ********

   // Temporary placeholder while ADTv2 function-definition integration is finalized.
  private val polymorphicTermConst = Constant[Ind](s"${name}Polyterm")
  registerConstant(polymorphicTermConst)
  val polymorphicTerm: Expr[Ind] = polymorphicTermConst

  private val termConst = Constant[Ind](s"${name}Term")
  registerConstant(termConst)
  val term: Expr[Ind] = termConst

  private[encoding] def termDefinitionFormula(adt: Expr[Ind]): Expr[Prop] =
    forall(t, t ∈ adt <=> forall(h, isHeight(h) ==> t ∈ unionRange(h)))

  private[encoding] val termDefinition: Expr[Prop] = termDefinitionFormula(term)

  private[encoding] val termSatisfiesDefinition = Lemma(termDefinition) {
    // have(thesis) by InstantiateForall(term)(polymorphicTerm.definition)
    have(thesis) by Sorry
  }
  

  private[encoding] val termExistence = Lemma(existsOne(z, termDefinitionFormula(z))) {

    // STEP 0: Caching
    val termDefinitionRight = forall(h, isHeight(h) ==> in(t, unionRange(h)))
    val inUnionRangeF = in(t, unionRange(f))

    // STEP 1: Prove that there exists a term satisfying the definition of this ADT.
    // Specifically, this term is the union of all the terms with a height.
    have(exists(z, termDefinition)) subproof {

      // STEP 1.1: Prove the forward implication of the definition, using the uniqueness of the height function
      have(inUnionRangeF |- inUnionRangeF) by Hypothesis
      thenHave((f === h, inUnionRangeF) |- in(t, unionRange(h))) by
        RightSubstEq.withParameters(List((f, h)), (Seq(f), inUnionRangeF))
      have(
        (isHeight(f), isHeight(h), inUnionRangeF) |-
          in(t, unionRange(h))
      ) by Cut(heightFunctionUniqueness2, lastStep)
      thenHave(
        (isHeight(f), inUnionRangeF) |-
          isHeight(h) ==> in(t, unionRange(h))
      ) by RightImplies
      thenHave((isHeight(f), inUnionRangeF) |- termDefinitionRight) by
        RightForall
      val forward =
        thenHave(isHeight(f) |- inUnionRangeF ==> termDefinitionRight) by
          RightImplies

      // STEP 1.2: Prove the backward implication of the definition
      have(termDefinitionRight |- termDefinitionRight) by Hypothesis
      thenHave(termDefinitionRight |- isHeight(f) ==> inUnionRangeF) by
        InstantiateForall(f)
      val backward =
        thenHave(isHeight(f) |- termDefinitionRight ==> inUnionRangeF) by Restate

      // STEP 1.3: Use the existence of the height function to prove the existence of this ADT
      have(isHeight(f) |- inUnionRangeF <=> termDefinitionRight) by
        RightIff(forward, backward)
      thenHave(
        isHeight(f) |- forall(t, inUnionRangeF <=> termDefinitionRight)
      ) by RightForall

      thenHave(
        isHeight(f) |- exists(z, forall(t, in(t, z) <=> termDefinitionRight))
      ) by RightExists
      thenHave(
        exists(f, isHeight(f)) |-
          exists(z, forall(t, in(t, z) <=> termDefinitionRight))
      ) by LeftExists
      have(exists(z, forall(t, in(t, z) <=> termDefinitionRight))) by Cut(heightFunctionExistence of (h := f), lastStep)
      thenHave(thesis) by Sorry //Tautology
    }

    // STEP 2: Conclude using the extension by definition

    have(thesis) by Sorry
      // Cut(lastStep, uniqueByExtension of (schemPred := lambda(t, termDefinitionRight)))
  }

  private[encoding] val termHasHeight = Lemma(
    isHeight(h) |- in(x, term) <=> ∃(n, in(n, N) /\ in(x, app(h, n)))
  )(have(thesis) by Sorry)

  private[encoding] val termsHaveHeight = constructors.map(c =>
    c -> Lemma(
      isHeight(h) |-
        (constructorVarsInDomain(c, term) <=>
          ∃(n, in(n, N) /\ constructorVarsInDomain(c, app(h, n))))
    )(have(thesis) by Sorry)
  ).toMap

  private[encoding] val heightConstructor = constructors.map(c =>
    c -> Lemma(
      (isHeight(h), in(n, N), constructorVarsInDomain(c, app(h, n))) |-
        in(c.term, app(h, successor(n)))
    )(have(thesis) by Sorry)
  ).toMap

  val intro = constructors
    .map(c =>
      c -> Lemma(
        simplify(constructorVarsInDomain(c, term)) |- simplify(in(c.term, term))
      )(have(thesis) by Sorry)
    ).toMap
}
