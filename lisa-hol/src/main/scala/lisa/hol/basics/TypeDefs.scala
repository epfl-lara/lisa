package lisa.hol.basics

import lisa.hol.HOLHelperTheorems.*
import lisa.hol.HOLSteps.HOLProofType
import lisa.hol.VarsAndFunctions.*
import lisa.hol.basics.Exists.{hexists, hexistsCorrect}
import lisa.hol.basics.Truth.{holT, holTruth}
import lisa.maths.SetTheory.Base.Comprehension.*
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.maths.SetTheory.Types.TypingRules.{BetaReduction, TAbs}
import lisa.utils.prooflib.BasicStep.*
import lisa.utils.prooflib.Exports.*

/**
 * HOL Light basic type-definition justifications.
 *
 * Model a new type as the subset of its representation type selected by its
 * characteristic predicate.
 */
object TypeDefs extends lisa.HOL:

  val A = typevar

  val x = typedvar(A)
  val z = variable[Ind]
  val p = typedvar(A ->: 𝔹)
  val B = { z ∈ A | (p * z) === holT }
  val y = typedvar(B)
  val r = typedvar(B)
  val a, u, v = variable[Ind]
  private val BNonEmpty = ∃(z, z ∈ B)
  private val boolType = computeType(One)

  val lib = lisa.SetTheoryLibrary

  private def absProperty(a: Expr[Ind], b: Expr[Ind]): Expr[Prop] =
    (b ∈ B) /\ (((p * a) === holT) <=> (a === b))

  private def absValue(a: Expr[Ind]): Expr[Ind] =
    ε(y, absProperty(a, y))

  private def repValue(b: Expr[Ind]): Expr[Ind] =
    ε(x, b === x)

  val absFun = fun(x, absValue(x))
  val repFun = fun(r, repValue(r))

  private val membershipB = Theorem(z ∈ B <=> (z ∈ A) /\ ((p * z) === holT)):
    have(thesis) by lisa.maths.SetTheory.Base.Comprehension.apply

  private val absChoiceB = Theorem((BNonEmpty, x ∈ A) |- absProperty(x, absValue(x))):
    val positive = have((x ∈ A, (p * x) === holT) |- absProperty(x, absValue(x))) subproof:
      have((x ∈ A, (p * x) === holT) |- x ∈ B) by Tautology.from(membershipB of (z := x))
      have((x ∈ A, (p * x) === holT) |- absProperty(x, x)) by Tautology.from(lastStep)
      thenHave(thesis) by RightEpsilon.withParameters(absProperty(x, y), y, x)

    val negative = have((x ∈ A, !((p * x) === holT), BNonEmpty) |- absProperty(x, absValue(x))) subproof:
      have((x ∈ A, !((p * x) === holT)) |- !(x ∈ B)) by Tautology.from(membershipB of (z := x))
      val xNotInB = lastStep

      have((x ∈ A, !((p * x) === holT), y ∈ B, x === y) |- x ∈ B) by Congruence
      have((x ∈ A, !((p * x) === holT), y ∈ B) |- !(x === y)) by Tautology.from(xNotInB, lastStep)
      have((x ∈ A, !((p * x) === holT), y ∈ B) |- absProperty(x, y)) by Tautology.from(lastStep)
      thenHave((x ∈ A, !((p * x) === holT), y ∈ B) |- absProperty(x, absValue(x))) by
        RightEpsilon.withParameters(absProperty(x, y), y, y)
      thenHave((x ∈ A, !((p * x) === holT), BNonEmpty) |- absProperty(x, absValue(x))) by
        LeftExists.withParameters(y ∈ B, y)

    have(thesis) by Tautology.from(positive, negative)

  private val absFixedB = Theorem(x ∈ B |- absFun * x === x):
    val xInB = assume(x ∈ B)

    val membership = have((x ∈ A) /\ ((p * x) === holT)) by Tautology.from(membershipB of (z := x))
    val xInA = have(x ∈ A) by Tautology.from(membership)
    val pTrue = have((p * x) === holT) by Tautology.from(membership)
    val nonEmpty = have(BNonEmpty) by RightExists(xInB)
    val choice = have(absProperty(x, absValue(x))) by Tautology.from(absChoiceB, nonEmpty, xInA)
    val xEqValue = have(x === absValue(x)) by Tautology.from(choice, pTrue)
    val valueEqX = have(absValue(x) === x) by Congruence.from(xEqValue)

    val T, e2 = variable[Ind]
    val e = variable[Ind >>: Ind]
    val beta = have(absFun * x === absValue(x)) by Tautology.from(
      BetaReduction of (T := A, e := λ(x, absValue(x)), e2 := x),
      xInA
    )
    have(thesis) by Congruence.from(beta, valueEqX)

  private val repFixedB = Theorem(r ∈ B |- repFun * r === r):
    assume(r ∈ B)

    have(r === r) by Restate
    val rEqValue = thenHave(r === repValue(r)) by RightEpsilon.withParameters(r === x, x, r)
    val valueEqR = have(repValue(r) === r) by Congruence.from(rEqValue)

    val T, e2 = variable[Ind]
    val e = variable[Ind >>: Ind]
    val beta = have(repFun * r === repValue(r)) by Tautology.from(
      BetaReduction of (T := B, e := λ(r, repValue(r)), e2 := r)
    )
    have(thesis) by Congruence.from(beta, valueEqR)

  private val equalityTypingB = Theorem((u ∈ A, v ∈ A) |- (holeq(A) * u * v) ∈ boolType):
    have(thesis) by Typecheck.prove

  private val absTypingB = HOLTheorem(BNonEmpty |- absFun :: A ->: B):
    val T, e2 = variable[Ind]
    val T1 = variable[Ind]
    val T2, e = variable[Ind >>: Ind]
    val body = λ(a, absValue(a))
    val codomain = λ(a, B)
    val valueTyping = have((BNonEmpty, a ∈ A) |- absValue(a) ∈ B) by Weakening(absChoiceB of (x := a))
    val bodyBeta = have(a ∈ A |- body(a) === absValue(a)) by Weakening(
      BetaReduction of (T := A, e := body, e2 := a)
    )
    val codomainBeta = have(a ∈ A |- codomain(a) === B) by Weakening(
      BetaReduction of (T := A, e := codomain, e2 := a)
    )
    have((BNonEmpty, a ∈ A) |- body(a) ∈ codomain(a)) by Congruence.from(valueTyping, bodyBeta, codomainBeta)
    thenHave(BNonEmpty |- (a ∈ A) ==> (body(a) ∈ codomain(a))) by RightImplies
    thenHave(BNonEmpty |- ∀(a, (a ∈ A) ==> (body(a) ∈ codomain(a)))) by RightForall
    val premise = lastStep
    val pivot = ∀(a, (a ∈ A) ==> (body(a) ∈ codomain(a)))
    val abstraction = have(pivot |- absFun ∈ (A ->: B)) by Restate.from(
      TAbs of (T1 := A, T2 := codomain, e := body)
    )
    have(thesis) by Cut.withParameters(pivot)(premise, abstraction)

  private val repTypingB = HOLTheorem(repFun :: B ->: A):
    val T, e2 = variable[Ind]
    val T1 = variable[Ind]
    val T2, e = variable[Ind >>: Ind]
    val body = λ(a, repValue(a))
    val codomain = λ(a, A)
    val valueTyping = have(a ∈ B |- repValue(a) ∈ A) subproof:
      val aInA = have(a ∈ B |- a ∈ A) by Tautology.from(membershipB of (z := a))
      have(a ∈ B |- a === a) by Restate
      val aEqValue = thenHave(a ∈ B |- a === repValue(a)) by RightEpsilon.withParameters(a === x, x, a)
      have(thesis) by Congruence.from(aInA, aEqValue)
    val bodyBeta = have(a ∈ B |- body(a) === repValue(a)) by Weakening(
      BetaReduction of (T := B, e := body, e2 := a)
    )
    val codomainBeta = have(a ∈ B |- codomain(a) === A) by Weakening(
      BetaReduction of (T := B, e := codomain, e2 := a)
    )
    have(a ∈ B |- body(a) ∈ codomain(a)) by Congruence.from(valueTyping, bodyBeta, codomainBeta)
    thenHave((a ∈ B) ==> (body(a) ∈ codomain(a))) by RightImplies
    thenHave(∀(a, (a ∈ B) ==> (body(a) ∈ codomain(a)))) by RightForall
    val premise = lastStep
    val pivot = ∀(a, (a ∈ B) ==> (body(a) ∈ codomain(a)))
    val abstraction = have(pivot |- repFun ∈ (B ->: A)) by Restate.from(
      TAbs of (T1 := B, T2 := codomain, e := body)
    )
    have(thesis) by Cut.withParameters(pivot)(premise, abstraction)

  private val absThmB = HOLTheorem(absFun * (repFun * y) =:= y):
    val yInB = assume(y ∈ B)
    val repY = have(repFun * y === y) by Weakening(repFixedB of (r := y))
    val absY = have(absFun * y === y) by Weakening(absFixedB of (x := y))
    val mappedRepY = have(absFun * (repFun * y) === absFun * y) by Congruence.from(repY)
    val roundTrip = have(absFun * (repFun * y) === y) by Congruence.from(mappedRepY, absY)
    val roundTripTyping = have((absFun * (repFun * y)) ∈ B) by Congruence.from(yInB, roundTrip)

    have(thesis) by Tautology.from(
      roundTrip,
      roundTripTyping,
      yInB,
      eqAlign of (A := B, x := absFun * (repFun * y), y := y)
    )

  private val repThmB = HOLTheorem(BNonEmpty |- (p * x) =:= ((repFun * (absFun * x)) =:= x)):
    val nonEmpty = assume(BNonEmpty)
    val xInA = assume(x ∈ A)
    val pTyping = assume(p ∈ computeType(p))
    val absX = absFun * x
    val roundTrip = repFun * absX
    val innerEquality = roundTrip =:= x

    val T, e2, q = variable[Ind]
    val e = variable[Ind >>: Ind]
    val choice = have(absProperty(x, absValue(x))) by Tautology.from(absChoiceB, nonEmpty, xInA)
    val valueInB = have(absValue(x) ∈ B) by Tautology.from(choice)
    val absBeta = have(absX === absValue(x)) by Weakening(
      BetaReduction of (T := A, e := λ(x, absValue(x)), e2 := x)
    )
    val absXInB = have(absX ∈ B) by Congruence.from(valueInB, absBeta)
    val repAbsX = have(roundTrip === absX) by Cut(absXInB, repFixedB of (r := absX))
    val absXInA = have(absX ∈ A) by Tautology.from(membershipB of (z := absX), absXInB)
    val roundTripInA = have(roundTrip ∈ A) by Congruence.from(absXInA, repAbsX)

    val forward = have(((p * x) === holT) ==> (roundTrip === x)) subproof:
      val pTrue = assume((p * x) === holT)
      val xInB = have(x ∈ B) by Tautology.from(membershipB of (z := x), xInA, pTrue)
      val absXIsX = have(absX === x) by Cut(xInB, absFixedB)
      val repXIsX = have(repFun * x === x) by Cut(xInB, repFixedB of (r := x))
      val mappedAbs = have(roundTrip === repFun * x) by Congruence.from(absXIsX)
      have(roundTrip === x) by Congruence.from(mappedAbs, repXIsX)

    val backward = have((roundTrip === x) ==> ((p * x) === holT)) subproof:
      val roundTripIsX = assume(roundTrip === x)
      val roundTripInB = have(roundTrip ∈ B) by Congruence.from(absXInB, repAbsX)
      val xInB = have(x ∈ B) by Congruence.from(roundTripInB, roundTripIsX)
      have((p * x) === holT) by Tautology.from(membershipB of (z := x), xInB)

    val characteristic = have(((p * x) === holT) <=> (roundTrip === x)) by Tautology.from(forward, backward)
    val truthAlignment = have(((p * x) === holT) <=> ((p * x) === One)) by Congruence.from(holTruth)
    val innerAlignment = have((roundTrip === x) <=> (innerEquality === One)) by Tautology.from(
      roundTripInA,
      xInA,
      eqAlign of (A := A, x := roundTrip, y := x)
    )
    val booleanEquality = have(((p * x) === One) <=> (innerEquality === One)) by Tautology.from(
      characteristic,
      truthAlignment,
      innerAlignment
    )

    val aNonEmpty = have(∃(a, a ∈ A)) by RightExists.withParameters(a ∈ A, a, x)(xInA)
    val innerEqualityTyping = have(innerEquality ∈ boolType) by
      Cut(roundTripInA, equalityTypingB of (u := roundTrip, v := x))
    val pXTyping = have(HOLProofType(p * x))
    val reversedBooleanEquality = have((innerEquality === One) <=> ((p * x) === One)) by Tautology.from(booleanEquality)
    val termsEqual = have((p * x) === innerEquality) by Tautology.from(
      pXTyping,
      aNonEmpty,
      innerEqualityTyping,
      reversedBooleanEquality,
      lisa.hol.HOLSteps.propExt of (p := p * x, q := innerEquality)
    )

    have(thesis) by Tautology.from(
      termsEqual,
      pXTyping,
      innerEqualityTyping,
      eqAlign of (A := boolType, x := p * x, y := innerEquality)
    )

  private val existsP = hexists(A) * p

  private val existsImpliesNonEmptyB = HOLTheorem(existsP |- BNonEmpty):
    val P = variable[Ind]
    val exists = assume(existsP)
    val nonEmptyA = assume(∃(a, a ∈ A))
    val pTyping = assume(p ∈ computeType(p))
    val boundedExists = have(∃(x :: A, p * x)) by Tautology.from(
      exists,
      nonEmptyA,
      pTyping,
      hexistsCorrect of (A := A, P := p, x := x)
    )

    val pTrue = have((x ∈ A, (p * x) === One) |- (p * x) === holT) by
      Congruence.from(holTruth)
    val witnessInB = have((x ∈ A, (p * x) === One) |- x ∈ B) by Tautology.from(
      membershipB of (z := x),
      pTrue
    )
    thenHave((x ∈ A, (p * x) === One) |- BNonEmpty) by RightExists.withParameters(z ∈ B, z, x)
    thenHave((x ∈ A) /\ ((p * x) === One) |- BNonEmpty) by Restate
    thenHave(∃(x, (x ∈ A) /\ ((p * x) === One)) |- BNonEmpty) by
      LeftExists.withParameters((x ∈ A) /\ ((p * x) === One), x)
    have(thesis) by Tautology.from(lastStep, boundedExists)

  val absTyping = HOLTheorem(existsP |- absFun :: A ->: B):
    have(thesis) by Cut.withParameters(BNonEmpty)(existsImpliesNonEmptyB, absTypingB)

  val repTyping = HOLTheorem(repFun :: B ->: A):
    have(thesis) by Restate.from(repTypingB)

  val absThm = HOLTheorem(absFun * (repFun * y) =:= y):
    have(thesis) by Restate.from(absThmB)

  val repThm = HOLTheorem(existsP |- (p * x) =:= ((repFun * (absFun * x)) =:= x)):
    have(thesis) by Cut.withParameters(BNonEmpty)(existsImpliesNonEmptyB, repThmB)
