package lisa.hol
import lisa.maths.SetTheory.Base.Predef.singleton
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.maths.SetTheory.Types.TypingHelpers.TypedConstant
import lisa.maths.SetTheory.Types.TypingHelpers.TypedConstantFunctional
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.maths.SetTheory.Types.TypingRules.{TAbs, BetaReduction}
import lisa.maths.SetTheory.Base.Predef.*

import lisa.utils.prooflib.Substitute

import VarsAndFunctions.HOLConstantType
import lisa.utils.prooflib.BasicStep.LeftOr
import lisa.utils.prooflib.BasicStep.RightAnd
import lisa.utils.prooflib.BasicStep.RightSubstEq
import lisa.utils.prooflib.BasicStep.Weakening
import lisa.utils.prooflib.BasicStep.Restate
import lisa.utils.prooflib.BasicStep.RightSubstEq
import lisa.utils.prooflib.BasicStep.RightSubstEq
import lisa.utils.unification.UnificationUtils.Substitution
import lisa.utils.prooflib.BasicStep.RightSubstEq
import lisa.utils.prooflib.BasicStep.LeftExists

object HOLHelperTheorems extends lisa.Main {
  given lisa.SetTheoryLibrary.type = lisa.SetTheoryLibrary
  private val f = variable[Ind]
  private val x = variable[Ind]
  private val y = variable[Ind]
  private val z = variable[Ind]
  private val a = variable[Ind]
  private val A = variable[Ind]
  private val B = variable[Ind]
  private val any = DEF(λ(x, ⊤))
  private val G = variable[Ind >>: Ind]
  private val H = variable[Ind >>: Ind]
  private val P = variable[Prop]
  private val lib = lisa.SetTheoryLibrary

  // A ->: B is the set of functions from A to B
  val Bool: Constant[Ind] = {
    val 𝔹 = DEF(unorderedPair(∅, singleton(∅)))
    𝔹
  }

  val `0 : 𝔹` = Theorem(∅ :: Bool) {
    have(∅ :: unorderedPair(∅, singleton(∅))) by Tautology.from(pairAxiom of (z := ∅, x := ∅, y := singleton(∅)))
    thenHave(thesis) by Substitute(Bool.definition)
  }

  val `1 : 𝔹` = Theorem(singleton(∅) :: Bool) {
    have(singleton(∅) :: unorderedPair(∅, singleton(∅))) by Tautology.from(pairAxiom of (z := singleton(∅), x := ∅, y := singleton(∅)))
    thenHave(thesis) by Substitute(Bool.definition)
  }

  val Zero: TypedConstant = {
    val Zero = DEF(∅)
    val Zero_in_B = Theorem(Zero :: Bool) {
      have(thesis) by Substitute(Zero.definition)(`0 : 𝔹`)
    }
    Zero.typedWith(Bool)(Zero_in_B)
  }

  val One: TypedConstant = {
    val One = DEF(singleton(∅))
    val One_in_B = Theorem(One :: Bool) {
      have(thesis) by Substitute(One.definition)(`1 : 𝔹`)
    }
    One.typedWith(Bool)(One_in_B)
  }

  val zero_in_B = Theorem(Zero :: Bool) {
    have(Zero :: Bool) by Typecheck.prove
  }

  val boolNonEmpty = Theorem(exists(x, (x ∈ Bool))) {
    have(thesis) by RightExists(One.justif)
  }
  val 𝔹 = HOLConstantType(Bool.id, boolNonEmpty)

  val `0 != 1` = Theorem(!(Zero === One)):
    have(!(∅ === singleton(∅))) by Restate.from(Singleton.nonEmpty of (x := ∅))
    thenHave(thesis) by Substitute(Zero.definition, One.definition)

  val boolBivalence = Theorem(
    (x :: 𝔹) <=> (x === Zero) \/ (x === One)
  ):
    val fwd = have(x :: 𝔹 ==> (x === Zero) \/ (x === One)) subproof:
      assume(x :: 𝔹)
      have(x :: 𝔹) by Restate
      thenHave(x :: unorderedPair(∅, singleton(∅))) by Substitute(𝔹.definition)
      have((x === ∅) \/ (x === singleton(∅))) by Tautology.from(pairAxiom of (z := x, x := ∅, y := singleton(∅)), lastStep)
      thenHave((x === Zero) \/ (x === One)) by Substitute(Zero.definition, One.definition)

    val bwd = have((x === Zero) \/ (x === One) ==> x :: 𝔹) subproof:
      val zEq = have(x === Zero |- x :: 𝔹) by RightSubstEq.withParameters(Seq((Zero, x)), (Seq(x), x :: 𝔹))(Zero.justif)
      val oEq = have(x === One |- x :: 𝔹) by RightSubstEq.withParameters(Seq((One, x)), (Seq(x), x :: 𝔹))(One.justif)
      have(thesis) by Tautology.from(zEq, oEq)

    have(thesis) by RightAnd(fwd, bwd)

  val boolZeroXorOne = Theorem(x :: 𝔹 |- (x === Zero) <=> !(x === One)):
    assume(x :: 𝔹)
    val cases = have((x === Zero) \/ (x === One)) by Tautology.from(boolBivalence of (x := x))
    val zeroCase = have(x === Zero |- (x === Zero) <=> !(x === One)) subproof:
      have(x === Zero |- (x === Zero) <=> !(Zero === One)) by Tautology.from(`0 != 1`)
      thenHave(x === Zero |- (x === Zero) <=> !(x === One)) by RightSubstEq.withParameters(Seq((Zero, x)), (Seq(b), (x === Zero) <=> !(b === One)))

    val oneCase = have(x === One |- (x === Zero) <=> !(x === One)) subproof:
      have(x === One |- (One === Zero) <=> !(One === One)) by Tautology.from(`0 != 1`)
      thenHave(x === One |- (x === Zero) <=> !(x === One)) by RightSubstEq.withParameters(Seq((One, x)), (Seq(b), (b === Zero) <=> !(b === One)))

    have(thesis) by Tautology.from(cases, zeroCase, oneCase)

  private val eqTerm = ε(b, (b :: 𝔹) /\ ((b === One) <=> (x === y)))
  private def eqProp(b: Expr[Ind]) = (b :: 𝔹) /\ ((b === One) <=> (x === y))
  private val eqTermProperty = Theorem(eqProp(eqTerm)):
    val eqCase = have(x === y |- eqProp(eqTerm)) subproof:
      assume(x === y)
      have((One === One) <=> (x === y)) by Restate
      have((One :: 𝔹) /\ ((One === One) <=> (x === y))) by RightAnd(One.justif, lastStep)
      thenHave(eqProp(eqTerm)) by RightEpsilon.withParameters((b :: 𝔹) /\ ((b === One) <=> (x === y)), b, One)
    val neqCase = have(!(x === y) |- eqProp(eqTerm)) subproof:
      assume(!(x === y))
      have((Zero === One) <=> (x === y)) by Tautology.from(`0 != 1`)
      have((Zero :: 𝔹) /\ ((Zero === One) <=> (x === y))) by RightAnd(Zero.justif, lastStep)
      thenHave(eqProp(eqTerm)) by RightEpsilon.withParameters((b :: 𝔹) /\ ((b === One) <=> (x === y)), b, Zero)
    have(thesis) by Tautology.from(eqCase, neqCase)

  private val eqBetaRed = Theorem((x :: A, y :: A) |- fun(x :: A, fun(y :: A, eqTerm)) * x * y === eqTerm):
    assume(x :: A, y :: A)

    val e = variable[Ind >>: Ind]
    val e2 = variable[Ind]
    val T = variable[Ind]

    val beta1 = have(fun(y :: A, eqTerm) * y === eqTerm) by Weakening(BetaReduction of (T := A, e2 := y, e := λ(y, eqTerm))) 
    val beta2 = have(fun(x :: A, fun(y :: A, eqTerm)) * x === fun(y :: A, eqTerm)) by Weakening(BetaReduction of (T := A, e2 := x, e := λ(x, fun(y :: A, eqTerm)))) 
    
    have(fun(x :: A, fun(y :: A, eqTerm)) * x * y === fun(x :: A, fun(y :: A, eqTerm)) * x * y) by Restate
    thenHave(fun(x :: A, fun(y :: A, eqTerm)) * x * y === fun(y :: A, eqTerm) * y) by Substitute(beta2)
    thenHave(fun(x :: A, fun(y :: A, eqTerm)) * x * y === eqTerm) by Substitute(beta1)


  val =:= : TypedConstantFunctional[Ind >>: Ind] = {
    val =:= = DEF(λ(A, fun(x :: A, fun(y :: A, ε(b, (b :: 𝔹) /\ ((b === One) <=> (x === y)))))))

    val typing_of_eq = Theorem(forall(A, =:=(A) :: (A ->: (A ->: 𝔹)))):
      val theEp = eqTerm
      val epType = theEp :: 𝔹
      val epProof = have(epType) by Weakening(eqTermProperty)

      val T1 = variable[Ind]
      val T2 = variable[Ind >>: Ind]
      val e = variable[Ind >>: Ind]

      // manual typing proof
      // to take epsilon binding x and y into account
      thenHave(x :: A ==> theEp :: 𝔹) by Weakening
      thenHave(∀(x :: A, theEp :: 𝔹)) by RightForall
      have(fun(x :: A, theEp) :: (A ->: 𝔹)) by Cut(lastStep, TAbs of (T1 := A, T2 := λ(x, 𝔹), e := λ(x, theEp)))
      thenHave(y :: A ==> fun(x :: A, theEp) :: (A ->: 𝔹)) by Weakening
      thenHave(∀(y :: A, fun(x :: A, theEp) :: (A ->: 𝔹))) by RightForall
      have(fun(x :: A, fun(y :: A, theEp)) :: (A ->: (A ->: 𝔹))) by Tautology.from(
        lastStep,
        TAbs of (T1 := A, T2 := λ(x, A ->: 𝔹), e := λ(y, fun(x :: A, theEp)))
      )

      // use this to conclude 
      thenHave(epType |- =:=(A) :: (A ->: (A ->: 𝔹))) by Substitute(=:=.definition)
      have(=:=(A) :: (A ->: (A ->: 𝔹))) by Cut(epProof, lastStep)
      thenHave(thesis) by RightForall
    
    TypedConstantFunctional[Ind >>: Ind](=:=.id, FunctionalClass(List(None), List(A), (A ->: (A ->: 𝔹))), typing_of_eq)
  }

  val eqRefl = Theorem((x :: A |- (=:=(A) * x * x) === One)):
    assume(x :: A)
    val theEp = ε(b, (b :: 𝔹) /\ ((b === One) <=> (x === x)))
    have((One :: 𝔹) /\ ((One === One) <=> (x === x))) by Tautology.from(One.justif)
    thenHave((theEp :: 𝔹) /\ ((theEp === One) <=> (x === x))) by RightEpsilon.withParameters((b :: 𝔹) /\ ((b === One) <=> (x === x)), b, One)
    val appliedEqOne = thenHave(theEp === One) by Weakening

    have(fun(x :: A, fun(y :: A, eqTerm)) * x * x === theEp) by Weakening(eqBetaRed of (y := x))

    thenHave(fun(x :: A, fun(y :: A, eqTerm)) * x * x === One) by Substitute(appliedEqOne)
    thenHave(thesis) by Substitute(=:=.definition)

  val eqAlign = Theorem((x :: A, y :: A) |- (x === y) <=> (=:=(A) * x * y === One)):
    assume(x :: A, y :: A)
    val fwd = have(x === y ==> (=:=(A) * x * y === One)) subproof:
      have(=:=(A) * x * x === One) by Weakening(eqRefl)
      thenHave(x === y |- =:=(A) * x * y === One) by RightSubstEq.withParameters(Seq((x, y)), (Seq(y), =:=(A) * x * y === One))

    val bwd = have((=:=(A) * x * y === One) ==> (x === y)) subproof:
      have((eqTerm === One) ==> (x === y)) by Weakening(eqTermProperty)
      thenHave(fun(x :: A, fun(y :: A, eqTerm)) * x * y === One ==> (x === y)) by Substitute(eqBetaRed)
      thenHave(thesis) by Substitute(=:=.definition)

    have(thesis) by RightAnd(fwd, bwd)

  val eqFromHol = Theorem((x :: A, y :: A, =:=(A) * x * y === One) |- x === y):
    val holEquality = =:=(A) * x * y === One
    val nativeEquality = x === y
    val holHypothesis = have(holEquality |- holEquality) by Hypothesis.withParameters(holEquality)
    val nativeHypothesis = have(nativeEquality |- nativeEquality) by Hypothesis.withParameters(nativeEquality)
    val backward = have((holEquality, holEquality ==> nativeEquality) |- nativeEquality) by
      LeftImplies.withParameters(holEquality, nativeEquality)(holHypothesis, nativeHypothesis)
    val aligned = have((holEquality, nativeEquality <=> holEquality) |- nativeEquality) by
      LeftIff.withParameters(nativeEquality, holEquality)(backward)
    have(thesis) by Cut.withParameters(nativeEquality <=> holEquality)(eqAlign, aligned)

  val eqToHol = Theorem((x :: A, y :: A, x === y) |- =:=(A) * x * y === One):
    val holEquality = =:=(A) * x * y === One
    val nativeEquality = x === y
    val nativeHypothesis = have(nativeEquality |- nativeEquality) by Hypothesis.withParameters(nativeEquality)
    val holHypothesis = have(holEquality |- holEquality) by Hypothesis.withParameters(holEquality)
    val forward = have((nativeEquality, nativeEquality ==> holEquality) |- holEquality) by
      LeftImplies.withParameters(nativeEquality, holEquality)(nativeHypothesis, holHypothesis)
    val aligned = have((nativeEquality, nativeEquality <=> holEquality) |- holEquality) by
      LeftIff.withParameters(nativeEquality, holEquality)(forward)
    have(thesis) by Cut.withParameters(nativeEquality <=> holEquality)(eqAlign, aligned)

  val eqAlignZero = Theorem((x :: A, y :: A) |- (!(x === y)) <=> (=:=(A) * x * y === Zero)):
    assume(x :: A, y :: A)

    val `x = y` = =:=(A) * x * y

    val typ = have(`x = y` :: 𝔹) by Typecheck.prove
    val conv = have((!(x === y)) <=> (!(`x = y` === One))) by Weakening(eqAlign)
    val bivalence = have((`x = y` === One) \/ (`x = y` === Zero)) by Tautology.from(boolBivalence of (x := `x = y`), typ)

    val fwd = have((!(x === y)) ==> (`x = y` === Zero)) by Tautology.from(conv, bivalence)

    val bwd = have((`x = y` === Zero) ==> (!(x === y))) subproof:
      assume(`x = y` === Zero)
      have(!(Zero === One)) by Weakening(`0 != 1`)
      thenHave(!(`x = y` === One)) by RightSubstEq.withParameters(Seq((Zero, `x = y`)), (Seq(x), !(x === One)))
      have(thesis) by Tautology.from(conv, lastStep)

    have(thesis) by RightAnd(fwd, bwd)

  val eqSymEq = Theorem((x :: A, y :: A) |- =:=(A) * x * y === =:=(A) * y * x):
    assume(x :: A, y :: A)

    val eqCase = have(x === y |- =:=(A) * x * y === =:=(A) * y * x) subproof:
      assume(x === y)
      val xyOne = have(=:=(A) * x * y === One) by Weakening(eqAlign)
      val yxOne = have(=:=(A) * y * x === One) by Weakening(eqAlign of (x := y, y := x))

      have(One === One) by Restate
      thenHave(thesis) by Substitute(xyOne, yxOne)

    val neqCase = have(!(x === y) |- =:=(A) * x * y === =:=(A) * y * x) subproof:
      assume(!(x === y))
      val xyZero = have(=:=(A) * x * y === Zero) by Weakening(eqAlignZero)
      val yxZero = have(=:=(A) * y * x === Zero) by Weakening(eqAlignZero of (x := y, y := x))

      have(Zero === Zero) by Restate
      thenHave(thesis) by Substitute(xyZero, yxZero)

    have(thesis) by Tautology.from(eqCase, neqCase)

  val eqSym = Theorem((x :: A, y :: A, =:=(A) * x * y === One) |- (=:=(A) * y * x === One)):
    assumeAll

    have(=:=(A) * x * y === One) by Restate
    thenHave(thesis) by Substitute(eqSymEq)
  
  val eqTrans = Theorem((x :: A, y :: A, z :: A, =:=(A) * x * y === One, =:=(A) * y * z === One) |- =:=(A) * x * z === One):
    assume(x :: A, y :: A, z :: A, =:=(A) * x * y === One, =:=(A) * y * z === One)

    val `x = y` = have(x === y) by Weakening(eqAlign of (x := x, y := y))
    val `y = z` = have(y === z) by Weakening(eqAlign of (x := y, y := z))

    have(y === z |- x === z) by RightSubstEq.withParameters(Seq((y, z)), (Seq(z), x === z))(`x = y`)
    val `x = z` = have(x === z) by Cut(`y = z`, lastStep)

    have(thesis) by Tautology.from(`x = z`, eqAlign of (x := x, y := z))

  val leibnizProperty = Theorem((x :: A, y :: A, f :: A ->: B) |- (=:=(A) * x * y === One) ==> (=:=(B) * (f * x) * (f * y) === One)):
    assume(x :: A, y :: A, f :: A ->: B, =:=(A) * x * y === One)

    val `x = y` = have(x === y) by Weakening(eqAlign of (x := x, y := y))
    
    have(f * x === f * x) by Restate
    thenHave(x === y |- f * x === f * y) by RightSubstEq.withParameters(Seq((x, y)), (Seq(y), f * x === f * y))
    val `f x = f y` = have(f * x === f * y) by Cut(`x = y`, lastStep)

    val fxType = have(f * x :: B) by Typecheck.prove
    val fyType = have(f * y :: B) by Typecheck.prove

    have((f * x === f * y) <=> (=:=(B) * (f * x) * (f * y) === One) |- =:=(B) * (f * x) * (f * y) === One) by RightSubstEq.withParameters(Seq((f * x === f * y, =:=(B) * (f * x) * (f * y) === One)), (Seq(P), P))(`f x = f y`)
    have((f * x :: B, f * y :: B) |- =:=(B) * (f * x) * (f * y) === One) by Cut(eqAlign of (A := B, x := f * x, y := f * y), lastStep)
    have((f * x :: B) |- =:=(B) * (f * x) * (f * y) === One) by Cut(fyType, lastStep)
    have(=:=(B) * (f * x) * (f * y) === One) by Cut(fxType, lastStep)

  val nonEmptyFuncSpace = Theorem(∃(x, x :: B) |- ∃(x, x :: (A ->: B))):
    val witness = fun(x :: A, b)

    val T1 = variable[Ind]
    val T2 = variable[Ind >>: Ind]
    val e = variable[Ind >>: Ind]

    val typing = have(b :: B |- witness :: (A ->: B)) subproof:
      assume(b :: B)
      have(x :: A ==> b :: B) by Restate
      thenHave(∀(x :: A, b :: B)) by RightForall
      have(witness :: (A ->: B)) by Cut(lastStep, TAbs of (T1 := A, T2 := λ(x, B), e := λ(x, b)))

    thenHave(b :: B |- ∃(x, x :: (A ->: B))) by RightExists
    thenHave(∃(b, b :: B) |- ∃(x, x :: (A ->: B))) by LeftExists

  val nonEmptyCodomain = Theorem((f :: (A ->: B), ∃(x, x :: A)) |- ∃(y, y :: B)):
    val e1, e2, T1 = variable[Ind]
    val T2 = variable[Ind >>: Ind]
    val applicationTyping = have((f :: (A ->: B), x :: A) |- f * x :: B) by
      Weakening(lisa.maths.SetTheory.Types.TypingRules.TApp of (e1 := f, e2 := x, T1 := A, T2 := λ(x, B)))
    val codomainWitness = have((f :: (A ->: B), x :: A) |- ∃(y, y :: B)) by
      RightExists.withParameters(y :: B, y, f * x)(applicationTyping)
    have(thesis) by LeftExists.withParameters(x :: A, x)(codomainWitness)

  val nonEmptyTypeExists = Theorem(∃(A, ∃(x, (x :: A)))):
    have(thesis) by RightExists(boolNonEmpty)

}
