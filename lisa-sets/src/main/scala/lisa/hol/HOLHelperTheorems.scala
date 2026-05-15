package lisa.hol
import lisa.maths.SetTheory.Base.Predef.singleton
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.maths.SetTheory.Types.TypingHelpers.TypedConstant
import lisa.maths.SetTheory.Types.TypingHelpers.TypedConstantFunctional
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.maths.SetTheory.Types.TypingRules.{TAbs, BetaReduction}
import lisa.maths.SetTheory.Base.Predef.*

import lisa.automation.Substitution.{Apply => Substitute}

import VarsAndFunctions.HOLConstantType
import lisa.utils.prooflib.BasicStepTactic.LeftOr
import lisa.utils.prooflib.BasicStepTactic.RightAnd
import lisa.utils.KernelHelpers.lambda
import lisa.utils.prooflib.BasicStepTactic.RightSubstEq
import lisa.utils.prooflib.BasicStepTactic.Weakening
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.BasicStepTactic.RightSubstEq
import lisa.utils.prooflib.BasicStepTactic.RightSubstEq
import lisa.utils.unification.UnificationUtils.Substitution
import lisa.utils.prooflib.BasicStepTactic.RightSubstEq
import lisa.utils.prooflib.BasicStepTactic.LeftExists
import lisa.kernel.proof.SequentCalculus.RightSubstIff

object HOLHelperTheorems extends lisa.Main {
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
  private val lib = summon[lisa.utils.prooflib.Library]

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
  val 𝔹 = HOLConstantType("𝔹", boolNonEmpty)

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
      val zEq = have(x === Zero |- x :: 𝔹) by RightSubstEq.withParameters(Seq((x, Zero)), (Seq(x), x :: 𝔹))(Zero.justif)
      val oEq = have(x === One |- x :: 𝔹) by RightSubstEq.withParameters(Seq((x, One)), (Seq(x), x :: 𝔹))(One.justif)
      lib.have(thesis) by Tautology.from(zEq, oEq)

    have(thesis) by RightAnd(fwd, bwd)

  val boolZeroXorOne = Theorem(x :: 𝔹 |- (x === Zero) <=> !(x === One)):
    assume(x :: 𝔹)
    val cases = have((x === Zero) \/ (x === One)) by Tautology.from(boolBivalence of (x := x))
    val zeroCase = have(x === Zero |- (x === Zero) <=> !(x === One)) subproof:
      have(x === Zero |- (x === Zero) <=> !(Zero === One)) by Tautology.from(`0 != 1`)
      thenHave(x === Zero |- (x === Zero) <=> !(x === One)) by RightSubstEq.withParameters(Seq((x, Zero)), (Seq(b), (x === Zero) <=> !(b === One)))

    val oneCase = have(x === One |- (x === Zero) <=> !(x === One)) subproof:
      have(x === One |- (One === Zero) <=> !(One === One)) by Tautology.from(`0 != 1`)
      thenHave(x === One |- (x === Zero) <=> !(x === One)) by RightSubstEq.withParameters(Seq((x, One)), (Seq(b), (b === Zero) <=> !(b === One)))

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
    have(thesis) by LeftOr(eqCase, neqCase)

  private val eqBetaRed = Theorem((x :: A, y :: A) |- fun(x :: A, fun(y :: A, eqTerm)) * x * y === eqTerm):
    assume(x :: A, y :: A)

    val e = variable[Ind >>: Ind]
    val e2 = variable[Ind]
    val T = variable[Ind]

    val beta1 = lib.have(fun(y :: A, eqTerm) * y === eqTerm) by Weakening(BetaReduction of (T := A, e2 := y, e := λ(y, eqTerm))) 
    val beta2 = lib.have(fun(x :: A, fun(y :: A, eqTerm)) * x === fun(y :: A, eqTerm)) by Weakening(BetaReduction of (T := A, e2 := x, e := λ(x, fun(y :: A, eqTerm)))) 
    
    lib.have(fun(x :: A, fun(y :: A, eqTerm)) * x * y === fun(x :: A, fun(y :: A, eqTerm)) * x * y) by Restate
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
      lib.have(fun(x :: A, theEp) :: (A ->: 𝔹)) by Cut(lastStep, TAbs of (T1 := A, T2 := λ(x, 𝔹), e := λ(x, theEp)))
      thenHave(y :: A ==> fun(x :: A, theEp) :: (A ->: 𝔹)) by Weakening
      thenHave(∀(y :: A, fun(x :: A, theEp) :: (A ->: 𝔹))) by RightForall
      lib.have(fun(x :: A, fun(y :: A, theEp)) :: (A ->: (A ->: 𝔹))) by Cut(lastStep, TAbs of (T1 := A, T2 := λ(x, A ->: 𝔹), e := λ(y, fun(x :: A, theEp))))

      // use this to conclude 
      thenHave(epType |- =:=(A) :: (A ->: (A ->: 𝔹))) by Substitute(=:=.definition)
      lib.have(=:=(A) :: (A ->: (A ->: 𝔹))) by Cut(epProof, lastStep)
      thenHave(thesis) by RightForall
    
    TypedConstantFunctional[Ind >>: Ind]("=:=", FunctionalClass(List(None), List(A), (A ->: (A ->: 𝔹))), typing_of_eq)
  }

  val eqRefl = Theorem((x :: A |- (=:=(A) * x * x) === One)):
    assume(x :: A)
    val theEp = ε(b, (b :: 𝔹) /\ ((b === One) <=> (x === x)))
    lib.have((One :: 𝔹) /\ ((One === One) <=> (x === x))) by Tautology.from(One.justif)
    thenHave((theEp :: 𝔹) /\ ((theEp === One) <=> (x === x))) by RightEpsilon.withParameters((b :: 𝔹) /\ ((b === One) <=> (x === x)), b, One)
    val appliedEqOne = thenHave(theEp === One) by Weakening

    have(fun(x :: A, fun(y :: A, eqTerm)) * x * x === theEp) by Weakening(eqBetaRed of (y := x))

    thenHave(fun(x :: A, fun(y :: A, eqTerm)) * x * x === One) by Substitute(appliedEqOne)
    thenHave(thesis) by Substitute(=:=.definition)

  val eqAlign = Theorem((x :: A, y :: A) |- (x === y) <=> (=:=(A) * x * y === One)):
    assume(x :: A, y :: A)
    val fwd = lib.have(x === y ==> (=:=(A) * x * y === One)) subproof:
      lib.have(=:=(A) * x * x === One) by Weakening(eqRefl)
      thenHave(x === y |- =:=(A) * x * y === One) by RightSubstEq.withParameters(Seq((x, y)), (Seq(y), =:=(A) * x * y === One))

    val bwd = lib.have((=:=(A) * x * y === One) ==> (x === y)) subproof:
      have((eqTerm === One) ==> (x === y)) by Weakening(eqTermProperty)
      thenHave(fun(x :: A, fun(y :: A, eqTerm)) * x * y === One ==> (x === y)) by Substitute(eqBetaRed)
      thenHave(thesis) by Substitute(=:=.definition)

    have(thesis) by RightAnd(fwd, bwd)

  val eqAlignZero = Theorem((x :: A, y :: A) |- (!(x === y)) <=> (=:=(A) * x * y === Zero)):
    assume(x :: A, y :: A)

    val `x = y` = =:=(A) * x * y

    val typ = lib.have(`x = y` :: 𝔹) by Typecheck.prove
    val conv = lib.have((!(x === y)) <=> (!(`x = y` === One))) by Weakening(eqAlign)
    val bivalence = lib.have((`x = y` === One) \/ (`x = y` === Zero)) by Tautology.from(boolBivalence of (x := `x = y`), typ)

    val fwd = lib.have((!(x === y)) ==> (`x = y` === Zero)) by Tautology.from(conv, bivalence)

    val bwd = lib.have((`x = y` === Zero) ==> (!(x === y))) subproof:
      assume(`x = y` === Zero)
      lib.have(!(Zero === One)) by Weakening(`0 != 1`)
      thenHave(!(`x = y` === One)) by RightSubstEq.withParameters(Seq((Zero, `x = y`)), (Seq(x), !(x === One)))
      lib.have(thesis) by Tautology.from(conv, lastStep)

    lib.have(thesis) by RightAnd(fwd, bwd)

  val eqSymEq = Theorem((x :: A, y :: A) |- =:=(A) * x * y === =:=(A) * y * x):
    assume(x :: A, y :: A)

    val eqCase = have(x === y |- =:=(A) * x * y === =:=(A) * y * x) subproof:
      assume(x === y)
      val xyOne = have(=:=(A) * x * y === One) by Weakening(eqAlign)
      val yxOne = have(=:=(A) * y * x === One) by Weakening(eqAlign of (x := y, y := x))

      lib.have(One === One) by Restate
      thenHave(thesis) by Substitute(xyOne, yxOne)

    val neqCase = have(!(x === y) |- =:=(A) * x * y === =:=(A) * y * x) subproof:
      assume(!(x === y))
      val xyZero = have(=:=(A) * x * y === Zero) by Weakening(eqAlignZero)
      val yxZero = have(=:=(A) * y * x === Zero) by Weakening(eqAlignZero of (x := y, y := x))

      lib.have(Zero === Zero) by Restate
      thenHave(thesis) by Substitute(xyZero, yxZero)

    lib.have(thesis) by LeftOr(eqCase, neqCase)

  val eqSym = Theorem((x :: A, y :: A, =:=(A) * x * y === One) |- (=:=(A) * y * x === One)):
    assumeAll

    lib.have(=:=(A) * x * y === One) by Restate
    thenHave(thesis) by Substitute(eqSymEq)
  
  val eqTrans = Theorem((x :: A, y :: A, z :: A, =:=(A) * x * y === One, =:=(A) * y * z === One) |- =:=(A) * x * z === One):
    assume(x :: A, y :: A, z :: A, =:=(A) * x * y === One, =:=(A) * y * z === One)

    val `x = y` = lib.have(x === y) by Weakening(eqAlign of (x := x, y := y))
    val `y = z` = lib.have(y === z) by Weakening(eqAlign of (x := y, y := z))

    lib.have(y === z |- x === z) by RightSubstEq.withParameters(Seq((y, z)), (Seq(z), x === z))(`x = y`)
    val `x = z` = lib.have(x === z) by Cut(`y = z`, lastStep)

    lib.have(thesis) by Tautology.from(`x = z`, eqAlign of (x := x, y := z))

  val leibnizProperty = Theorem((x :: A, y :: A, f :: A ->: B) |- (=:=(A) * x * y === One) ==> (=:=(B) * (f * x) * (f * y) === One)):
    assume(x :: A, y :: A, f :: A ->: B, =:=(A) * x * y === One)

    val `x = y` = lib.have(x === y) by Weakening(eqAlign of (x := x, y := y))
    
    lib.have(f * x === f * x) by Restate
    thenHave(x === y |- f * x === f * y) by RightSubstEq.withParameters(Seq((x, y)), (Seq(y), f * x === f * y))
    val `f x = f y` = lib.have(f * x === f * y) by Cut(`x = y`, lastStep)

    val fxType = lib.have(f * x :: B) by Typecheck.prove
    val fyType = lib.have(f * y :: B) by Typecheck.prove

    have((f * x === f * y) <=> (=:=(B) * (f * x) * (f * y) === One) |- =:=(B) * (f * x) * (f * y) === One) by RightSubstEq.withParameters(Seq((f * x === f * y, =:=(B) * (f * x) * (f * y) === One)), (Seq(P), P))(`f x = f y`)
    lib.have((f * x :: B, f * y :: B) |- =:=(B) * (f * x) * (f * y) === One) by Cut(eqAlign of (A := B, x := f * x, y := f * y), lastStep)
    lib.have((f * x :: B) |- =:=(B) * (f * x) * (f * y) === One) by Cut(fyType, lastStep)
    lib.have(=:=(B) * (f * x) * (f * y) === One) by Cut(fxType, lastStep)

  val nonEmptyFuncSpace = Theorem(∃(x, x :: B) |- ∃(x, x :: (A ->: B))):
    val witness = fun(x :: A, b)

    val T1 = variable[Ind]
    val T2 = variable[Ind >>: Ind]
    val e = variable[Ind >>: Ind]

    val typing = lib.have(b :: B |- witness :: (A ->: B)) subproof:
      assume(b :: B)
      lib.have(x :: A ==> b :: B) by Restate
      thenHave(∀(x :: A, b :: B)) by RightForall
      have(witness :: (A ->: B)) by Cut(lastStep, TAbs of (T1 := A, T2 := λ(x, B), e := λ(x, b)))

    thenHave(b :: B |- ∃(x, x :: (A ->: B))) by RightExists
    thenHave(∃(b, b :: B) |- ∃(x, x :: (A ->: B))) by LeftExists

  val nonEmptyTypeExists = Theorem(∃(A, ∃(x, (x :: A)))):
    have(thesis) by RightExists(boolNonEmpty)

}
