package lisa.hol
import lisa.maths.SetTheory.Base.Predef.singleton
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.maths.SetTheory.Types.TypingHelpers.TypedConstant
import lisa.maths.SetTheory.Types.TypingHelpers.TypedConstantFunctional
import lisa.maths.SetTheory.Types.TypingHelpers._

import VarsAndFunctions.HOLConstantType
object HOLHelperTheorems extends lisa.Main {
  val f = variable[Ind]
  val x, y, z = variable[Ind]
  val a = variable[Ind]
  val A, B = variable[Ind]
  val any = DEF(λ(x, ⊤))
  val G, H = variable[Ind >>: Ind]

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

  val =:= : TypedConstantFunctional[Ind >>: Ind] = {
    val =:= = Constant[Ind >>: Ind]("=:=").printInfix()
    addSymbol(=:=)
    val typing_of_eq = Axiom(forall(A, =:=(A) :: (A ->: (A ->: 𝔹))))
    TypedConstantFunctional[Ind >>: Ind]("=:=", FunctionalClass(List(None), List(A), (A ->: (A ->: 𝔹))), typing_of_eq)
  }

  val nonEmptyFuncSpace = Axiom(exists(x, x ∈ B) ==> exists(x, x ∈ (A ->: B)))

  val T = variable[Ind]
  val nonEmptyTypeExists = Theorem(exists(T, exists(x, (x ∈ T)))) {
    have(thesis) by RightExists(boolNonEmpty)
  }

}
