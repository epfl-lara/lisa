package lisa.hol

import lisa.maths.SetTheory.Base.Pair.given
import lisa.maths.SetTheory.Base.Replacement.|
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.automation.Substitution.{Apply => Substitute}
import lisa.hol.HOLHelperTheorems.*
import lisa.utils.prooflib.BasicStepTactic.RightForall
import lisa.hol.VarsAndFunctions.*

object HOLBasics extends lisa.HOL {

  val A = typevar
  val B = typevar
  val T = typevar

  ////////////////////////////////////////////////////
  // HOL Light preliminaries
  //
  // the section defines the basic HOL Light operators so as to prove the axioms
  // from its library as theorems.

  /**
    * Higher-order embedded universal quantifier.
    */
  val hforall : TypedConstantFunctional[Ind >>: Ind] = {

    val f = typedvar(A ->: 𝔹)
    val a = typedvar(A)
    val x = typedvar(A)

    val hforall = DEF(λ(A, fun(f, f =:= fun(a, One))))

    val typing_of_forall = Theorem(∀(A, nonEmpty(A) ==> hforall(A) :: ((A ->: 𝔹) ->: 𝔹))) {
      have(fun(f, f =:= fun(a, One)) :: ((A ->: 𝔹) ->: 𝔹)) by Typecheck.prove
      thenHave(∃(x, x :: A) |- hforall(A) :: ((A ->: 𝔹) ->: 𝔹)) by Substitute(hforall.definition)
      thenHave(nonEmpty(A) ==> hforall(A) :: ((A ->: 𝔹) ->: 𝔹)) by Restate
      thenHave(thesis) by RightForall
    }

    TypedConstantFunctional[Ind >>: Ind]("hforall", FunctionalClass(List(None), List(A), ((A ->: 𝔹) ->: 𝔹)), typing_of_forall)
  }

  /**
    * Higher-order embedded conjunction.
    * 
    * Defined as in HOL Light:
    * `(/\) = \p q. (\f:bool->bool->bool. f p q) = (\f. f T T)`
    */
  val hand : TypedConstantFunctional[Ind] = {

    val p = typedvar(𝔹)
    val q = typedvar(𝔹)
    val f = typedvar(𝔹 ->: 𝔹 ->: 𝔹)

    val hand = DEF(fun(p, fun(q, fun(f, f * p * q) =:= fun(f, f * One * One))))

    val typing_of_and = Theorem(hand :: (𝔹 ->: 𝔹 ->: 𝔹)) {
      have(fun(p, fun(q, fun(f, f * p * q) =:= fun(f, f * One * One))) :: (𝔹 ->: 𝔹 ->: 𝔹)) by Typecheck.prove
      thenHave(thesis) by Substitute(hand.definition)
    }

    TypedConstantFunctional[Ind]("hand", FunctionalClass(List(), List(), (𝔹 ->: 𝔹 ->: 𝔹)), typing_of_and)
  }

  /**
    * Higher-order embedded implication.
    * 
    * Defined as in HOL Light:
    * `(==>) = \p q. p /\ q <=> p`
    */
  val himp : TypedConstantFunctional[Ind] = {

    val p = typedvar(𝔹)
    val q = typedvar(𝔹)

    val himp = DEF(fun(p, fun(q, (hand * p * q) =:= p)))

    val typing_of_imp = Theorem(himp :: (𝔹 ->: 𝔹 ->: 𝔹)) {
      have(fun(p, fun(q, (hand * p * q) =:= p)) :: (𝔹 ->: 𝔹 ->: 𝔹)) by Typecheck.prove
      thenHave(thesis) by Substitute(himp.definition)
    }

    TypedConstantFunctional[Ind]("himp", FunctionalClass(List(), List(), (𝔹 ->: 𝔹 ->: 𝔹)), typing_of_imp)
  }

  /**
    * Higher-order embedded existential quantifier.
    * 
    * Defined as in HOL Light:
    * `(?) = \P:A->bool. !q. (!x. P x ==> q) ==> q`
    * 
    * This uses the embedded universal quantifier `hforall` and embedded implication `himp`.
    */
  val hexists : TypedConstantFunctional[Ind >>: Ind] = {

    val P = typedvar(A ->: 𝔹)
    val q = typedvar(𝔹)
    val x = typedvar(A)
    val y = typedvar(𝔹)
    val z = variable[Ind]

    val hexists = DEF(λ(A, fun(P, hforall(𝔹) * fun(q, himp * (hforall(A) * fun(x, himp * (P * x) * q)) * q))))

    val typing_of_exists = Theorem(∀(A, nonEmpty(A) ==> hexists(A) :: ((A ->: 𝔹) ->: 𝔹))) {

      val faType = hforall(A) :: ((A ->: 𝔹) ->: 𝔹)
      val fbType = hforall(𝔹) :: ((𝔹 ->: 𝔹) ->: 𝔹)
      val impType = himp :: (𝔹 ->: 𝔹 ->: 𝔹)

      val faStep = have(faType) by Restate.from(hforall.justif of A)
      val fbStep = have(fbType) by Tautology.from(hforall.justif of 𝔹, 𝔹.nonEmptyThm)
      val imStep = have(impType) by Restate.from(himp.justif)

      // have((faType, fbType, impType, exists(q, q :: 𝔹), nonEmpty(A)) |- hforall(𝔹) :: ((𝔹 ->: 𝔹) ->: 𝔹)) by Typecheck.prove
      // have((faType, fbType, impType, exists(q, q :: 𝔹), nonEmpty(A)) |- hforall(A) :: ((A ->: 𝔹) ->: 𝔹)) by Typecheck.prove
      // have((faType, fbType, impType, exists(q, q :: 𝔹), nonEmpty(A)) |- himp :: (𝔹 ->: 𝔹 ->: 𝔹)) by Typecheck.prove
      have((faType, fbType, impType, exists(q, q :: 𝔹), nonEmpty(A)) |- (hforall(A) * fun(x, x =:= x)) :: 𝔹) by Typecheck.prove
      // have((faType, fbType, impType, exists(q, q :: 𝔹), nonEmpty(A)) |- fun(P, hforall(𝔹) * fun(q, himp * (hforall(A) * fun(x, himp * (P * x) * q)) * q)) :: ((A ->: 𝔹) ->: 𝔹)) by Typecheck.prove
      // thenHave((faType, fbType, impType, exists(q, q :: 𝔹), nonEmpty(A)) |- hexists(A) :: ((A ->: 𝔹) ->: 𝔹)) by Substitute(hexists.definition)
      // have(nonEmpty(A) ==> hexists(A) :: ((A ->: 𝔹) ->: 𝔹)) by Tautology.from(lastStep, hforall.justif of A, hforall.justif of 𝔹, himp.justif, 𝔹.nonEmptyThm)
      // thenHave(thesis) by RightForall
    }

    TypedConstantFunctional[Ind >>: Ind]("hexists", FunctionalClass(List(None), List(A), ((A ->: 𝔹) ->: 𝔹)), typing_of_exists)
  }

  // define @
  //

  ////////////////////////////////////////////////////
  // HOL Light axioms
  // ETA_AX, INFINITY_AX, SELECT_AX

  /**
   * ETA_AX 
   * 
   * ```ocaml
   * let ETA_AX = new_axiom
   *   `!t:A->B. (\x. t x) = t`;;
   * ```
   */
  val etaAx = 1

  /**
   * INFINITY_AX
   * 
   * ```ocaml
   * let INFINITY_AX = new_axiom
   *  `?f:ind->ind. ONE_ONE f /\ ~(ONTO f)`;;
   * ```
   */
  val infinityAx = 2

  /**
   * SELECT_AX
   * 
   * ```ocaml
   * let SELECT_AX = new_axiom
   *  `!P (x:A). P x ==> P((@) P)`;;
   * ```
   */
  val selectAx = 3

}