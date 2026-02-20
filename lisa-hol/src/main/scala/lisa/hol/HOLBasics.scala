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
  val !! : TypedConstantFunctional[Ind >>: Ind] = {

    val f = typedvar(A ->: 𝔹)
    val a = typedvar(A)
    val x = typedvar(A)

    val !! = DEF(λ(A, fun(f, f =:= fun(a, One))))

    val typing_of_forall = Theorem(∀(A, nonEmpty(A) ==> !!(A) :: ((A ->: 𝔹) ->: 𝔹))) {
      have(fun(f, f =:= fun(a, One)) :: ((A ->: 𝔹) ->: 𝔹)) by Typecheck.prove
      thenHave(∃(x, x :: A) |- !!(A) :: ((A ->: 𝔹) ->: 𝔹)) by Substitute(!!.definition)
      thenHave(nonEmpty(A) ==> !!(A) :: ((A ->: 𝔹) ->: 𝔹)) by Restate
      thenHave(thesis) by RightForall
    }

    TypedConstantFunctional[Ind >>: Ind]("!!", FunctionalClass(List(None), List(A), ((A ->: 𝔹) ->: 𝔹)), typing_of_forall)
  }
  // define ?
  // define @

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