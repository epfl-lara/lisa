package lisa.hol.basics

import lisa.automation.Substitution.{Apply => Substitute}
import lisa.hol.HOLHelperTheorems._
import lisa.hol.HOLSteps._
import lisa.hol.VarsAndFunctions._
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.maths.SetTheory.Types.TypingRules.BetaReduction
import lisa.maths.SetTheory.Types.TypingRules.TAbs
import lisa.utils.prooflib.BasicStepTactic._
import lisa.utils.prooflib.Library
import lisa.utils.prooflib.ProofTacticLib._
import lisa.utils.prooflib.SimpleDeducedSteps._

/**
 * HOL Light choice operator (select / epsilon).
 *
 * Defines:
 *  - selectProp (private helper)
 *  - selectTerm (private helper)
 *  - selectWellDefined (helper theorem)
 *  - hselect (polymorphic constant)
 */
object Select extends lisa.HOL {

  val A = typevar

  val x = typedvar(A)
  val y = typedvar(A)
  val P = typedvar(A ->: 𝔹)

  val lib = summon[Library]

  // defining select

  private[hol] def selectProp(x: Expr[Ind]) = (x :: A) /\ (∃(y, (y :: A) /\ (P * y === One)) ==> (P * x === One))
  private[hol] val selectTerm = ε(x, selectProp(x))

  private[hol] val selectWellDefined = HOLTheorem(selectProp(selectTerm)):
    assumeAll

    val existsCase = have(∃(y, (y :: A) /\ (P * y === One)) |- selectProp(selectTerm)) subproof:
      lib.have((y :: A) /\ (P * y === One) |- selectProp(y)) by Restate
      thenHave((y :: A) /\ (P * y === One) |- selectProp(selectTerm)) by RightEpsilon.withParameters(selectProp(y), y, y)
      thenHave(∃(y, (y :: A) /\ (P * y === One)) |- selectProp(selectTerm)) by LeftExists

    val emptyCase = have((nonEmpty(A), ! ∃(y, (y :: A) /\ (P * y === One))) |- selectProp(selectTerm)) subproof:
      assume(nonEmpty(A), ! ∃(y, (y :: A) /\ (P * y === One)))
      have((y :: A) |- selectProp(y)) by Restate
      thenHave((y :: A) |- selectProp(selectTerm)) by RightEpsilon.withParameters(selectProp(y), y, y)
      thenHave(∃(y, y :: A) |- selectProp(selectTerm)) by LeftExists

    have(thesis) by Tautology.from(existsCase, emptyCase)

  /**
   * Higher-order embedded choice operator.
   *
   * Deferred to epsilon terms internally
   */
  val hselect: HOLPolymorphicConstant[Ind >>: Ind] = {
    val P = typedvar(A ->: 𝔹)
    val x = typedvar(A)
    val y = typedvar(A)

    val hselect = DEF(
      λ(
        A,
        fun(
          P,
          ε(
            x,
            // the result is always in A
            (x :: A) /\
              // but if there is a witness, then the result satisfies P as well
              (∃(y, (y :: A) /\ (P * y === One)) ==> (P * x === One))
          )
        )
      )
    )

    val typing_of_select = Theorem(∀(A, nonEmpty(A) ==> hselect(A) :: ((A ->: 𝔹) ->: A))):
      lib.have((nonEmpty(A), (P :: (A ->: 𝔹))) |- selectProp(selectTerm)) by Weakening(selectWellDefined)
      thenHave(nonEmpty(A) |- (P :: (A ->: 𝔹)) ==> (selectTerm :: A)) by Weakening
      val epsType = thenHave(nonEmpty(A) |- ∀(P :: (A ->: 𝔹), selectTerm :: A)) by RightForall

      val T1 = variable[Ind]
      val T2 = variable[Ind >>: Ind]
      val e = variable[Ind >>: Ind]

      lib.have(nonEmpty(A) |- fun(P, selectTerm) :: ((A ->: 𝔹) ->: A)) by Cut(epsType, TAbs of (T1 := (A ->: 𝔹), T2 := λ(x, A), e := λ(P, selectTerm)))
      thenHave(nonEmpty(A) |- hselect(A) :: ((A ->: 𝔹) ->: A)) by Substitute(hselect.definition)
      thenHave(nonEmpty(A) ==> hselect(A) :: ((A ->: 𝔹) ->: A)) by Restate
      thenHave(thesis) by RightForall

    HOLPolymorphicConstant[Ind >>: Ind](hselect.id, FunctionalClass(List(None), List(A), ((A ->: 𝔹) ->: A)), typing_of_select)
  }

}
