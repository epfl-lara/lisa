package lisa.maths

import lisa.automation.MathlibTactics.{ByCases, ByContra, Rw, Simp, SolveByElim}
import lisa.utils.fol.FOL.{*, given}

/**
 * Regression tests for mathlib-inspired tactics in `lisa.automation.MathlibTactics`.
 *
 * These are checked by running `RunAllTheorems` (module initialization runs theorems).
 */
object MathlibTacticTests extends lisa.Main {

  val p = variable[Prop]
  val q = variable[Prop]
  val r = variable[Prop]

  val x = variable[Ind]
  val y = variable[Ind]
  val P = variable[Ind >>: Prop]
  val Q = variable[Ind >>: Prop]
  val R0 = variable[Ind >>: Prop]

  val simp_and_left = Theorem((p /\ q) |- p) {
    have(thesis) by Simp
  }

  val by_contra_double_neg = Theorem((!(!p)) |- p) {
    assume(!(!p))

    val contra = have(!p |- ()) subproof {
      assume(!p)
      have(thesis) by Simp
    }

    have(thesis) by ByContra(p)(contra)
  }

  val by_cases_example = Theorem(((p ==> r), (!p ==> r)) |- r) {
    val pr = assume(p ==> r)
    val npr = assume(!p ==> r)

    val caseP = have(p |- r) subproof {
      val hp = have(p |- p) by Hypothesis
      have(thesis) by Simp.from(pr, hp)
    }

    val caseNotP = have(!p |- r) subproof {
      val hnp = have(!p |- !p) by Hypothesis
      have(thesis) by Simp.from(npr, hnp)
    }

    have(thesis) by ByCases(p)(caseP, caseNotP)
  }

  val rw_rewrite_term = Theorem((x === y, P(x)) |- P(y)) {
    val eq = assume(x === y)
    assume(P(x))

    have(P(x)) by Hypothesis
    thenHave(P(y)) by Rw(eq)
    have(thesis) by Rewrite(lastStep)
  }

  val simp_forall_instantiation = Theorem(∀(λ(x, P(x))) |- P(y)) {
    have(thesis) by Simp
  }

  val solve_by_elim_imp_chain = Theorem((P(y), ∀(λ(x, P(x) ==> Q(x))), ∀(λ(x, Q(x) ==> R0(x)))) |- R0(y)) {
    have(thesis) by SolveByElim
  }

  val solve_by_elim_two_premises = Theorem((P(y), Q(y), ∀(λ(x, P(x) ==> (Q(x) ==> R0(x))))) |- R0(y)) {
    have(thesis) by SolveByElim
  }
}
