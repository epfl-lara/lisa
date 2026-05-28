package ADTv2Examples.proofs

import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Types.ADTv2.library.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.funEqDef
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.{a, b, f, x}

object InductionOnNat extends lisa.Main {

  val n = variable[Ind]
  val prev = variable[Ind]
  val natDoubleN = variable[Ind]

  val natReflexive = Theorem((n :: nat) |- n === n) {
    have(thesis) by Induction(n, nat) {
      Case(zero) subproof {
        have(thesis) by RightRefl
      }
      Case(succ, prev) subproof {
        have(thesis) by RightRefl
      }
    }
  }

  val doubleIsNat = Theorem((n :: nat) |- double * n :: nat) {
    have(thesis) by Induction(n, nat) {
      Case(zero) subproof {
        have(thesis) by Congruence.from(
          double.elim(zero), 
          zero.intro
        )
      }
      Case(succ, natDoubleN) subproof {

        assume(double * natDoubleN :: nat)

        val st1 = have(natDoubleN :: nat |- double * (succ * natDoubleN) === succ * (succ * (double * natDoubleN))) by
          Tautology.from(double.elim(succ))
        val st2 = have(succ * (succ * (double * natDoubleN)) :: nat) by Tautology.from(
          succ.intro,
          funEqDef of (f := succ, a := nat.term, b := nat.term, x := succ * (double * natDoubleN)),
          funEqDef of (f := succ, a := nat.term, b := nat.term, x := double * natDoubleN)
        )
        have(thesis) by Congruence.from(st1,st2)
      }
    }
  }

}
