package ADTv2Examples.proofs

import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Types.ADTv2.library.*
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.{a, b, f, x}
import lisa.maths.SetTheory.Types.TypingTheorems.arrowElim

object SimpleInduction extends lisa.Main {

  val n = variable[Ind]
  val prev = variable[Ind]
  val b = variable[Ind]
  val l = variable[Ind]

  section("Induction on Bool")

  val negNegIsId = Theorem((b :: bool) |- not * (not * b) === b) {
    val negFalse = have(not * fals === tru) by Restate.from(not.elim(fals))
    val negTrue = have(not * tru === fals) by Restate.from(not.elim(tru))

    have(thesis) by Induction() {
      Case(tru) subproof {
        have(not * (not * tru) === tru) by Congruence.from(negTrue, negFalse)
      }
      Case(fals) subproof {
        have(not * (not * fals) === fals) by Congruence.from(negTrue, negFalse)
      }
    }
  }

  section("Induction on Nat")

  val natReflexive = Theorem((n :: nat) |- n === n) {
    have(thesis) by Induction() {
      Case(zero) subproof {
        have(thesis) by RightRefl
      }
      Case(succ, prev) subproof {
        have(thesis) by RightRefl
      }
    }
  }

  val doubleIsNat = Theorem((n :: nat) |- double * n :: nat) {
    have(thesis) by Induction() {
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
          arrowElim of (f := succ, a := nat.term, b := nat.term, x := succ * (double * natDoubleN)),
          arrowElim of (f := succ, a := nat.term, b := nat.term, x := double * natDoubleN)
        )
        have(thesis) by Congruence.from(st1, st2)
      }
    }
  }

  section("Induction on a parametric ADT, inferred from the goal")

  // Unlike the cases above, the ADT here carries a type argument. `Induction()` still
  // takes no arguments: it reads `l` and `list(nat)` straight off the goal. That works
  // because the ADT is recovered from the term -- the `list` symbol applied to the `nat`
  // symbol -- rather than being rebuilt from the declared name "list".
  val lengthIsNat = Theorem((l :: list(nat)) |- length(nat) * l :: nat) {
    have(thesis) by Induction() {
      Case(nil) subproof {
        have(thesis) by Congruence.from((length.elim(nil) of nat), zero.intro)
      }
      Case(cons, listLengthHead, listLengthTail) subproof {

        assume(length(nat) * listLengthTail :: nat)

        val st1 = have(
          (listLengthHead :: nat, listLengthTail :: list(nat)) |-
            length(nat) * (cons(nat) * listLengthHead * listLengthTail) === succ * (length(nat) * listLengthTail)
        ) by Tautology.from((length.elim(cons) of nat))
        val st2 = have(succ * (length(nat) * listLengthTail) :: nat) by Tautology.from(
          succ.intro,
          arrowElim of (f := succ, a := nat.term, b := nat.term, x := length(nat) * listLengthTail)
        )
        have(thesis) by Congruence.from(st1, st2)
      }
    }
  }
}
