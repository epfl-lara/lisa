package ADTv2Examples.proofs

import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Types.ADTv2.library.Bool.*
import lisa.maths.SetTheory.Types.ADTv2.library.List.*
import lisa.maths.SetTheory.Types.ADTv2.library.Nat.*
import ADTv2Examples.functions.NestedPatterns.{countTrue, existsTrue}

object NestedPatternInduction extends lisa.Main {

  private var l = variable[Ind]
  private val hd = variable[Ind]
  private val tl = variable[Ind]
  private val boolList = list.specialize(bool)



  section("Proof example: non-existence of a true in a list implies zero count")

  
  val nonExistsImpliesZeroCount = Lemma(
    l :: list.termAt(Seq(bool.term)) |- (existsTrue(bool) * l === fals) ==> (countTrue(bool) * l === zero)
  ){
    have(thesis) by Induction(l, boolList) {

      Case(nil) subproof {
        // existsTrue[list/nil[bool/term1]] = bool/fals ⇒ countTrue[list/nil[bool/term1]] = nat/zero

        have(thesis) by Tautology.from(countTrue.elim(bool)(nil))
      }
      Case(cons, tru, tl) subproof {
        // ( cons/arg0 ∈ bool/term1, tl ∈ list/term2[bool/term1], existsTrue[tl] = bool/fals ⇒ countTrue[tl] = nat/zero, cons/arg0 = bool/tru )
        // ⊢ existsTrue[list/cons[bool/term1](cons/arg0)(tl)] = bool/fals ⇒ countTrue[list/cons[bool/term1](cons/arg0)(tl)] = nat/zero

        val arg0 = Variable[Ind]("cons/arg0")
        val listAtArg0 = cons(bool) * arg0 * tl
        assume(
          arg0 :: bool.term,
          tl :: list.termAt(Seq(bool.term)),
          (existsTrue(bool) * tl === fals) ==> (countTrue(bool) * tl === zero),
          arg0 === tru
        )

        val existsAtTru = have(existsTrue(bool) * listAtArg0 === tru) by
          Tautology.from(existsTrue.elim(bool)(Case(cons, tru, tl)))

        have(thesis) subproof {
          assume(existsTrue(bool) * listAtArg0 === fals)
          val truEqFals = have(tru === fals) by Congruence.from(lastStep, existsAtTru)
          have(countTrue(bool) * listAtArg0 === zero) by Tautology.from(
            truEqFals,
            bool.injectivity(tru, fals)
          )
          thenHave(thesis) by RightImplies.withParameters(
            existsTrue(bool) * listAtArg0 === fals,
            countTrue(bool) * listAtArg0 === zero
          )
        }
      }
      Case(cons, fals, tl) subproof {
        // ( cons/arg0 ∈ bool/term1, tl ∈ list/term2[bool/term1], existsTrue[tl] = bool/fals ⇒ countTrue[tl] = nat/zero, cons/arg0 = bool/fals )
        // ⊢ existsTrue[list/cons[bool/term1](cons/arg0)(tl)] = bool/fals ⇒ countTrue[list/cons[bool/term1](cons/arg0)(tl)] = nat/zero

        val arg0 = Variable[Ind]("cons/arg0")
        val listAtArg0 = cons(bool) * arg0 * tl
        assume(
          arg0 :: bool.term,
          tl :: list.termAt(Seq(bool.term)),
          (existsTrue(bool) * tl === fals) ==> (countTrue(bool) * tl === zero),
          arg0 === fals
        )

        val existsAtFals = have(existsTrue(bool) * listAtArg0 === existsTrue(bool) * tl) by
          Tautology.from(existsTrue.elim(bool)(Case(cons, fals, tl)))
        val countAtFals = have(countTrue(bool) * listAtArg0 === countTrue(bool) * tl) by
          Tautology.from(countTrue.elim(bool)(Case(cons, fals, tl)))

        have(thesis) subproof {
          assume(existsTrue(bool) * listAtArg0 === fals)
          val noTrueTail = have(existsTrue(bool) * tl === fals) by Congruence.from(lastStep, existsAtFals)
          val zeroTail = have(countTrue(bool) * tl === zero) by Tautology.from(noTrueTail)
          have(countTrue(bool) * listAtArg0 === zero) by Congruence.from(countAtFals, zeroTail)
          thenHave(thesis) by RightImplies.withParameters(
            existsTrue(bool) * listAtArg0 === fals,
            countTrue(bool) * listAtArg0 === zero
          )
        }
      }
    }
  }
  
  val nonExistsImpliesZeroCount2 = Lemma(
    l :: list.termAt(Seq(bool.term)) |- (existsTrue(bool) * l === fals) ==> (countTrue(bool) * l === zero)
  ){
    have(thesis) by Induction(l, boolList) {

      Case(nil) subproof {
        // existsTrue[list/nil[bool/term1]] = bool/fals ⇒ countTrue[list/nil[bool/term1]] = nat/zero

        have(thesis) by Tautology.from(countTrue.elim(bool)(nil))
      }
      Case(cons, tru, tl) subproof {
        // ( cons/arg0 ∈ bool/term1, tl ∈ list/term2[bool/term1], existsTrue[tl] = bool/fals ⇒ countTrue[tl] = nat/zero, cons/arg0 = bool/tru ) 
        // ⊢ existsTrue[list/cons[bool/term1](cons/arg0)(tl)] = bool/fals ⇒ countTrue[list/cons[bool/term1](cons/arg0)(tl)] = nat/zero

        val arg0 = Variable[Ind]("cons/arg0")
        val listAtArg0 = cons(bool) * arg0 * tl
        assume(
          arg0 :: bool.term,
          tl :: list.termAt(Seq(bool.term)),
          (existsTrue(bool) * tl === fals) ==> (countTrue(bool) * tl === zero),
          arg0 === tru
        )

        val existsAtTru = have(existsTrue(bool) * listAtArg0 === tru) by
          Tautology.from(existsTrue.elim(bool)(Case(cons, tru, tl)))

        have(thesis) subproof {
          assume(existsTrue(bool) * listAtArg0 === fals)
          val truEqFals = have(tru === fals) by Congruence.from(lastStep, existsAtTru)
          have(countTrue(bool) * listAtArg0 === zero) by Tautology.from(
            truEqFals,
            bool.injectivity(tru, fals)
          )
          thenHave(thesis) by RightImplies.withParameters(
            existsTrue(bool) * listAtArg0 === fals,
            countTrue(bool) * listAtArg0 === zero
          )
        }
      }
      Case(cons, fals, tl) subproof {
        // ( cons/arg0 ∈ bool/term1, tl ∈ list/term2[bool/term1], existsTrue[tl] = bool/fals ⇒ countTrue[tl] = nat/zero, cons/arg0 = bool/fals ) 
        // ⊢ existsTrue[list/cons[bool/term1](cons/arg0)(tl)] = bool/fals ⇒ countTrue[list/cons[bool/term1](cons/arg0)(tl)] = nat/zero

        val arg0 = Variable[Ind]("cons/arg0")
        val listAtArg0 = cons(bool) * arg0 * tl
        assume(
          arg0 :: bool.term,
          tl :: list.termAt(Seq(bool.term)),
          (existsTrue(bool) * tl === fals) ==> (countTrue(bool) * tl === zero),
          arg0 === fals
        )

        val existsAtFals = have(existsTrue(bool) * listAtArg0 === existsTrue(bool) * tl) by
          Tautology.from(existsTrue.elim(bool)(Case(cons, fals, tl)))
        val countAtFals = have(countTrue(bool) * listAtArg0 === countTrue(bool) * tl) by
          Tautology.from(countTrue.elim(bool)(Case(cons, fals, tl)))

        have(thesis) subproof {
          assume(existsTrue(bool) * listAtArg0 === fals)
          val noTrueTail = have(existsTrue(bool) * tl === fals) by Congruence.from(lastStep, existsAtFals)
          val zeroTail = have(countTrue(bool) * tl === zero) by Tautology.from(noTrueTail)
          have(countTrue(bool) * listAtArg0 === zero) by Congruence.from(countAtFals, zeroTail)
          thenHave(thesis) by RightImplies.withParameters(
            existsTrue(bool) * listAtArg0 === fals,
            countTrue(bool) * listAtArg0 === zero
          )
        }
      }
    }
  }
  
}
