import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Functions.BasicTheorems.{appTyping, funcBetweenEqInFuncSpace}
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.utils.fol.FOL

object RecursiveFunction extends lisa.Main {

  // *******************************
  // * ADT Functions and Induction *
  // *******************************

  val x = variable[Ind]
  val f = variable[Ind]
  val n, m = variable[Ind]
  val k = variable[Ind]
  val l = variable[Ind]
  val hd, tl = variable[Ind]
  val A, B = variable[Ind]

  val list = API.defineAST(
    name = "list",
    typeVars = Seq("A"),
    constructors =
      Seq(("nil", Seq.empty), ("cons", Seq(("head", "A"), ("tail", SelfRef))))
  )
  val nil = list.constructors(0)
  val cons = list.constructors(1)

  val nat = API.defineAST(
    name = "nat",
    typeVars = Seq.empty,
    constructors = Seq(("zero", Seq.empty), ("succ", Seq(("k", SelfRef))))
  )
  val zero = nat.constructors(0)
  val succ = nat.constructors(1)

  val unit = API.defineAST(
    name = "unit",
    typeVars = Seq.empty,
    constructors = Seq(("star", Seq.empty))
  )
  val star = unit.constructors(0)

  val list_unit = list(unit)
  val nil_unit = nil(unit)
  val cons_unit = cons(unit)

  println(s"${nil.intro.statement}")
  println(s"${nil_unit.intro.statement}")
  println(s"${cons.intro.statement}")
  println(s"${cons_unit.intro.statement}")
  println(s"${list.term}")
  println(s"${list(unit).term}")

  // Minimal recursive template: no additional recursion lemmas, only case equations.
  val length = recFun(list, nat) { self =>
    Case(nil):
      zero
    Case(cons, hd, tl):
      succ * (self * tl)
  }
  val listFromLength = recFun(nat, list_unit) { self =>
    Case(zero):
      nil_unit
    Case(succ, k):
      nil_unit
      // cons(unit) * star * (self * k)
  }

  show(length.intro)
  for (cons <- list.constructors) show(length.elim(cons))

  // val lengthFromLength = Lemma((x :: nat) |- length(unit) * (listFromLength * x) === x) {
  //   have(thesis) by Induction(x, nat) {
  //     Case(zero) subproof {

  //       val lenZero = have(listFromLength * zero === nil(unit)) by
  //         Tautology.from(listFromLength.elim(zero))
  //       val lenNil = have(length(unit) * nil(unit) === zero) by
  //         Tautology.from(length.elim(nil) of (A := unit))

  //       have(length(unit) * (listFromLength * zero) === zero) by
  //         Congruence.from(lenZero, lenNil)
  //       thenHave(thesis) by Restate
  //     }
  //     Case(succ, k) subproof {
  //       assume(k :: nat)

  //       // Unfold the recursive definition of listFromLength at succ(k).
  //       val lenSucc = have(
  //         listFromLength * (succ * k) === cons(unit) * star * (listFromLength * k)
  //       ) by Restate.from(listFromLength.elim(succ))

  //       // Assert the type of listFromLength * k
  //       val listFromLengthTyped =
  //         have((k :: nat) |- listFromLength * k :: listFromLength.returnType) by
  //           Tautology.from(
  //             listFromLength.intro,
  //             funcBetweenEqInFuncSpace of
  //               (f := listFromLength.term, A := nat, B := listFromLength.returnType),
  //             appTyping of
  //               (
  //                 f := listFromLength.term,
  //                 A := nat,
  //                 B := listFromLength.returnType,
  //                 x := k
  //               )
  //           )

  //       // Now unfold length on cons, using the type above
  //       val zeroInNat = have(zero ∈ nat) by Tautology.from(zero.intro)
  //       val starInUnit = have(star ∈ unit) by Tautology.from(star.intro)
  //       val unfoldLengthOnSucc = have(
  //         length(unit) * (cons(unit) * star * (listFromLength * k)) ===
  //           succ * (length(unit) * (listFromLength * k))
  //       ) by Tautology.from(
  //         listFromLengthTyped,
  //         zeroInNat,
  //         starInUnit,
  //         length.elim(cons) of (A := unit, hd := star, tl := (listFromLength * k))
  //       )

  //       // Chain the recursive equations with the induction hypothesis.
  //       val rewriteSucc = have(
  //         length(unit) * (listFromLength * (succ * k)) ===
  //           succ * (length(unit) * (listFromLength * k))
  //       ) by Congruence.from(lenSucc, unfoldLengthOnSucc)

  //       val inductionHypothesis = have(
  //         (length(unit) * (listFromLength * k) === k) |-
  //           length(unit) * (listFromLength * k) === k
  //       ) by Hypothesis

  //       have(
  //         (length(unit) * (listFromLength * k) === k) |-
  //           length(unit) * (listFromLength * (succ * k)) === succ * k
  //       ) by Congruence.from(rewriteSucc, inductionHypothesis)
  //       thenHave(thesis) by Restate
  //     }
  //   }
  // }

  // show(lengthFromLength)

}
