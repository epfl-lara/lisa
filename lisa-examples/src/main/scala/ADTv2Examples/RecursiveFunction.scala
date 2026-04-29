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


  val listU = API.defineAST(
    name = "listU",
    typeVars = Seq("unit"),
    constructors =
      Seq(("nilU", Seq.empty), ("consU", Seq(("head", "unit"), ("tail", SelfRef))))
  )
  val nilU = listU.constructors(0)
  val consU = listU.constructors(1)

  val nil_unit = nil(unit)
  val cons_unit = cons(unit)
  val list_unit = list(unit)
  println(s"nil : ${nil}")
  println(s"nil(unit) : ${nil_unit}")
  println(s"nilU : ${nilU}")
  println(s"nil intro : ${nil.intro}")
  println(s"nilU intro : ${nilU.intro}")
  // println(s"cons : ${cons}")
  // println(s"cons(unit) : ${cons_unit}")
  // println(s"cons intro : ${cons.intro}")
  println(s"unit : ${unit}")
  println(s"list : ${list}")
  println(s"list(unit) : ${list_unit}")
  println(s"listU : ${listU}")


  // Typing lemmas

  val nilU_typing = Lemma(nilU :: listU) {
    have(thesis) by Typecheck.prove
  }

  val nil_typing = Lemma(nil_unit :: list_unit) {
    have(thesis) by Sorry
  }
  val nil_base = Lemma(nil() :: list) {
    have(thesis) by Typecheck.prove
  }
  

  // Minimal recursive template: no additional recursion lemmas, only case equations.
  // val length = recFun2(list, nat) { self =>
  //   Case(nil):
  //     zero
  //   Case(cons, hd, tl):
  //     succ * (self * tl)
  // }

  val listFromLength = recFun2(nat, list_unit) { self =>
    Case(zero):
      nil_unit
    Case(succ, k):
      nil_unit
      // cons(unit) * star * (self * k)
  }

  /* ERROR LOGS : 
  [info] nil : list/nil
  [info] nil(unit) : list/nil[oneTerm]
  [info] nil intro :  ⊢ ∀(A, list/nil[A] ∈ listTerm)
  [info] list : list[A]
  [info] list(unit) : listTerm[oneTerm]
  [info] In listFromLength, case nat/zero:
  [info]    assumptions: Set(listFromLengthRecSelf ∈ natTerm ->: listTerm[oneTerm], nat/zero ∈ natTerm)
  [info]    goal: list/nil[oneTerm] ∈ listTerm[oneTerm]
  [info]    intro:  ⊢ nat/zero ∈ natTerm
  [info] listFromLengthRecSelf ∈ natTerm ->: listTerm[oneTerm] ⊢ list/nil[oneTerm] ∈ listTerm[oneTerm]
  [info]
  [info]     val stmt = have(innerProof)
  [info]    Proof tactic Typecheck used in (Tactics.scala:62) did not succeed:
  [info]    Failed to construct the equivalence proof for universeOf(list/nil[oneTerm]) and listTerm[oneTerm]
  [info] [Error] lisa.utils.prooflib.ProofTacticLib$UnapplicableProofTactic: Failed to construct the equivalence proof for universeOf(list/nil[oneTerm]) and listTerm[oneTerm]
  [info] 	at lisa.maths.SetTheory.Types.Tactics$Typecheck$.checkProof(Tactics.scala:218)
  [info] 	at lisa.maths.SetTheory.Types.Tactics$Typecheck$.prove(Tactics.scala:61)
  [info] 	at lisa.maths.SetTheory.Types.ADTv2.recursion.Witness.$anonfun$2(Witness.scala:207)
  [info]
  [error] Nonzero exit code returned from runner: 1
  */

  // show(length.intro)
  // for (cons <- list.constructors) show(length.elim(cons))
  show(listFromLength.intro)
  for (succ <- nat.constructors) show(listFromLength.elim(succ))

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
