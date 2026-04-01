
import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Functions.BasicTheorems.{appTyping, funcBetweenEqInFuncSpace}
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
    constructors = Seq(
      ("nil", Seq.empty),
      ("cons", Seq(("head", "A"), ("tail", SelfRef)))
    )
  )
  val nil = list.constructors(0)
  val cons = list.constructors(1)
  
  val nat = API.defineAST(
    name = "nat",
    typeVars = Seq.empty,
    constructors = Seq(
      ("zero", Seq.empty),
      ("succ", Seq(("k", SelfRef)))
    )
  )
  val zero = nat.constructors(0)
  val succ = nat.constructors(1)

  // Minimal recursive template: no additional recursion lemmas, only case equations.
  val length = recFun(list, nat) { self =>
    Case(nil):
      zero
    Case(cons, hd, tl):
      succ * (self * tl)
  }
  
  println(s"length: ${length}")
  println(s"length term: ${length.term}")
  println(s"length(nat): ${length(nat)}")
  println(s"list: ${list}")
  println(s"listNat: ${list(nat())}")

  val listFromLength = recFun(nat, list){ self =>
    Case(zero):
      nil(nat())
    Case(succ, k):
      cons(nat) * zero * (self * k)
      // TODO : automatically infer Nat to cons
  }

  show(length.intro)
  for (cons <- list.constructors) show(length.elim(cons))
  show(listFromLength.intro)
  for (succ <- nat.constructors) show(listFromLength.elim(succ))

  val lengthFromLength = Lemma(
    (x :: nat) |- 
    length(nat) * (listFromLength * x) === x
  ){
    have(thesis) by Induction(x, nat){
      Case(zero) subproof {

        val lenZero = have(listFromLength * zero === nil(nat())) by Restate.from(listFromLength.elim(zero))
        val lenNil = have(length(nat) * nil(nat()) === zero) by Tautology.from(length.elim(nil) of (A := nat()))

        have(length(nat) * (listFromLength * zero) === zero) by Congruence.from(lenZero, lenNil)
        thenHave(thesis) by Restate
      }
      Case(succ, k) subproof {

        assume(k :: nat)

        // Unfold the recursive definition of listFromLength at succ(k).
        val lenSucc = have(listFromLength * (succ * k) === cons(nat()) * zero * (listFromLength * k)) by 
          Restate.from(listFromLength.elim(succ))

        val listFromLengthTyped = have((k :: nat) |- listFromLength * k :: listFromLength.returnType) by
          Tautology.from(
            listFromLength.intro,
            funcBetweenEqInFuncSpace of (f := listFromLength.term, A := nat(), B := listFromLength.returnType),
            appTyping of (f := listFromLength.term, A := nat(), B := listFromLength.returnType, x := k)
          )

        val unfoldLengthOnSucc = have(
          (k :: nat) |- length(nat) * (cons(nat()) * zero * (listFromLength * k)) === succ * (length(nat) * (listFromLength * k))
        ) by Tautology.from(
          zero.intro,
          listFromLengthTyped,
          length.elim(cons) of (A := nat(), hd := zero, tl := listFromLength * k)
        )

        // println(s"Unfolded length(nat) on cons: ${unfoldLengthOnSucc.statement}")
        // println(s"vs ${(length.elim(cons)).statement}")
        // println(s"vs ${(length.elim(cons) of (A := Variable[Ind]("B"))).statement}")
        // println(s"vs ${(length.elim(cons) of (A := nat())).statement}")

        // Chain the recursive equations with the induction hypothesis.
        val rewriteSucc = have(
          (k :: nat) |- length(nat) * (listFromLength * (succ * k)) === succ * (length(nat) * (listFromLength * k))
        ) by Congruence.from(lenSucc, unfoldLengthOnSucc)

        val inductionHypothesis = have(
          (k :: nat, length(nat) * (listFromLength * k) === k) |- length(nat) * (listFromLength * k) === k
        ) by Hypothesis

        have(
          (k :: nat, length(nat) * (listFromLength * k) === k) |- length(nat) * (listFromLength * (succ * k)) === succ * k
        ) by Congruence.from(rewriteSucc, inductionHypothesis)
        thenHave(thesis) by Restate
      }
    }
  }

  show(lengthFromLength)

  
  val unit = API.defineAST(
    name = "one",
    typeVars = Seq.empty,
    constructors = Seq(
      ("star", Seq.empty)
    )
  )
  val star = unit.constructors(0)

  show(unit.induction)
  show(unit.elim)

  // val lengthFromLength2 = Lemma(
  //   (l :: (list * unit)) |- listFromLength * (length(nat) * l) === l
  // ){
  //   have(thesis) by Induction(l, list * unit){
  //     Case(nil) subproof {

  //       have( listFromLength * (length(nat) * nil) === nil ) by Sorry
  //     }
  //     Case(cons, hd, tl) subproof {

  //       have( listFromLength * (length(nat) * (cons * hd * tl)) === cons * hd * tl ) by Sorry
  //     }
  //   }
  // }

}