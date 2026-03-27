
import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Types.TypingHelpers.{*}

object RecursiveFunction extends lisa.Main {

  // *******************************
  // * ADT Functions and Induction *
  // *******************************

  val x = variable[Ind]
  val n, m = variable[Ind]
  val k = variable[Ind]
  val hd, tl = variable[Ind]

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

  val listFromLength = recFun(nat, list){ self =>
    Case(zero):
      nil
    Case(succ, k):
      cons * zero * (self * k)
  }

  show(length.intro)
  for (cons <- list.constructors) show(length.elim(cons))
  show(listFromLength.intro)
  for (succ <- nat.constructors) show(listFromLength.elim(succ))

  val lengthFromLength = Lemma(
    length * (listFromLength * x) === x
  ){
    println(s"thesis: ${thesis}")
    have(thesis) by Induction(x, nat){
      Case(zero) subproof {
        println(s"Case zero: ${thesis}")
        have(thesis) by Sorry
      }
      Case(succ, k) subproof {
        println(s"Case succ: ${thesis}")
        have(thesis) by Sorry
      }
    }
  }

}