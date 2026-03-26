
import lisa.maths.SetTheory.Types.ADTv2.*

object InductiveFunction extends lisa.Main {

  // *******************************
  // * ADT Functions and Induction *
  // *******************************

  val x = variable[Ind]
  val n, m = variable[Ind]
  val N = variable[Ind]


  val bool = API.defineAST(
    name = "bool",
    typeVars = Seq.empty,
    constructors = Seq(
      ("tru", Seq.empty),
      ("fals", Seq.empty)
    )
  )
  val tru = bool.constructors(0)
  val fals = bool.constructors(1)


  show(bool.induction)

  val notFun = fun(bool, bool):
    Case(tru):
      fals
    Case(fals):
      tru

  show(notFun.intro)
  for (c <- notFun.elim.keys) show(notFun.elim(c))
  

  val negNegIsId = Theorem((x :: bool) |- notFun * (notFun * x) === x) {
    val notFals = have(notFun * fals === tru) by Restate.from((notFun.elim(fals)))
    val notTrue = have(notFun * tru === fals) by Restate.from((notFun.elim(tru)))
    have(thesis) by Induction(x, bool){
      Case(tru) subproof {
        have(notFun * (notFun * tru) === tru) by Congruence.from(notTrue, notFals)
      }
      Case(fals) subproof {
        have(notFun * (notFun * fals) === fals) by Congruence.from(notTrue, notFals)
      }
    }
  }
  
  val nat = API.defineAST(
    name = "nat",
    typeVars = Seq.empty,
    constructors = Seq(
      ("zero", Seq.empty),
      ("succ", Seq(("N", SelfRef)))
    )
  )
  val zero = nat.constructors(0)
  val succ = nat.constructors(1)
  

  val predFun = fun(nat, nat):
    Case(zero):
      zero
    Case(succ, n):
      n

  show(succ.intro)
  show(succ.introApp)
  for (c <- predFun.elim.keys) show(predFun.elim(c))

  val predSucc = Lemma((n :: nat) |- predFun * (succ * n) === n) {
    have(thesis) by Induction(n, nat){
      Case(zero) subproof {
        have(zero :: nat) by Restate.from(zero.intro)
        have(predFun * (succ * zero) === zero) by 
          Tautology.from(lastStep, predFun.elim(succ) of (n := zero))
      }
      Case(succ, m) subproof {
        have( m :: nat |- predFun * (succ * (succ * m)) === succ * m) by
          Tautology.from(
            succ.introApp of (N := m), 
            predFun.elim(succ) of (n := succ * m)
          )
      }
    }
  }


}