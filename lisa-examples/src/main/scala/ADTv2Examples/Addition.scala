
import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Types.ADTv2.basics.Nat.*
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Types.TypingHelpers
import lisa.utils.fol.FOL

object Addition extends lisa.Main {


  def show(m : Map[?, THM]) : Unit = 
    m.foreach{ case (k, stmt) => show(stmt) }

  val n, k, m = variable[Ind]

  val idNat = recFun(nat, nat) { self =>
    Case(zero):
      zero
    Case(succ, n):
      succ * (self * n)
  }
  val addOne = recFun(nat, nat) { self =>
    Case(zero):
      succ * zero
    Case(succ, n):
      succ * (self * n)
  }

  /* 
  0 + m = m
  Sn + m = n + Sm
  
  0: id_N
  Sn: m -> addOne (self * n * m)
  */

  val T = nat.term ->: nat.term

  val add = recFun(nat, T) { self =>
    Case(zero):
      idNat
    Case(succ, n):
      TypingHelpers.fun(
        m :: nat.term,
        addOne * ((self * n) * m)
      )
  }

  show(idNat.intro)
  show(add.intro)

  show(idNat.elim)
  show(addOne.elim)
  show(add.elim)

}
