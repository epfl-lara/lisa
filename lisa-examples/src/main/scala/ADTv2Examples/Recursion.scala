import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Functions.BasicTheorems.{appTyping, funcBetweenEqInFuncSpace}
import lisa.utils.fol.FOL

object Recursion extends lisa.Main {

  // *******************************
  // * ADT Functions and Induction *
  // *******************************

  def show(m : Map[?, THM]) : Unit = 
    m.foreach{ case (k, stmt) => show(stmt) }

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

 
  val length = recFun(list, nat) { self =>
    Case(nil):
      zero
    Case(cons, hd, tl):
      succ * (self * tl)
  }

  val double = recFun(nat, nat) { self =>
    Case(zero):
      zero
    Case(succ, k):
      succ * (succ * (self * k))
  }

  section("Recursive functions")
  show(double.intro)
  show(double.elim)
  show(length.intro)
  show(length.elim)

  section("Internals")
  show(length.debug_uniqueness)
  // show(length.debug_existence)
  show(length.debug_classDefinitionFact)

}
