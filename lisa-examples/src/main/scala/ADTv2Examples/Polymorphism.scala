import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Types.ADTv2.basics.Box.*
import lisa.maths.SetTheory.Types.ADTv2.basics.Unit.*
import lisa.maths.SetTheory.Types.ADTv2.basics.List.*
import lisa.maths.SetTheory.Types.ADTv2.basics.Nat.*
import lisa.maths.SetTheory.Types.ADTv2.basics.Union.*
import lisa.maths.SetTheory.Types.ADTv2.basics.Option.*
import lisa.maths.SetTheory.Functions.Pi.{->:}

object Polymorphism extends lisa.Main {

  val boxUnit = box(unit)
  val packUnit = pack(unit)

  val listUnit = list(unit)

  section("ADT theorems")
  show(box.induction)
  show(boxUnit.induction)
  show(box.elim)
  show(boxUnit.elim)

  // section("Constructor injectivity")
  // for (c1 <- list.constructors; c2 <- list.constructors)
  //   if (c1 != c2)
  //     show(list.injectivity(c1, c2))
  //     show(listUnit.injectivity(c1, c2))

  section("Constructor theorems")
  show(pack.intro)
  show(packUnit.intro)
  show(pack.introApp)
  show(packUnit.introApp)
  show(pack.injectivity)
  show(packUnit.injectivity)

  section("Recursion theorems")

  val hd, tl = variable[Ind]

  val length = recFun(list, nat) { self =>
    Case(nil):
      zero
    Case(cons, hd, tl):
      succ * (self * tl)
  }
  val unit_list_length = length(unit)

  show(length.intro)
  show(unit_list_length.intro)
  show(length.introApp)
  show(unit_list_length.introApp)

  // section("Recursion elimination theorems")
  // for (c <- length.elimination.keys) show(length.elimination(c))
  // for (c <- unit_list_length.elimination.keys) show(unit_list_length.elimination(c))

  section("Complex instanciations")

  val A, T = variable[Ind]

  show(box(box(unit)).induction)
  show(union.substitute(A := unit).induction)
  // show(option(box).induction)

}
