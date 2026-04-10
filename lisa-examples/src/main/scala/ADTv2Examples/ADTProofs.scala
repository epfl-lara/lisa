
import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.utils.fol.FOL

object ADTProofs extends lisa.Main {

  val union = API.defineAST(
    name = "union",
    typeVars = Seq("A","B"),
    constructors = Seq(
      ("inl", Seq(("x", "A"))),
      ("inr", Seq(("y", "B")))
    )
  )
  val inl = union.constructors(0)
  val inr = union.constructors(1)

  val bool = API.defineAST(
    name = "bool",
    typeVars = Seq.empty,
    constructors = Seq(
      ("true", Seq.empty),
      ("false", Seq.empty)
    )
  )
  val true_ = bool.constructors(0)
  val false_ = bool.constructors(1)


  val unit = API.defineAST(
    name = "unit",
    typeVars = Seq.empty,
    constructors = Seq(
      ("star", Seq.empty)
    )
  )
  val star = unit.constructors(0)


  println(s"bool: ${bool}")
  println(s"bool(): ${bool()}")
  println(s"union: ${union}")
  println(s"union() : ${union()}")
  println(s"union of bool and unit: ${union(bool, unit)}")
  println(s"inl: ${inl}")
  println(s"inl of bool and unit: ${inl(bool, unit)}")

  show(union.induction)
  show(bool.induction)
  show(unit.induction)
  show(union.elim)
  show(bool.elim)
  show(unit.elim)

}