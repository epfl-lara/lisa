import lisa.maths.SetTheory.Types.ADTv2.*

object BuilderAPI extends lisa.Main {

  // ***********************
  // *   ADT Builder API   *
  // ***********************

  // println(s"Loading ADTv2Example / list2 ADT...")

  val list2 = API.defineAST(
    name = "list2",
    typeVars = Seq("A"),
    constructors = Seq(
      ("node2", Seq(("val2", arg(typ("A"))), ("left2", SelfRef), ("right2", SelfRef))),
      ("leaf2", Seq(("Val2", arg(typ("A"))))),
      // ("nameConflict", Seq(
      //   // ("n", arg(typ("A"))),
      //   // ("m", arg(typ("A"))),
      //   // ("h", arg(typ("A"))),
      //   // ("h_1", arg(typ("A"))),
      //   // ("x", SelfRef),
      //   ("otherVar", SelfRef)
      // )),
      ("nil2", Seq.empty),
      ("cons2", Seq(("head2", arg(typ("A"))), ("tail2", SelfRef)))
    )
  )

}
