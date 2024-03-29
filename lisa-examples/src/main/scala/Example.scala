

object ITP2024_Examples extends lisa.HOL {

  ///////////////////////////
  /////////// HOL ///////////
  ///////////////////////////

    val x = typedvar(𝔹)
    val y = typedvar(𝔹)
    val f = typedvar(𝔹 |=> 𝔹)
    val g = typedvar(𝔹 |=> (𝔹 |=> 𝔹))
    val h = typedvar((𝔹 |=> 𝔹) |=> 𝔹)

    

    output("------Expression 5------")
    val expr5 = λ(h,  λ(f, f*(x)) =:= h)
    output("expr5: " + expr5)
    output("expr5 type: " + computeType(expr5))

    val typecheckTest5 = TypingTheorem(expr5 :: (((𝔹 |=> 𝔹) |=> 𝔹) |=> 𝔹) )

    

  ////////////////////////////
  /////////// ADTs ///////////
  ////////////////////////////


  import lisa.maths.settheory.types.ADTTactic.*
  import ADTSyntax.*

  val typ = variable

  val define(list: ADT, constructors(nil, cons)) = () | (typ, list)
  val define(weird: ADT, constructors(c1, c2, c3)) = () | (Self, Self) | (BaseType(emptySet), Self, typ)

  val typecheckNil = TypingTheorem(nil(𝔹) :: list(𝔹))
  val typecheckCons = TypingTheorem(cons(𝔹) :: (𝔹 |=> (list(𝔹) |=> list(𝔹))))
}
