

object HOLTypechecking extends lisa.HOL{

    val x = typedvar(𝔹)
    val y = typedvar(𝔹)
    val f = typedvar(𝔹 |=> 𝔹)
    val g = typedvar(𝔹 |=> (𝔹 |=> 𝔹))
    val h = typedvar((𝔹 |=> 𝔹) |=> 𝔹)

    output("------Expression 1------")
    val expr1 = g*(x)*(f*(y))
    output("expr1: " + expr1)
    output("expr1 type: " + computeType(expr1))

    val typecheckTest = TypingTheorem(expr1 :: 𝔹)


    output("------Expression 2------")
    val expr2 = g*(x)*(λ(x, f*(x))*(y))
    output("expr2: " + expr2)
    output("expr2 type: " + computeType(expr2))

    val typecheckTest2 = TypingTheorem(expr2 :: 𝔹)


    output("------Expression 3------")
    val expr3 = x =:= y
    output("expr3: " + expr3)
    output("expr3 type: " + computeType(expr3))

    val typecheckTest3 = TypingTheorem(expr3 :: 𝔹 )


    output("------Expression 4------")
    val expr4 = (g*(x)) =:= λ(x, f*(x))
    output("expr4: " + expr4)
    output("expr4 type: " + computeType(expr4))

    val typecheckTest4 = TypingTheorem(expr4 :: 𝔹 )

    output("------Expression 5------")
    val expr5 = λ(h,  λ(f, f*(x)) =:= h)
    output("expr5: " + expr5)
    output("expr5 type: " + computeType(expr5))

    val typecheckTest5 = TypingTheorem(expr5 :: (((𝔹 |=> 𝔹) |=> 𝔹) |=> 𝔹) )

}


object ADT extends lisa.HOL {
  import lisa.maths.settheory.types.ADTTactic.*
  import ADTSyntax.*

  // Type variable
  val A = variable

  // Defining polymorphic lists with two constructors: nil taking no arguments, representing the empty list,
  // and cons taking an element and a list, representing the prepending of an element to a list.
  val define(list: ADT, constructors(nil, cons)) = () | (A, list)

  val typecheckNil = TypingTheorem(nil(𝔹) :: list(𝔹))
  val typecheckCons = TypingTheorem(cons(𝔹) :: (𝔹 |=> (list(𝔹) |=> list(𝔹))))

}

object HOLImport extends lisa.HOL{
  lisa.hol.HOLImport.importHOLLight
}