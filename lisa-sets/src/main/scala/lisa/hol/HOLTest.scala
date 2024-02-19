package lisa.hol

object HOLTest extends lisa.HOL{

    val x = typedvar(𝔹)
    val y = typedvar(𝔹)
    val z = typedvar(𝔹)

    val f = typedvar(𝔹 |=> 𝔹)
    val g = typedvar(𝔹 |=> (𝔹 |=> 𝔹))

    val expr = g*(x)*(f*(y))

    println(expr)
    val typecheckTest = TypingTheorem(expr :: 𝔹)


    val expr2 = g*(x)*(Abstraction(x, f*(x))*(y))
    println("expr2: " + expr2)
    println("expr2 type: " + computeType(expr2))
    val typecheckTest2 = TypingTheorem(expr2 :: 𝔹)

    println("------Expression 3------")
    val expr3 = (g*(x)).=:=(𝔹 |=> 𝔹)(Abstraction(x, f*(x)))

    println("expr3: " + expr3)
    println("expr3 type: " + computeType(expr3))
    val typecheckTest3 = TypingTheorem(expr3 :: 𝔹 )



}
