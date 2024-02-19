package lisa.hol

object HOLTest extends lisa.HOL{

    val x = variable(𝔹)
    val y = variable(𝔹)
    val z = variable(𝔹)

    val f = variable(𝔹 |=> 𝔹)
    val g = variable(𝔹 |=> (𝔹 |=> 𝔹))

    val expr = g*(x)*(f*(y))

    println(expr)
    val typecheckTest = TypingTheorem(expr :: 𝔹)


    val expr2 = g*(x)*(Abstraction(x, f*(x))*(y))
    println(expr2)
    println(computeType(expr2))
    val typecheckTest2 = TypingTheorem(expr2 :: 𝔹)



}
