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
    println(expr2)
    println(computeType(expr2))
    val typecheckTest2 = TypingTheorem(expr2 :: 𝔹)



}
