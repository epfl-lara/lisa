package lisa.hol

object HOLTest extends lisa.HOL{

    val x = variable(𝔹)
    val y = variable(𝔹)
    val z = variable(𝔹)

    val f = variable(𝔹 |=> 𝔹)
    val g = variable(𝔹 |=> (𝔹 |=> 𝔹))

    val expr = g.@@(x).@@(f.@@(y))
    println(expr)
    val typecheckTest = TypingTheorem(expr :: 𝔹)
    println(typecheckTest.statement.toString)
    println("hello !" + typecheckTest.statement)
    println(typecheckTest.statement)

}
