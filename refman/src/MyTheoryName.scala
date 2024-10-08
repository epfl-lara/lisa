//> using scala 3.5.1
//> using jar "../../../lisa/target/scala-3.5.1/lisa-assembly-0.7.jar"
object MyTheoryName extends lisa.Main:
  val x = variable
  val y = variable
  val f = function[1]
  val P = predicate[1]

  val fixedPointDoubleApplication = Theorem( 
    ∀(x, P(x) ==> P(f(x))) |- P(x) ==> P(f(f(x)))
  ) {
    assume(∀(x, P(x) ==> P(f(x))))
    val step1 = have(P(x) ==> P(f(x))) by InstantiateForall
    val step2 = have(P(f(x)) ==> P(f(f(x)))) by InstantiateForall
    have(thesis) by Tautology.from(step1, step2)
  } 

  val emptySetIsASubset = Theorem(
    ∅ ⊆ x
  ) {
    have((y ∈ ∅) ==> (y ∈ x)) by Tautology.from(
                            emptySetAxiom of (x := y))
    val rhs = thenHave (∀(y, (y ∈ ∅) ==> (y ∈ x))) by RightForall
    have(thesis) by Tautology.from(
                            subsetAxiom of (x := ∅, y := x), rhs)
  }

  @main def show = println(emptySetAxiom)

