package lisa.maths.settheory

object Equality extends lisa.Main:

  val x = variable[Ind]
  val y = variable[Ind]
  val z = variable[Ind]

  val transitivity = Theorem((x === y, y === z) |- (x === z)):
    have((x === y, y === z) |- (x === y)) by Hypothesis
    thenHave(thesis) by RightSubstEq.withParameters(Seq(y -> z), Seq(y) -> (x === y))

end Equality
