package lisa.maths.settheory

object Equality extends lisa.Main:

  val x = variable[Term]
  val y = variable[Term]
  val z = variable[Term]

  val transitivity = Theorem((x === y, y === z) |- (x === z)):
    have((x === y, y === z) |- (x === y)) by Hypothesis
    thenHave(thesis) by InstSchema(y := z)

end Equality
