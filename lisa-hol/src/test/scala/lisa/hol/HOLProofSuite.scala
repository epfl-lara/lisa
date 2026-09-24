package lisa.hol

import lisa.SetTheoryLibrary
import org.scalatest.funsuite.AnyFunSuite

/** Check the proof registry as well as module initialization. */
class HOLProofSuite extends AnyFunSuite:
  private def check(name: String)(initialize: => lisa.Main): Unit =
    test(name):
      initialize
      val errors = SetTheoryLibrary.theorems.all
        .filter(_.fullName.value.startsWith(name + "."))
        .flatMap(theorem => theorem.errors.map(error => s"${theorem.fullName.value}:${error.line.value}: ${error.message}"))
        .toSeq
      assert(errors.isEmpty, errors.mkString("\n"))

  check("lisa.hol.ExtendedHOLSteps")(lisa.hol.ExtendedHOLSteps)
  check("lisa.hol.HOLBasics")(lisa.hol.HOLBasics)
  check("lisa.hol.HOLExtStepsTests")(lisa.hol.HOLExtStepsTests)
  check("lisa.hol.HOLHelperTheorems")(lisa.hol.HOLHelperTheorems)
  check("lisa.hol.HOLSteps")(lisa.hol.HOLSteps)
  check("lisa.hol.Import")(lisa.hol.Import)
  check("lisa.hol.basics.Connectives")(lisa.hol.basics.Connectives)
  check("lisa.hol.basics.Exists")(lisa.hol.basics.Exists)
  check("lisa.hol.basics.False")(lisa.hol.basics.False)
  check("lisa.hol.basics.Forall")(lisa.hol.basics.Forall)
  check("lisa.hol.basics.Inductive")(lisa.hol.basics.Inductive)
  check("lisa.hol.basics.Select")(lisa.hol.basics.Select)
  check("lisa.hol.basics.Truth")(lisa.hol.basics.Truth)
  check("lisa.hol.basics.TypeDefs")(lisa.hol.basics.TypeDefs)

  test("monomorphic HOL constants have checked definition proofs"):
    assert(!basics.Connectives.hand.holDefinition.kernel.usesSorry)
    assert(!basics.Connectives.himp.holDefinition.kernel.usesSorry)
    assert(!basics.Connectives.hnot.holDefinition.kernel.usesSorry)

  test("existence and type-definition proofs do not inherit Sorry"):
    for theorem <- Seq(basics.Exists.hexistsCorrect, basics.TypeDefs.typeNonEmpty, basics.TypeDefs.absTyping, basics.TypeDefs.repThm) do
      assert(!theorem.kernel.usesSorry, theorem.fullName.value)
