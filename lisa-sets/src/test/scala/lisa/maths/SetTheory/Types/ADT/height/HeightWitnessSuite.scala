package lisa.maths.SetTheory.Types.ADT.height

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.ProofChecks._
import lisa.maths.SetTheory.Types.ADT.encoding.SyntacticADT
import lisa.maths.SetTheory.Types.ADT.encoding.SyntacticConstructor
import lisa.maths.SetTheory.Types.ADT.syntax.AST.SelfRef
import lisa.maths.SetTheory.Types.ADT.syntax.AST.TypeArg
import lisa.utils.prooflib.OutputManager
import lisa.utils.prooflib.StringOutputManager
import org.scalatest.funsuite.AnyFunSuite

/**
 * Executes the height specification and retained existence and uniqueness theorems.
 */
class HeightWitnessSuite extends AnyFunSuite:
  private given OutputManager = new StringOutputManager

  private def checkHeightProofs(declaration: SyntacticADT): Unit =
    assert(!declaration.heightValid.hasErrorsOrSorry)
    assert(!declaration.heightExists.hasErrorsOrSorry)
    assert(!declaration.heightUniqueness.hasErrorsOrSorry)
    assert(!declaration.heightExistsOne.hasErrorsOrSorry)

  test("retain height existence and uniqueness for an empty datatype"):
    checkHeightProofs(new SyntacticADT("heightWitnessEmpty", Seq.empty, Seq.empty))

  test("retain height existence and uniqueness with payload and recursive fields"):
    val A, payload1, tail1, payload2, tail2 = variable[Ind]
    val name = "heightWitnessList"
    val empty = new SyntacticConstructor(Seq.empty, Seq.empty, Seq.empty, 0, name)
    val cons = new SyntacticConstructor(
      Seq(TypeArg("A"), SelfRef),
      Seq(payload1, tail1),
      Seq(payload2, tail2),
      1,
      name
    )
    checkHeightProofs(new SyntacticADT(name, Seq(empty, cons), Seq(A)))
