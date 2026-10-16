package lisa.hol

import lisa.SetTheoryLibrary
import lisa.SetTheoryLibrary.∈
import lisa.hol.VarsAndFunctions.*
import lisa.maths.SetTheory.Types.TypingHelpers.TypeAssign
import lisa.utils.K
import lisa.utils.fol.FOL.{_, given}
import lisa.utils.prooflib.*
import org.scalatest.funsuite.AnyFunSuite

class CleanSuite extends AnyFunSuite:
  private given Library = SetTheoryLibrary
  private val x = variable[Ind](K.Identifier("cleanup-x"))
  private val y = variable[Ind](K.Identifier("cleanup-y"))
  private val a = TypeVariable(K.Identifier("cleanup-A"))
  private val b = TypeVariable(K.Identifier("cleanup-B"))

  private def checked(result: ProofJudgement): Thm =
    assert(result.isValid, result.errors.map(_.message).mkString("\n"))
    assert(!result.thm.kernel.usesSorry)
    result.thm

  test("remove unused typings and retain required type non-emptiness"):
    val premise = checked(BasicStep.RightRefl(Sequent(Set(x ∈ a, y ∈ b), Set(a === a))))
    val result = checked(Proof.withContext(HOLSteps.Clean.allVariables(premise)))
    assert(result.statement.left.exists(isSame(_, nonEmpty(a))))
    assert(result.statement.left.exists(isSame(_, nonEmpty(b))))
    assert(!result.statement.left.contains(x ∈ a))
    assert(!result.statement.left.contains(y ∈ b))
    val cleaned = checked(Proof.withContext(HOLSteps.Clean.allTypeVars(result)))
    assert(cleaned.statement.left.exists(isSame(_, nonEmpty(a))))
    assert(!cleaned.statement.left.exists(isSame(_, nonEmpty(b))))

  test("retain variables used in the conclusion or another typing assumption"):
    val statement = Sequent(Set(x ∈ a, y ∈ x), Set(y === y))
    val premise = checked(BasicStep.RightRefl(statement))
    assert(checked(Proof.withContext(HOLSteps.Clean.allVariables(premise))).statement == statement)
    assert(!Proof.withContext(HOLSteps.Clean.variable(TypeAssign(y, x))(premise)).isValid)

  test("reject mismatched typed-variable annotations"):
    val typed = TypedVariable(x.id, a)
    val premise = checked(BasicStep.RightRefl(Sequent(Set(typed ∈ b), Set(a === a))))
    intercept[LisaHOLException]:
      Proof.withContext(HOLSteps.Clean.variable(TypeAssign(typed, b))(premise))

  test("preserve type annotations that are not syntactically free variables"):
    val typed = TypedVariable(x.id, a)
    val statement = Sequent(Set.empty, Set(typed === typed))
    assert(statement.hasFree(typed))
    assert(!statement.hasFree(a))
    val replaced = statement.substitute(a := b)
    assert(replaced.hasFree(typed))
    assert(replaced.freeVars.collect { case v: TypedVariable => v.typ } == Set(b))
