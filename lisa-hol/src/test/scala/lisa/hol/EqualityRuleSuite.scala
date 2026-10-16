package lisa.hol

import lisa.SetTheoryLibrary
import lisa.hol.HOLHelperTheorems.{One, 𝔹}
import lisa.hol.VarsAndFunctions.*
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Types.TypingHelpers.*
import lisa.utils.K
import lisa.utils.fol.FOL.{_, given}
import lisa.utils.prooflib.*
import org.scalatest.funsuite.AnyFunSuite

class EqualityRuleSuite extends AnyFunSuite:
  private given Library = SetTheoryLibrary
  private val x = TypedVariable(K.Identifier("rule-x"), 𝔹)
  private val y = TypedVariable(K.Identifier("rule-y"), 𝔹)
  private val f = TypedVariable(K.Identifier("rule-f"), 𝔹 ->: 𝔹)
  private val g = TypedVariable(K.Identifier("rule-g"), 𝔹 ->: 𝔹)
  private val context = Set(x :: 𝔹, y :: 𝔹, f :: f.typ, g :: g.typ)

  private def premise(conclusion: Expr[Prop]): Thm =
    val statement = context |- conclusion
    Thm(statement, lisa.kernel.proof.Assume(using SetTheoryLibrary.theory)(statement.underlying).toOption.get)

  private def checked(result: ProofJudgement, conclusion: Expr[Prop], premises: Thm*): Unit =
    assert(result.isValid, result.errors.map(_.message).mkString("\n"))
    assert(!result.kernel.usesSorry)
    assert(result.kernel.assumptions == premises.flatMap(_.kernel.assumptions).toSet)
    assert(isSameSet(result.thm.statement.right, Set(conclusion)))

  test("EQ_MP composes variable and composite propositions without new proof holes"):
    for (left, right) <- Seq((x, y), (f * x, g * y), (f * (g * x), g * (f * y))) do
      HOLSteps.HOLProofType.resetCache()
      val equality = premise((left =:= right) === One)
      val truth = premise(left === One)
      checked(Proof.withContext(ExtendedHOLSteps._EQ_MP(equality, truth)), right === One, equality, truth)

  test("EQ_MP rejects a proposition unrelated to the equality's left side"):
    val equality = premise((f * x =:= g * y) === One)
    val truth = premise(y === One)
    assert(!Proof.withContext(ExtendedHOLSteps._EQ_MP(equality, truth)).isValid)

  test("MK_COMB retains both equality dependencies for variable and composite arguments"):
    for (left, right) <- Seq((x, y), (f * x, g * y)) do
      HOLSteps.HOLProofType.resetCache()
      val functions = premise((f =:= g) === One)
      val arguments = premise((left =:= right) === One)
      checked(Proof.withContext(ExtendedHOLSteps._MK_COMB(functions, arguments)), (f * left =:= g * right) === One, functions, arguments)

  test("MK_COMB rejects an argument equality at the wrong type"):
    val functions = premise((f =:= g) === One)
    assert(!Proof.withContext(ExtendedHOLSteps._MK_COMB(functions, functions)).isValid)
