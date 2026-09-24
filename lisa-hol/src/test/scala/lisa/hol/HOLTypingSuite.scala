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

class HOLTypingSuite extends AnyFunSuite:
  private given Library = SetTheoryLibrary

  private def checked(result: ProofJudgement): Thm =
    assert(result.isValid, result.errors.map(_.message).mkString("\n"))
    val theorem = result.justification.get
    assert(!theorem.kernel.usesSorry)
    theorem

  private val function = TypedVariable(K.Identifier("hol-typing-function"), 𝔹 ->: 𝔹)
  private val argument = TypedVariable(K.Identifier("hol-typing-argument"), 𝔹)

  for composite <- Seq(false, true) do
    test(s"application congruence preserves typing with composite argument = $composite"):
      HOLSteps.HOLProofType.resetCache()
      val term = if composite then function * argument else argument
      val result = Proof.withContext:
        val functionEquality = checked(ExtendedHOLSteps._REFL(function))
        val argumentEquality = checked(ExtendedHOLSteps._REFL(term))
        val congruence = checked(ExtendedHOLSteps._MK_COMB(functionEquality, argumentEquality))
        assert((functionEquality.kernel.axioms ++ argumentEquality.kernel.axioms).subsetOf(congruence.kernel.axioms))
        ProofJudgement(congruence)

      val theorem = checked(result)
      assert(isSameSequent(theorem.statement, Set(function :: (𝔹 ->: 𝔹), argument :: 𝔹) |- ((function * term =:= function * term) === One)))

  test("term instantiation accepts alpha-equivalent function types"):
    val bound = variable[Ind](K.Identifier("hol-inst-type-binder"))
    val renamedType = Pi(𝔹)(λ(bound, 𝔹))
    val replacement = TypedVariable(K.Identifier("hol-inst-replacement"), renamedType)
    assert(function.typ != replacement.typ)
    assert(isSame(function.typ, replacement.typ))

    val result = Proof.withContext:
      val premise = checked(ExtendedHOLSteps._REFL(function))
      HOLSteps._INST(Seq(function -> replacement), premise)
    val theorem = checked(result)
    assert(isSameSequent(theorem.statement, replacement :: renamedType |- ((replacement =:= replacement) === One)))

  test("term instantiation rejects genuinely different types"):
    val result = Proof.withContext:
      val premise = checked(ExtendedHOLSteps._REFL(function))
      HOLSteps._INST(Seq(function -> argument), premise)
    assert(!result.isValid)

  test("equivalent types still discharge a composite replacement's typing"):
    val bound = variable[Ind](K.Identifier("hol-inst-composite-binder"))
    val renamedType = Pi(𝔹)(λ(bound, 𝔹))
    val source = TypedVariable(K.Identifier("hol-inst-composite-source"), renamedType)
    val replacement = HOLAbstraction(argument, argument)
    assert(source.typ != computeType(replacement))
    assert(isSame(source.typ, computeType(replacement)))
    val result = Proof.withContext:
      val premise = checked(ExtendedHOLSteps._REFL(source))
      HOLSteps._INST(Seq(source -> replacement), premise)
    val theorem = checked(result)
    assert(isSameSequent(theorem.statement, () |- ((replacement =:= replacement) === One)))
