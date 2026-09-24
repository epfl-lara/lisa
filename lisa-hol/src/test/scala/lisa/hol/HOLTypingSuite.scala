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
