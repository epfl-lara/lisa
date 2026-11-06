package lisa.hol

import lisa.SetTheoryLibrary
import lisa.hol.HOLHelperTheorems.{One, 𝔹}
import lisa.hol.VarsAndFunctions.*
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Types.TypingHelpers.*
import lisa.utils.K
import lisa.utils.fol.FOL.{*, given}
import org.scalatest.funsuite.AnyFunSuite

class InstantiationTypingSuite extends AnyFunSuite:
  private object Owner extends lisa.HOL:
    val theorem = Theorem(⊤):
      have(thesis) by Restate

  private val function = TypedVariable(K.Identifier("inst-function"), 𝔹 ->: 𝔹)
  private val argument = TypedVariable(K.Identifier("inst-argument"), 𝔹)

  private def instantiate(source: TypedVariable, replacements: Seq[(Variable[Ind], Expr[Ind])]): Option[Sequent] =
    import SetTheoryLibrary.*
    val proof = new BaseProof(Owner.theorem.asInstanceOf[THMFromProof])
    given proof.type = proof
    val premise = have(ExtendedHOLSteps._REFL(source))
    HOLSteps._INST(replacements, premise) match
      case valid: proof.ValidProofTactic =>
        val result = proof.newProofStep(valid)
        assert(K.SCProofChecker.checkSCProof(proof.toSCProof).isValid)
        assert(proof.justifications.forall(theorem => !theorem.withSorry))
        Some(result.bot)
      case _: proof.InvalidProofTactic => None

  test("accept alpha-equivalent variable and inferred composite types"):
    val bound = variable[Ind](K.Identifier("inst-type-binder"))
    val renamedType = Pi(𝔹)(λ(bound, 𝔹))
    val replacement = TypedVariable(K.Identifier("inst-replacement"), renamedType)
    assert(function.typ != renamedType && isSame(function.typ, renamedType))
    val variableResult = instantiate(function, Seq(function -> replacement)).get
    assert(isSameSequent(variableResult, replacement :: renamedType |- ((replacement =:= replacement) === One)))
    val source = TypedVariable(K.Identifier("inst-source"), renamedType)
    val composite = VarsAndFunctions.fun(argument, argument)
    val compositeResult = instantiate(source, Seq(source -> composite)).get
    assert(isSameSequent(compositeResult, () |- ((composite =:= composite) === One)))

  test("reject variable and composite replacements at genuinely different types"):
    assert(instantiate(function, Seq(function -> argument)).isEmpty)
    assert(instantiate(function, Seq(function -> (function * argument))).isEmpty)

  test("ignore the type of an absent substitution source"):
    val unused = TypedVariable(K.Identifier("inst-unused"), 𝔹 ->: 𝔹)
    val result = instantiate(argument, Seq(unused -> argument)).get
    assert(isSameSequent(result, argument :: 𝔹 |- ((argument =:= argument) === One)))
