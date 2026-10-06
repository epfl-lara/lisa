package lisa.hol

import lisa.hol.HOLHelperTheorems.*
import lisa.hol.VarsAndFunctions.*
import lisa.utils.K
import org.scalatest.funsuite.AnyFunSuite

class InstantiationTypeSuite extends AnyFunSuite:
  private object Proofs extends lisa.HOL:
    val bound = variable[Ind](K.Identifier("inst-renamed-binder"))
    val renamed = Pi(𝔹)(λ(bound, 𝔹))
    val source = TypedVariable(K.Identifier("inst-source"), 𝔹 ->: 𝔹)
    val replacement = TypedVariable(K.Identifier("inst-replacement"), renamed)
    val argument = TypedVariable(K.Identifier("inst-argument"), 𝔹)

    val equivalent = HOLTheorem(replacement =:= replacement):
      val premise = have(ExtendedHOLSteps._REFL(source))
      val result = have(HOLSteps._INST(Seq(source -> replacement), premise))
      have(thesis) by Weakening(result)

    val identity = HOLAbstraction(argument, argument)
    val compositeSource = TypedVariable(K.Identifier("inst-composite-source"), renamed)
    val composite = HOLTheorem(identity =:= identity):
      val premise = have(ExtendedHOLSteps._REFL(compositeSource))
      val result = have(HOLSteps._INST(Seq(compositeSource -> identity), premise))
      have(thesis) by Weakening(result)

    def rejectWrongType(): Unit =
      val proof = new BaseProof(equivalent.asInstanceOf[THMFromProof])
      given proof.type = proof
      val premise = have(ExtendedHOLSteps._REFL(source))
      assert(!HOLSteps._INST(Seq(source -> argument), premise).isValid)

  test("accept alpha-equivalent replacement types with checked SC proofs"):
    assert(Proofs.source.typ != Proofs.replacement.typ)
    assert(Proofs.isSame(Proofs.source.typ, Proofs.replacement.typ))
    for theorem <- Seq(Proofs.equivalent, Proofs.composite) do
      assert(theorem.kernelProof.exists(K.SCProofChecker.checkSCProof(_).isValid))
      assert(!theorem.innerJustification.withSorry)

  test("reject a genuinely different replacement type"):
    Proofs.rejectWrongType()
