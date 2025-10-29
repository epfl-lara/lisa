package lisa.utils.prooflib

import lisa.utils.KernelHelpers.{_, given}
import lisa.utils.fol.{FOL => F}
import lisa.test.ProofTacticTestLib
import lisa.utils.prooflib.SimpleDeducedSteps.InstantiateForall

class InstantiationTest extends ProofTacticTestLib {

  val x = variable[Ind]
  val y = variable[Ind]
  val z = variable[Ind]
  val P = variable[Ind >>: Prop]

  val correctPairs = List(
    (() |- ∀(x, P(x)), () |- P(y), (∀(x, P(x)), Seq(y))),
    (() |- ∀(x, P(x)), () |- P(x), (∀(x, P(x)), Seq(x))),
    (P(y) |- ∀(x, P(x)), P(y) |- P(y), (∀(x, P(x)), Seq(y))),
    (P(x) |- ∀(x, P(x)), P(x) |- P(x), (∀(x, P(x)), Seq(x))),
    // with nested quantifiers
    (() |- ∀(x, ∀(y, P(x))), () |- ∀(y, P(z)), (∀(x, ∀(y, P(x))), Seq(z))),
    (() |- ∀(x, ∀(y, P(x))), () |- P(y), (∀(x, ∀(y, P(x))), Seq(y, x)))
  )

  val incorrectPairs = List(
    // wrong direction
    (() |- P(y), () |- ∀(x, P(x)), (∀(x, P(x)), Seq(y))),
    // not enough quantifiers
    (() |- ∀(x, ∀(y, P(x))), () |- P(x), (∀(x, ∀(y, P(x))), Seq(x))),
    // too many quantifiers
    (() |- ∀(x, P(x)), () |- ∀(y, P(y)), (∀(x, P(x)), Seq(y))),
    // incorrect instantiation term count
    (() |- ∀(x, P(x)), () |- P(y), (∀(x, P(x)), Seq(x, y))),
    // incorrect instantiation term
    (() |- ∀(x, P(x)), () |- P(x), (∀(x, P(x)), Seq(y))),
    // capturing
    (() |- ∀(x, ∀(y, P(x))), () |- ∀(y, P(y)), (∀(x, ∀(y, P(x))), Seq(y))),
  )

  test("InstantiateForall explicit") {
    testTacticCases(correctPairs, incorrectPairs) {
      case (premiseSeq, conclusionSeq, (phi, terms)) =>
        InstantiateForall(phi, terms*)(introduceSequent(premiseSeq))(conclusionSeq)
    }
  }

  test("InstantiateForall implicit") {
    // without the explicit using somehow overload resolution fails??
    val lib = summon[Library]
    val proof = summon[lib.Proof]
    testTacticCases(using proof)(correctPairs, incorrectPairs.take(1)) {
      case (premiseSeq, conclusionSeq, (_, t)) =>
        val prem = introduceSequent(using proof)(premiseSeq)
        InstantiateForall(using lib, proof)(prem: proof.Fact)(conclusionSeq)
    }
  }

}
