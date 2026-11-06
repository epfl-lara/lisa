package lisa.hol

import lisa.SetTheoryLibrary
import lisa.hol.HOLHelperTheorems.𝔹
import lisa.hol.VarsAndFunctions.*
import lisa.maths.SetTheory.Base.Predef.∈
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.maths.SetTheory.Types.TypingHelpers.{fun as _, *}
import lisa.utils.K
import lisa.utils.fol.FOL.{_, given}
import lisa.utils.prooflib.*
import lisa.utils.prooflib.ProofHelpers.*
import org.scalatest.funsuite.AnyFunSuite

class AbstractionTypingSuite extends AnyFunSuite:
  private given Library = SetTheoryLibrary
  private def typing(term: Expr[Ind]): Thm =
    val result = Proof.withContext:
      Subproof:
        have(HOLSteps.HOLProofType(term))
    assert(result.isValid, result.errors.mkString("\n"))
    result.thm

  test("reuse an abstraction body while discharging only its binder"):
    HOLSteps.HOLProofType.resetCache()
    val x = TypedVariable(K.Identifier("reuse-abs-x"), 𝔹)
    val f = TypedVariable(K.Identifier("reuse-abs-f"), 𝔹 ->: 𝔹)
    val term = fun(x, f * x)
    val result = typing(term)
    assert(isSameSequent(result.statement, (f ∈ f.typ) |- (term ∈ (𝔹 ->: 𝔹))))
    assert(!result.kernel.usesSorry)
    assert(HOLSteps.HOLProofType.cacheSize >= 3)

  test("reuse nested and vacuous abstractions without leaking either binder"):
    HOLSteps.HOLProofType.resetCache()
    val x = TypedVariable(K.Identifier("reuse-abs-outer"), 𝔹)
    val y = TypedVariable(K.Identifier("reuse-abs-inner"), 𝔹)
    val term = fun(x, fun(y, x))
    assert(isSameSequent(typing(term).statement, () |- (term ∈ (𝔹 ->: (𝔹 ->: 𝔹)))))

  test("preserve tracked holes through abstraction reuse"):
    HOLSteps.HOLProofType.resetCache()
    val raw = Constant[Ind](K.Identifier("reuse-abs-hole"))
    SetTheoryLibrary.addSymbol(raw)
    val statement = () |- raw ∈ 𝔹
    val fact = Thm(statement, lisa.kernel.proof.Assume(using SetTheoryLibrary.theory)(statement.underlying).toOption.get)
    val value = TypedConstant(raw.id, 𝔹, fact)
    val x = TypedVariable(K.Identifier("reuse-abs-hole-binder"), 𝔹)
    val result = typing(fun(x, value)).kernel
    assert(result.assumptions == Set(statement.underlying))
    assert(!result.usesSorry)

  test("keep binder annotations separate for equal erased body terms"):
    HOLSteps.HOLProofType.resetCache()
    val a = TypeVariable(K.Identifier("reuse-abs-A"))
    val b = TypeVariable(K.Identifier("reuse-abs-B"))
    for domain <- Seq(a, b) do
      val x = TypedVariable(K.Identifier("reuse-abs-shared-id"), domain)
      val term = fun(x, x)
      assert(isSameSequent(typing(term).statement, () |- (term ∈ (domain ->: domain))))

  test("retain general inference for a dependent abstraction body type"):
    HOLSteps.HOLProofType.resetCache()
    val x = TypedVariable(K.Identifier("reuse-abs-dependent-x"), 𝔹)
    val dependent = Pi(𝔹)(λ(x, x))
    val f = TypedVariable(K.Identifier("reuse-abs-dependent-f"), dependent)
    val term = fun(x, f * x)
    assert(isSameSequent(typing(term).statement, (f ∈ dependent) |- (term ∈ dependent)))

  test("use the declared abstraction domain when binder metadata differs"):
    HOLSteps.HOLProofType.resetCache()
    val x = TypedVariable(K.Identifier("reuse-abs-domain-binder"), 𝔹)
    val domain = 𝔹 ->: 𝔹
    val term = abs(domain)(λ(x, x))
    assert(isSameSequent(typing(term).statement, () |- (term ∈ (domain ->: domain))))

  test("reject a body proof unrelated to the declared abstraction"):
    val x = variable[Ind](K.Identifier("reuse-abs-wrong-x"))
    val y = variable[Ind](K.Identifier("reuse-abs-wrong-y"))
    val z = variable[Ind](K.Identifier("reuse-abs-wrong-z"))
    val result = Proof.withContext:
      val unrelated = have(y ∈ 𝔹 |- y ∈ 𝔹) by BasicStep.Hypothesis
      Typecheck.abstractionProof(using SetTheoryLibrary)(x, 𝔹, z, 𝔹)(unrelated)
    assert(!result.isValid)

  test("discharge all alpha-equivalent copies of the binder typing"):
    val u = variable[Ind](K.Identifier("reuse-abs-alpha-u"))
    val v = variable[Ind](K.Identifier("reuse-abs-alpha-v"))
    val first = Pi(𝔹)(λ(u, 𝔹))
    val second = Pi(𝔹)(λ(v, 𝔹))
    val f = variable[Ind](K.Identifier("reuse-abs-alpha-f"))
    val result = Proof.withContext:
      val body = have((f ∈ first, f ∈ second) |- f ∈ first) by BasicStep.Hypothesis
      Typecheck.abstractionProof(using SetTheoryLibrary)(f, second, f, first)(body)
    assert(result.isValid, result.errors.mkString("\n"))
    assert(result.thm.statement.left.isEmpty)
    assert(!result.kernel.usesSorry)
